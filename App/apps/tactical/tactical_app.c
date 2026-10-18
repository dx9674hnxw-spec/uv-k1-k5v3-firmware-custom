/* Copyright 2026 Armel F4HWN
 * SPDX-License-Identifier: Apache-2.0
 *
 * Tactical — modal overlay transceiver with a "tactical console" UI on the
 * channel that was current at launch. Voice TX uses the resident TX path
 * (tx_set_params keys the carrier with the channel CTCSS/DCS and the
 * microphone open); RX follows the squelch like ToneCall (REG_0C bit 1).
 *
 * On top: a mission chrono (SysTick), an APCO ten-code status, a call
 * journal, a roger beep (sent on air before unkeying), a TX time limit, a
 * night (inverted) display and US siren tones (wail, yelp, phaser). The
 * siren only plays on the speaker; it is never keyed.
 *
 * Keys: PTT transmit · 1-7 status · MENU roger beep · F ops/journal ·
 *       STAR night · 0 siren (cycles, PTT or EXIT stops) · EXIT quit.
 */
#include <stdint.h>
#include <stdbool.h>
#include "../app_api.h"

#define LOOP_MS        10u
#define CFG_MAGIC      0x7Cu
#define LOG_LEN        6u
#define STATUS_N       7u
#define ROGER_N        5u
#define SIREN_N        4u
#define TX_LIMIT_S     120u      /* own TX time-out: the resident TOT is not exposed */

#define REG_0C         0x0Cu     /* bit 1: squelch open                    */
#define REG_30         0x30u
#define REG_70         0x70u
#define REG_71         0x71u     /* tone 1 frequency                       */
#define REG_30_TX_LINK 0xC3FAu   /* BK4819_EnableTXLink                    */
#define REG_30_IDLE    0xC1FEu   /* as BK4819_PlaySingleTone leaves it     */
#define REG_70_TONE1   0xC200u   /* TONE1 on, tuning gain 66               */
#define REG_70_SIREN   0xE000u   /* TONE1 on, tuning gain 96 (loud beep)   */

enum { ST_IDLE, ST_RX, ST_TX, ST_SIREN };
enum { ROGER_OFF, ROGER_BIP, ROGER_BIPBOP, ROGER_QUINDAR, ROGER_MDC };

typedef struct {
    uint16_t at;     /* mission second the call started */
    uint16_t dur;    /* seconds                         */
    uint8_t  tx;     /* own transmission                */
    uint8_t  s;      /* peak S level (RX only)          */
} log_t;

/* APCO ten-codes (the usual US meaning; some agencies differ). Each line is
 * at most 17 small-font glyphs, so it stays inside the 128 px line. */
static const char *const STATUS[STATUS_N] = {
    "10-8 EN SERVICE", "10-76 EN ROUTE", "10-97 SUR PLACE", "10-6 OCCUPE",
    "10-7 HORS SERVICE", "10-19 RETOUR BASE", "CODE 4 RAS"
};
static const char *const ROGER[ROGER_N] = {
    "ROGER OFF", "ROGER BIP", "ROGER BIP-BOP", "ROGER QUINDAR", "ROGER MDC"
};
static const char *const SIREN[SIREN_N] = { "", "SIRENE WAIL", "SIRENE YELP", "SIRENE PHASER" };

static const app_api_t *A;
static log_t journal[LOG_LEN];
static log_t *live;               /* entry being timed, NULL when idle */
static uint32_t t0;
static uint16_t mission;
static uint8_t logCount, logHead, state, status, roger, sNow, siren;
static uint32_t sirenT0;
static bool running, night, journalView, txTimedOut;
static uint8_t txDenied;          /* tx_state() code: 1 band/lock/mode, 2 battery low, 3 voltage high */
static char text[28];             /* longest: a 20-glyph journal row + NUL */

/* The Cortex-M0+ has no divider: route the compiler's helpers to the resident
 * ones (API level 2) instead of linking libgcc's. */
uint64_t __aeabi_uidivmod(uint32_t n, uint32_t d) { return A->uidivmod(n, d); }
uint32_t __aeabi_uidiv(uint32_t n, uint32_t d) { return (uint32_t)A->uidivmod(n, d); }

static char *put(char *o, const char *s) { while (*s) *o++ = *s++; return o; }
static char *put2(char *o, uint8_t v) { *o++ = (char)('0' + v / 10u); *o++ = (char)('0' + v % 10u); return o; }
static char *putTime(char *o, uint16_t s) { o = put2(o, (uint8_t)((s / 60u) % 100u)); *o++ = ':'; return put2(o, (uint8_t)(s % 60u)); }
static char *putFreq(char *o, uint32_t f)
{
    char t[10]; int8_t n = 0;
    uint32_t mhz = f / 100000u;
    do { t[n++] = (char)('0' + mhz % 10u); mhz /= 10u; } while (mhz);
    while (n--) *o++ = t[n];
    *o++ = '.'; f %= 100000u;
    for (uint32_t p = 10000u; p; p /= 10u) *o++ = (char)('0' + (f / p) % 10u);
    *o = '\0';
    return o;
}

static uint8_t sLevel(int16_t dbm)
{
    if (dbm >= -93) return 9;
    if (dbm < -141) return 0;
    return (uint8_t)((uint16_t)(dbm + 147) / 6u);
}

static void invertLine(uint8_t line) { for (uint8_t x = 0; x < 128u; x++) A->fb[line][x] ^= 0xFFu; }

/* ---- call journal ---- */
static void logOpen(bool tx)
{
    live = &journal[logHead];
    logHead = (uint8_t)((logHead + 1u) % LOG_LEN);
    if (logCount < LOG_LEN) logCount++;
    live->at = mission; live->dur = 0; live->tx = tx; live->s = 0;
}

static const log_t *logAt(uint8_t age) { return &journal[(logHead + LOG_LEN - 1u - age) % LOG_LEN]; }

/* ---- radio ---- */
static void sirenStop(void);

static void rxListen(bool open)
{
    A->audio_path(open);
    A->led(open);
}

static void rxResume(void)
{
    A->set_af(APP_AF_FM);   /* AM channels also use the FM AF output (radio.c) */
    rxListen(false);
}

static void txStart(void)
{
    sirenStop();
    txDenied = A->tx_state();
    if (txDenied) return;
    rxListen(false);
    A->tx_set_params();     /* carrier + PA + channel CTCSS/DCS, microphone open */
    state = ST_TX;
    txTimedOut = false;
    logOpen(true);
}

/* BK4819 REG_71 value for a tone in Hz (driver scale_freq, rounded). */
static uint16_t toneReg(uint16_t hz) { return (uint16_t)(((uint32_t)hz * 1353245u + (1u << 16)) >> 17); }

/* Roger beep, still keyed: ToneCall's tone path, but the tone stays unmuted
 * while REG_71 is rewritten, so multi-tone patterns have no gaps or clicks. */
static void tone(uint16_t hz, uint16_t ms) { A->bk_write(REG_71, toneReg(hz)); A->delay_ms(ms); }

static void rogerBeep(void)
{
    A->tx_mute(true);
    A->set_af(APP_AF_MUTE);
    A->bk_write(REG_70, REG_70_TONE1);
    A->bk_write(REG_30, REG_30_TX_LINK);
    A->bk_write(REG_71, toneReg(1000));
    A->tx_mute(false);
    switch (roger) {
        case ROGER_BIP:     tone(1000, 150); break;
        case ROGER_BIPBOP:  tone(1250, 90); tone(850, 110); break;
        case ROGER_QUINDAR: tone(2475, 250); break;
        default:            /* MDC-1200-like burst: random 1200/1800 Hz at ~1 kbit/s */
            for (uint8_t i = 0; i < 180u; i++) tone((A->rand32() & 1u) ? 1800u : 1200u, 1);
            break;
    }
    A->tx_mute(true);
    A->bk_write(REG_70, 0u);
    A->bk_write(REG_30, REG_30_IDLE);
}

static void txStop(void)
{
    if (state != ST_TX) return;
    if (roger) rogerBeep();
    A->tx_mute(true);
    A->tx_end();            /* PA off + RX registers restored */
    state = ST_IDLE;
    live = (void *)0;
    rxResume();
}

/* US siren on the speaker only: the receiver is parked while it sounds. */
static void sirenStop(void)
{
    if (state != ST_SIREN) return;
    A->tx_mute(true);
    A->audio_path(false);
    A->tones_off_rx();
    state = ST_IDLE;
    siren = 0;
    rxResume();
}

static void sirenNext(void)
{
    const uint8_t next = (uint8_t)((siren + 1u) % SIREN_N);
    sirenStop();
    if (!next) return;
    siren = next;
    state = ST_SIREN;
    sirenT0 = A->ticks_ms();
    A->prepare_tone();                 /* AF beep path, TX DSP, tone muted */
    A->bk_write(REG_70, REG_70_SIREN);
    A->bk_write(REG_71, toneReg(700));
    A->audio_path(true);
    A->tx_mute(false);
    A->led(true);
}

/* Sweep 700-1500 Hz: wail rises 2 s / falls 2 s, yelp rises in 1/3 s,
 * phaser in 1/10 s. */
static void sirenTick(void)
{
    static const uint16_t PERIOD[SIREN_N] = { 1, 4000, 330, 100 };
    const uint32_t period = PERIOD[siren];
    uint32_t ph = (A->ticks_ms() - sirenT0) % period;
    if (siren == 1u) ph = (ph < period / 2u) ? ph * 2u : (period - ph) * 2u; /* triangle */
    A->bk_write(REG_71, toneReg((uint16_t)(700u + ph * 800u / period)));
}

/* One loop step: chrono, squelch, journal. */
static void tick(void)
{
    mission = (uint16_t)((A->ticks_ms() - t0) / 1000u);
    if (state == ST_SIREN) { sirenTick(); return; }
    if (state == ST_TX) {
        live->dur = (uint16_t)(mission - live->at);
        if (live->dur >= TX_LIMIT_S) { txStop(); txTimedOut = true; }
        return;
    }
    const bool open = (A->bk_read(REG_0C) & 2u) != 0u;
    if (open != (state == ST_RX)) {
        rxListen(open);
        state = open ? ST_RX : ST_IDLE;
        if (open) { A->backlight_on(); logOpen(false); txTimedOut = false; }
        else live = (void *)0;
    }
    if (state == ST_RX) {
        sNow = sLevel(A->rssi_dbm());
        if (sNow > live->s) live->s = sNow;
        live->dur = (uint16_t)(mission - live->at);
    } else {
        sNow = 0;
    }
}

/* ---- screens ---- */
static void drawHeader(void)
{
    A->status_clear();
    A->print_inverse("TAC", 2, 0, true, true, 16);
    char *o = putTime(text, mission); *o = '\0';
    A->print_tiny(text, 22, 0, true, true);
    A->print_tiny(journalView ? "JOURNAL" : (night ? "NUIT" : "OPS"), 50, 0, true, true);
    A->draw_battery();
}

static void drawOps(void)
{
    char *o;
    const bool blink = ((A->ticks_ms() / 500u) & 1u) != 0u;

    /* line 0: state banner */
    if (state == ST_TX) {
        o = put(text, "EMISSION  ");
        o = putTime(o, live->dur); *o = '\0';
        A->print_bold(text, 0, 127, 0);
        invertLine(0);
    } else if (state == ST_RX) {
        A->print_bold("RECEPTION", 0, 127, 0);
        if (blink) invertLine(0);
    } else if (state == ST_SIREN) {
        A->print_bold(SIREN[siren], 0, 127, 0);
        if (blink) invertLine(0);
    } else if (txDenied) {
        static const char *const WHY[3] = { "TX BLOQUE: BANDE", "BATTERIE FAIBLE", "TENSION HAUTE" };
        A->print_bold(WHY[(txDenied - 1u) % 3u], 0, 127, 0);
    } else if (txTimedOut) {
        A->print_bold("TX COUPE: 2 MIN", 0, 127, 0);
    } else {
        A->print_normal("VEILLE", 0, 127, 0);
    }

    /* lines 1-2: RX frequency, big font */
    const uint32_t rx = A->rx_freq(), tx = A->tx_freq();
    putFreq(text, rx);
    A->print_string(text, 0, 127, 1, 8);

    /* line 3: frequency of the TX VFO (the one tx_state() checks), roger */
    o = put(text, tx != rx ? "TX " : "TX="); putFreq(o, tx);
    A->print_tiny(text, 2, 25, false, true);
    const char *r = ROGER[roger];
    uint8_t n = 0; while (r[n]) n++;
    A->print_tiny(r, (uint8_t)(127u - n * 4u), 25, false, true);   /* right-aligned */

    /* line 4: S-meter, or the microphone scope while transmitting */
    if (state == ST_TX) {
        A->audio_scope(4u, true);
    } else {
        A->audio_scope(4u, false);
        text[0] = 'S'; text[1] = (char)('0' + sNow); text[2] = '\0';
        A->print_tiny(text, 2, 33, false, true);
        for (uint8_t i = 0; i < 9u; i++) {
            uint8_t *p = &A->fb[4][14u + i * 12u];
            const uint8_t bar = (i < sNow) ? 0x7Eu : 0x42u;
            for (uint8_t k = 0; k < 10u; k++) p[k] = (k == 0u || k == 9u) ? 0x7Eu : bar;
        }
    }

    /* line 5: last call */
    if (logCount) {
        const log_t *e = logAt(0);
        o = put(text, e->tx ? "DERNIER TX " : "DERNIER RX ");
        o = putTime(o, e->at); *o = '\0';
    } else {
        put(text, "AUCUN APPEL")[0] = '\0';
    }
    A->print_tiny(text, 2, 41, false, true);

    /* line 6: operational status, inverted */
    A->print_normal(STATUS[status], 2, 0, 6);
    invertLine(6);
}

static void drawJournal(void)
{
    /* Tiny font, columns aligned with the rows below. */
    A->print_tiny("HEURE  SENS S   DUREE", 2, 1, false, true);
    invertLine(0);
    if (!logCount) { A->print_normal("JOURNAL VIDE", 0, 127, 3); return; }
    for (uint8_t i = 0; i < logCount; i++) {
        const log_t *e = logAt(i);
        char *o = putTime(text, e->at);
        o = put(o, e->tx ? "  TX   " : "  RX   ");
        *o++ = e->tx ? '-' : (char)('0' + e->s);
        o = put(o, "   "); o = putTime(o, e->dur); *o = '\0';
        A->print_tiny(text, 2, (uint8_t)(9u + i * 8u), false, true);
    }
}

static void draw(void)
{
    A->display_clear();
    drawHeader();
    if (journalView) drawJournal(); else drawOps();
    if (night) {
        for (uint8_t x = 0; x < 128u; x++) A->status_line[x] ^= 0xFFu;
        for (uint8_t l = 0; l < 7u; l++) invertLine(l);
    }
    A->blit_status(); A->blit_full();
}

static void key(uint8_t k)
{
    txTimedOut = false;
    if (k >= APP_KEY_1 && k <= APP_KEY_7) { status = (uint8_t)(k - APP_KEY_1); return; }
    switch (k) {
        case APP_KEY_MENU: roger = (uint8_t)((roger + 1u) % ROGER_N); break;
        case APP_KEY_F:    journalView = !journalView; break;
        case APP_KEY_STAR: night = !night; break;
        case APP_KEY_0:    if (state == ST_IDLE || state == ST_SIREN) sirenNext(); break;
        case APP_KEY_EXIT: if (state == ST_SIREN) sirenStop(); else running = false; break;
        default: break;
    }
}

__attribute__((section(".text.entry"), used))
void app_main(const app_api_t *api)
{
    uint8_t c[4];
    A = api;
    A->cfg_load(c, 4);
    const bool valid = c[0] == CFG_MAGIC;
    status = (valid && c[1] < STATUS_N) ? c[1] : 0u;
    night  = valid && c[2] != 0u;
    roger  = (valid && c[3] < ROGER_N) ? c[3] : ROGER_MDC;

    running = true; t0 = A->ticks_ms();
    A->backlight_on();
    rxResume();

    uint8_t prev = APP_KEY_INVALID;
    uint32_t lastDraw = 0, lastBattery = t0;
    while (running) {
        uint8_t k = A->get_key();
        const bool saver = k == APP_KEY_SAVER;
        if (saver || k == APP_KEY_WAKE) k = APP_KEY_INVALID;
        if (k != APP_KEY_INVALID) A->backlight_on();

        if (k == APP_KEY_PTT) {
            if (prev != APP_KEY_PTT && state != ST_TX) txStart();
        } else {
            if (prev == APP_KEY_PTT) { txStop(); txDenied = 0; }
            if (k != prev && k != APP_KEY_INVALID) key(k);
        }
        prev = k;

        tick();
        if (state != ST_IDLE) A->backlight_on();

        const uint32_t now = A->ticks_ms();
        if ((!saver || state != ST_IDLE) && now - lastDraw >= 50u) { lastDraw = now; draw(); }
        if (state != ST_TX && now - lastBattery >= 1000u) { lastBattery = now; A->battery_sample(); }
        A->delay_ms(state == ST_SIREN ? 2u : LOOP_MS); A->backlight_update();
    }

    sirenStop();
    txStop();
    rxListen(false);
    A->set_af(APP_AF_MUTE);
    const uint8_t n[4] = { CFG_MAGIC, status, night, roger };
    if (n[0] != c[0] || n[1] != c[1] || n[2] != c[2] || n[3] != c[3])
        A->cfg_save(n, 4);   /* flash written only on change */
}
