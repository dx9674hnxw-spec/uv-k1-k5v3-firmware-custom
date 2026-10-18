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
 * night (inverted) display and a panic button: holding 0 for one second
 * transmits the emergency alert tone, also heard on the speaker (911/1823 Hz alternating every 167 ms,
 * 2 s bursts every 3.01 s) until the user stops it.
 *
 * Keys: PTT transmit · 1-7 status · MENU roger beep · F ops/journal ·
 *       STAR night · 0 held 1 s panic (PTT or EXIT cancels) · EXIT quit.
 */
#include <stdint.h>
#include <stdbool.h>
#include "../app_api.h"

#define LOOP_MS        10u
#define CFG_MAGIC      0x7Du
#define LOG_LEN        6u
#define STATUS_N       7u
#define ROGER_N        5u
#define TX_LIMIT_S     120u      /* own TX time-out: the resident TOT is not exposed */
#define PANIC_HOLD_MS  1000u     /* 0 held this long arms the panic        */
#define PANIC_LO_HZ    911u      /* alert tones, measured from the reference */
#define PANIC_HI_HZ    1823u     /*   recording (an octave apart)            */
#define PANIC_STEP_MS  167u      /* each tone                              */
#define PANIC_ON_MS    2004u     /* 12 tones per burst                     */
#define PANIC_CYCLE_MS 3010u     /* burst + silence                        */

#define REG_0C         0x0Cu     /* bit 1: squelch open                    */
#define REG_30         0x30u
#define REG_70         0x70u
#define REG_71         0x71u     /* tone 1 frequency                       */
#define REG_30_TX_LINK 0xC3FAu   /* BK4819_EnableTXLink                    */
#define REG_30_IDLE    0xC1FEu   /* as BK4819_PlaySingleTone leaves it     */
#define REG_70_TONE1   0xC200u   /* TONE1 on, tuning gain 66               */
#define AF_BEEP        3u        /* BK4819_AF_BEEP: the TX tone on the speaker */

enum { ST_IDLE, ST_RX, ST_TX, ST_PANIC };
enum { LOG_RX, LOG_TX, LOG_PANIC };
enum { ROGER_OFF, ROGER_BIP, ROGER_BIPBOP, ROGER_QUINDAR, ROGER_MDC };

typedef struct {
    uint16_t at;     /* mission second the call started */
    uint16_t dur;    /* seconds                         */
    uint8_t  tx;     /* LOG_RX, LOG_TX or LOG_PANIC     */
    uint8_t  s;      /* peak S level (RX only)          */
} log_t;

/* APCO ten-codes (the usual US meaning; some agencies differ). Each line is
 * at most 17 small-font glyphs, so it stays inside the 128 px line. */
static const char *const STATUS[STATUS_N] = {
    "10-8 EN SERVICE", "10-76 EN ROUTE", "10-97 SUR PLACE", "10-6 OCCUPE",
    "10-7 HORS SERVICE", "10-19 RETOUR BASE", "CODE 4 RAS"
};
static const char *const ROGER[ROGER_N] = {
    "R:OFF", "R:BIP", "R:BIPBOP", "R:QUINDAR", "R:MDC"
};

static const app_api_t *A;
static log_t journal[LOG_LEN];
static log_t *live;               /* entry being timed, NULL when idle */
static uint32_t t0;
static uint16_t mission;
static uint8_t logCount, logHead, state, status, roger, sNow;
static uint32_t panicT0, holdT0;
static uint16_t panicHz;          /* tone currently keyed, 0 = muted */
static bool holding0;
static bool running, night, journalView, txTimedOut;
static uint8_t txDenied;          /* tx_state() code: 1 band/lock/mode, 2 battery low, 3 voltage high */
static char name[11];             /* channel name, "" when unknown (VFO mode) */
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
static void logOpen(uint8_t tx)
{
    live = &journal[logHead];
    logHead = (uint8_t)((logHead + 1u) % LOG_LEN);
    if (logCount < LOG_LEN) logCount++;
    live->at = mission; live->dur = 0; live->tx = tx; live->s = 0;
}

static const log_t *logAt(uint8_t age) { return &journal[(logHead + LOG_LEN - 1u - age) % LOG_LEN]; }

/* ---- radio ---- */
static void panicStop(void);

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
    txDenied = A->tx_state();
    if (txDenied) return;
    rxListen(false);
    A->tx_set_params();     /* carrier + PA + channel CTCSS/DCS, microphone open */
    state = ST_TX;
    txTimedOut = false;
    logOpen(LOG_TX);
}

/* BK4819 REG_71 value for a tone in Hz (driver scale_freq, rounded). */
static uint16_t toneReg(uint16_t hz) { return (uint16_t)(((uint32_t)hz * 1353245u + (1u << 16)) >> 17); }

/* Roger beep, still keyed: ToneCall's tone path, but the tone stays unmuted
 * while REG_71 is rewritten, so multi-tone patterns have no gaps or clicks. */
static void tone(uint16_t hz, uint16_t ms) { A->bk_write(REG_71, toneReg(hz)); A->delay_ms(ms); }

/* Keyed tone path (ToneCall's register sequence), left muted. With local,
 * the tone is also heard on the speaker, as BK4819_PlaySingleTone does for
 * the resident roger beep with DTMF side tone on. */
static void toneOn(bool local)
{
    A->tx_mute(true);
    A->set_af(local ? AF_BEEP : APP_AF_MUTE);
    A->audio_path(local);
    A->bk_write(REG_70, REG_70_TONE1);
    A->bk_write(REG_30, REG_30_TX_LINK);
}

static void toneOff(void)
{
    A->tx_mute(true);
    A->audio_path(false);
    A->set_af(APP_AF_MUTE);
    A->bk_write(REG_70, 0u);
    A->bk_write(REG_30, REG_30_IDLE);
}

static void rogerBeep(void)
{
    toneOn(false);
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
    toneOff();
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

/* ---- panic button: the emergency alert, keyed on the channel ---- */
static void panicStart(void)
{
    txDenied = A->tx_state();
    if (txDenied) return;
    rxListen(false);
    A->tx_set_params();
    toneOn(true);           /* on air and on the speaker */
    state = ST_PANIC;
    panicT0 = A->ticks_ms();
    panicHz = 0;
    logOpen(LOG_PANIC);
    A->backlight_on();
}

static void panicStop(void)
{
    if (state != ST_PANIC) return;
    toneOff();
    A->tx_end();
    state = ST_IDLE;
    live = (void *)0;
    rxResume();
}

static void panicTick(void)
{
    /* No end: only PTT or EXIT stops the alert. */
    const uint32_t ph = (A->ticks_ms() - panicT0) % PANIC_CYCLE_MS;
    const uint16_t hz = ph >= PANIC_ON_MS ? 0u
                      : ((ph / PANIC_STEP_MS) & 1u) ? PANIC_HI_HZ : PANIC_LO_HZ;
    if (hz == panicHz) return;
    if (hz) A->bk_write(REG_71, toneReg(hz));
    if (!hz || !panicHz) A->tx_mute(!hz);   /* the silence keeps the carrier */
    panicHz = hz;
}

/* One loop step: chrono, squelch, journal. */
static void tick(void)
{
    mission = (uint16_t)((A->ticks_ms() - t0) / 1000u);
    if (state == ST_PANIC) {
        panicTick();
        if (live) live->dur = (uint16_t)(mission - live->at);
        return;
    }
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
    } else if (state == ST_PANIC) {
        A->print_bold("!! URGENCE !!", 0, 127, 0);
        if (((A->ticks_ms() / 250u) & 1u) != 0u) invertLine(0);
    } else if (holding0) {
        A->print_normal("MAINTENIR 0...", 0, 127, 0);
    } else if (txDenied) {
        static const char *const WHY[3] = { "TX BLOQUE", "BATT FAIBLE", "TENSION HAUTE" };
        A->print_bold(WHY[(txDenied - 1u) % 3u], 0, 127, 0);
    } else if (txTimedOut) {
        A->print_bold("TX COUPE: 2 MIN", 0, 127, 0);
    } else {
        A->print_normal("VEILLE", 0, 127, 0);
    }

    /* lines 1-2: channel name in the big font, else the RX frequency */
    const uint32_t rx = A->rx_freq(), tx = A->tx_freq();
    putFreq(text, rx);
    A->print_string(name[0] ? name : text, 0, 127, 1, 8);

    /* line 3: RX frequency under a name, ">TX" when the TX VFO differs (the
     * one tx_state() checks), roger on the right */
    o = name[0] ? putFreq(text, rx) : text;
    if (tx != rx) { o = put(o, name[0] ? ">" : "TX "); o = putFreq(o, tx); }
    *o = '\0';
    A->print_tiny(text, 2, 25, false, true);
    const char *r = ROGER[roger];
    uint8_t n = 0; while (r[n]) n++;
    A->print_tiny(r, (uint8_t)(127u - n * 4u), 25, false, true);   /* right-aligned */

    /* line 4: S-meter, the microphone scope while transmitting, or the alert */
    if (state == ST_PANIC) {
        o = put(text, "ALERTE ");
        o = putTime(o, live->dur); *o = '\0';
        A->print_normal(text, 0, 127, 4);
    } else if (state == ST_TX) {
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

    /* line 5: how to stop the alert, else the last call */
    if (state == ST_PANIC) {
        put(text, "PTT OU EXIT: ARRET")[0] = '\0';
    } else if (logCount) {
        const log_t *e = logAt(0);
        static const char *const LAST[3] = { "DERNIER RX ", "DERNIER TX ", "URGENCE " };
        o = put(text, LAST[e->tx]);
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
    for (uint8_t i = 0; i < logCount; i++) {
        const log_t *e = logAt(i);
        char *o = putTime(text, e->at);
        static const char *const DIR[3] = { "  RX   ", "  TX   ", "  SOS  " };
        o = put(o, DIR[e->tx]);
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
        case APP_KEY_EXIT: if (state == ST_PANIC) panicStop(); else running = false; break;
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

    /* Channel name through the BEAM2 export of the TX VFO (a flash read that
     * bypasses the overlay cache). Kept only when that VFO is the one being
     * received; absent service or VFO mode: the frequency stays big. */
    if (A->beam_get) {
        app_beam_channel_t ch;
        A->beam_get(&ch);
        uint8_t n = 0;
        if (ch.rx_frequency == A->rx_freq())
            while (n < 10u && (uint8_t)(ch.name[n] - 0x20u) < 0x5Fu) { name[n] = ch.name[n]; n++; }
        while (n && name[n - 1u] == ' ') n--;
        name[n] = '\0';
    }

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

        if (state == ST_PANIC && k == APP_KEY_PTT) {
            if (prev != APP_KEY_PTT) panicStop();   /* PTT cancels; release+press to talk */
        } else if (k == APP_KEY_PTT) {
            if (prev != APP_KEY_PTT && state != ST_TX && prev == APP_KEY_INVALID) txStart();
        } else {
            if (prev == APP_KEY_PTT) { txStop(); txDenied = 0; }
            if (k != prev && k != APP_KEY_INVALID) key(k);
        }
        /* panic: 0 held PANIC_HOLD_MS from idle or receive */
        holding0 = k == APP_KEY_0 && (state == ST_IDLE || state == ST_RX);
        if (holding0) {
            if (prev != APP_KEY_0) holdT0 = A->ticks_ms();
            else if (A->ticks_ms() - holdT0 >= PANIC_HOLD_MS) { holding0 = false; panicStart(); }
        }
        prev = k;

        tick();
        if (state != ST_IDLE) A->backlight_on();

        const uint32_t now = A->ticks_ms();
        if ((!saver || state != ST_IDLE) && now - lastDraw >= 50u) { lastDraw = now; draw(); }
        if (state != ST_TX && now - lastBattery >= 1000u) { lastBattery = now; A->battery_sample(); }
        A->delay_ms(LOOP_MS); A->backlight_update();
    }

    panicStop();
    txStop();
    rxListen(false);
    A->set_af(APP_AF_MUTE);
    const uint8_t n[4] = { CFG_MAGIC, status, night, roger };
    for (uint8_t i = 0; i < 4u; i++)
        if (n[i] != c[i]) { A->cfg_save(n, 4); break; }   /* flash written only on change */
}
