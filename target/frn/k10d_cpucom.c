/*
 * K10D companion-CPU (CPUCOM) model.
 *
 * The K10D main CPU talks to a companion processor over a full-duplex SPI link
 * (data 0x5c004043, status 0x5c004040, byte handshake on GPIO 0x50000106, both
 * modelled in op_helper.c). Each transaction the main CPU sends
 *     [cmd][out_size][out_size bytes]
 * and simultaneously clocks in
 *     [resp0][in_size][in_size bytes]
 * resp0 routes the reply through the firmware's CPUCOM response registry
 * (0x104652f4: registry[resp0] -> handler slot 0x74). Facts this model rests on,
 * all read from the firmware (see K10D-BRINGUP.md d313):
 *
 *  - Cmd 0x01 is the main CPU's periodic status poll; its 5 out bytes carry the
 *    main CPU's own status. A reply with resp0 = 0x01 (command echo) is the plain
 *    acknowledgement (d312 sweep).
 *  - The companion CPU's status messages are replies whose resp0 is an ASCII
 *    command letter; the settings manager (cls_105a6a14) registers for 25 of them
 *    (table 0x105a5e06: letter, payload size; event codes 0x105a5e38) and forwards
 *    each as event 0xa00xx to its listeners. At runtime the listeners are:
 *    'A' (9 bytes) -> screen manager (status LCD); 'H' (0x45) and 'B' (0x17) ->
 *    mode controller ('H' sets flag 0x37 bit 0x80, which the startup task waits
 *    on); 'C', 'I' -> object 0x805329c0; 'X' -> object 0x804a9828.
 *  - Payload bytes default to 0xff (status bits are active-low; see build_status).
 *  - Until 'A' arrives the main CPU polls ~300 times/s (status byte 3 = 0x10); the
 *    poll payload is a bit-field record of main-CPU state (field table 0x105a78c4:
 *    byte 3 bits 0x01 field 0x0a, 0x10 field 0x0e, 0x20 field 0x0f set by the startup
 *    state update 0x10435344). Bit 0x20 is NOT an acknowledgement of 'A' as first
 *    thought; it is used here only as the point after which 'A' stops repeating.
 *  - After 'A' the main CPU sends Cmd 0x05 with 0x3d bytes (a settings block).
 *  - Response registry at runtime (0x80048318, 255 x ptr): 0x01 poll context;
 *    0x07 cls_105a7a9c (sends 05/1f/06/2f/07, table 0x105a7a3c); '@'..'Z' except
 *    'E','P' settings manager; 'E','P' cls_105a5cb4; 0x60-0x68 cls_105a7320;
 *    0x70.. cls_105a7230; 0x80..0xd6 cls_105a7640. A reply whose resp0 has no
 *    entry is dropped and its requester waits forever.
 *
 *  - Interrupt vector 31 (ICR15, 0x44f; raw handler 0x1049109e -> irq source 0xf)
 *    is handled by the task-5 poll object (vtable 0x105a7ea0, IRQ interface at
 *    obj+0x20): on source 0xf it posts its flag (obj+0x28) ONLY if its transfer
 *    object is active (0x1046614c). Raised as an "attention" line between
 *    transfers it is ignored every time, so it is not the message-pending signal;
 *    it looks like a transfer-complete/ready interrupt. Opt-in: FRN_DSP_ATTN=1.
 *
 * Behaviour: silent until the Cmd 0x04 POST handshake completes; then raise vector
 * 31 while a status message is pending; deliver it as the
 * reply to the main CPU's Cmd 0x00 (read) or Cmd 0x01 (poll). 'A' first (repeated
 * on polls at most twice, or until the main CPU's poll shows bit 0x20), then each queued boot status
 * message once (default 'H', 'B'), then plain echoes. Other commands are acknowledged by echoing the command byte with
 * in_size 0, except Cmd 0x04 (POST), which keeps the long-standing 0x01 ack.
 * Payloads are NOT known: they default to zero bytes and can be set per letter
 * with FRN_DSP_<letter>=hexbytes (payload only). FRN_DSP_BOOT=HB sets the queue.
 * FRN_DSP_LOG=1 logs every message the model sends and every command it sees.
 */
#include "qemu/osdep.h"
#include "k10d_cpucom.h"

#define MAXMSG 80

typedef struct { uint8_t b[MAXMSG + 2]; int len; } Msg;

/* payload sizes from the firmware's table 0x105a5e06 (letter -> size) */
static const struct { char c; uint8_t size; } k_sizes[] = {
    {'C',0x10},{'D',0x0c},{'W',0x02},{'T',0x20},{'M',0x20},{'O',0x20},{'Q',0x20},{'V',0x04},
    {'F',0x0b},{'H',0x45},{'J',0x10},{'B',0x17},{'K',0x10},{'L',0x10},{'R',0x04},{'@',0x04},
    {'G',0x0b},{'I',0x1b},{'S',0x01},{'N',0x08},{'U',0x01},{'X',0x05},{'A',0x09},{'Y',0x04},
    {'Z',0x06},
};

static int st_init, st_log, st_acked_a, st_cmd, st_pos;
static Msg st_cur;                 /* reply being clocked out this transaction */
static char st_queue[32]; static int st_qn, st_qi;
static char st_pre[16]; static int st_pn, st_pi;     /* sent after POST, before 'A' */
static uint8_t st_tx[MAXMSG + 2]; static int st_txlen;
static uint8_t st_last_status[8]; static int st_last_status_len;
static FILE *st_out;
static int st_attn_sent, st_a_sent, st_post_done, st_a_count;  /* POST = Cmd 0x04 handshake */           /* attention edge delivered for the current backlog */

static int letter_size(char c)
{
    for (size_t i = 0; i < sizeof k_sizes / sizeof k_sizes[0]; i++)
        if (k_sizes[i].c == c) return k_sizes[i].size;
    return -1;
}

static void build_status(char c, Msg *m)
{
    int n = letter_size(c);
    if (n < 0) n = 0;
    memset(m, 0, sizeof *m);
    m->b[0] = (uint8_t)c; m->b[1] = (uint8_t)n; m->len = 2 + n;
    /* Default payload: all ones. The firmware reads these status bits ACTIVE-LOW
     * (cls_105a8a1c item test 0x1046b156: an item is asserted when its bit is 0, except
     * items 0x29/0x2a); all-zero payloads asserted every input at once and drove boot
     * into a shutdown-like mode transition (0x104329b0(...,3) -> 0x10432a9c parks). */
    memset(m->b + 2, 0xff, n);
    /* 'B' byte 0 = exposure mode index (field table 0x105a6480: field 0 = byte 0, 0..0x11,
     * decoded by 0x104f1bb0). 0xff is out of range: the status screen then takes its
     * "no mode" branch, looks up widget 0x2090082 that is never created, calls through a
     * null pointer and the camera restarts. 0 = P (shown as "Progrm Automatic Exposure"). */
    if (c == 'B' && n > 0) m->b[2] = 0x00;
    char var[16]; snprintf(var, sizeof var, "FRN_DSP_%c", c);
    const char *s = getenv(var); int k = 0;
    while (s && *s && k < n) {
        while (*s == ' ' || *s == ',') s++;
        char hb[3] = {0}; int j = 0;
        while (j < 2 && isxdigit((unsigned char)*s)) hb[j++] = *s++;
        if (!j) break;
        m->b[2 + k++] = (uint8_t)strtoul(hb, NULL, 16);
    }
}

/* Timed status messages (FRN_KEYS): "<M insns>:<letter>[:<hex payload>];..." — at that
 * instruction count (millions) the message is queued and the request interrupt is raised;
 * the main CPU then polls and receives it. Used to inject button presses after boot. */
#define LATE_MAX 32
static struct { uint64_t at; Msg m; } late[LATE_MAX];
static int late_n, late_next, late_head, late_tail;   /* scheduled [late_next..late_n); due queue [head..tail) */
static Msg late_due[LATE_MAX];
static uint64_t st_insns;

static void parse_late(void)
{
    const char *q = getenv("FRN_KEYS");
    while (q && *q && late_n < LATE_MAX) {
        char *e; uint64_t at = strtoull(q, &e, 0) * 1000000ull;
        if (e == q || *e != ':') break;
        char c = e[1]; q = e + 2;
        if (letter_size(c) < 0) break;
        build_status(c, &late[late_n].m);
        if (*q == ':') {
            q++; int k = 0, n = late[late_n].m.len - 2;
            while (*q && *q != ';' && k < n) {
                while (*q == ' ' || *q == ',') q++;
                char hb[3] = {0}; int j = 0;
                while (j < 2 && isxdigit((unsigned char)*q)) hb[j++] = *q++;
                if (!j) break;
                late[late_n].m.b[2 + k++] = (uint8_t)strtoul(hb, NULL, 16);
            }
        }
        late[late_n].at = at; late_n++;
        while (*q && *q != ';') q++;
        if (*q == ';') q++;
    }
}

/* Interactive buttons (hw/frn/k10d_display.c, main-loop thread): an 'A' record to send
 * now. Handed over through a small ring read by k10d_cpucom_tick on the CPU thread. */
#define KEY_RING 16
static uint8_t key_ring[KEY_RING][9];
static volatile unsigned key_w, key_r;
void k10d_cpucom_post_key_record(const uint8_t *payload9);
void k10d_cpucom_post_key_record(const uint8_t *payload9)
{
    unsigned w = key_w;
    if (w - key_r >= KEY_RING) return;
    memcpy(key_ring[w % KEY_RING], payload9, 9);
    __atomic_store_n(&key_w, w + 1, __ATOMIC_RELEASE);
}

/* Arbitrary status messages from the main-loop thread (FRN_MSG_FILE, k10d_display.c). */
static Msg msg_ring[KEY_RING];
static volatile unsigned msg_w, msg_r;
void k10d_cpucom_post_msg(char c, const uint8_t *payload, int n);
void k10d_cpucom_post_msg(char c, const uint8_t *payload, int n)
{
    unsigned w = msg_w;
    if (w - msg_r >= KEY_RING || letter_size(c) < 0) return;
    Msg *m = &msg_ring[w % KEY_RING];
    build_status(c, m);
    for (int i = 0; i < n && i < m->len - 2; i++) m->b[2 + i] = payload[i];
    __atomic_store_n(&msg_w, w + 1, __ATOMIC_RELEASE);
}

void k10d_cpucom_tick(void)
{
    st_insns++;
    while (msg_r != __atomic_load_n(&msg_w, __ATOMIC_ACQUIRE) && late_tail - late_head < LATE_MAX) {
        late_due[late_tail++ % LATE_MAX] = msg_ring[msg_r % KEY_RING];
        if (st_log) fprintf(st_out ? st_out : stderr, "[dsp] msg-file: queued '%c'\n", msg_ring[msg_r % KEY_RING].b[0]);
        msg_r++; st_attn_sent = 0;
    }
    /* Button records are released at least KEY_GAP instructions apart: the firmware does not
     * register a release that follows its press by less than ~4-5M instructions (measured: a
     * 3M hold leaves the key "held" and the next press is ignored; 5M works). This emulator
     * runs a few M instructions per second, so a short real key tap needs this stretch.
     * FRN_KEY_GAP=<M insns> overrides (default 6). */
    static uint64_t key_last;
    static long key_gap = -1;
    if (key_gap < 0) { const char *g = getenv("FRN_KEY_GAP"); key_gap = g ? strtol(g, NULL, 0) * 1000000L : 6000000L; }
    if (key_r != __atomic_load_n(&key_w, __ATOMIC_ACQUIRE) && late_tail - late_head < LATE_MAX
        && (key_last == 0 || st_insns - key_last >= (uint64_t)key_gap)) {
        Msg m; build_status('A', &m);
        memcpy(m.b + 2, key_ring[key_r % KEY_RING], 9);
        late_due[late_tail++ % LATE_MAX] = m;
        key_r++; key_last = st_insns;
        st_attn_sent = 0;
    }
    while (late_next < late_n && st_insns >= late[late_next].at && late_tail - late_head < LATE_MAX) {
        late_due[late_tail++ % LATE_MAX] = late[late_next].m;
        if (st_log) fprintf(st_out ? st_out : stderr, "[dsp] key/status message '%c' due at %llu insns\n",
                                 late[late_next].m.b[0], (unsigned long long)st_insns);
        late_next++;
        st_attn_sent = 0;
    }
}

static void init(FILE *out)
{
    st_init = 1; st_out = out;
    st_log = getenv("FRN_DSP_LOG") != NULL;
    parse_late();
    const char *pq = getenv("FRN_DSP_PRE");
    for (; pq && *pq && st_pn < (int)sizeof st_pre; pq++)
        if (letter_size(*pq) >= 0) st_pre[st_pn++] = *pq;
    const char *q = getenv("FRN_DSP_BOOT");
    if (!q) q = "HB";
    if (!pq) { st_pre[0] = 'X'; st_pn = 1; }   /* default: 'X' before 'A' (startup waits for it, 0xd0004) */
    for (; *q && st_qn < (int)sizeof st_queue; q++)
        if (letter_size(*q) >= 0) st_queue[st_qn++] = *q;
}

/* 1 while the companion has something to send: boot messages not yet delivered or a timed /
 * key message queued. Drives its request line (GPIO 0x50000106 bit 0x02), which the vector-31
 * poll gate (cpucom_request_line_asserted 0x1046614c) reads. */
int k10d_cpucom_pending(void)
{
    if (!st_init) return 1;
    return !st_post_done || !st_acked_a || st_pi < st_pn || st_qi < st_qn || late_head < late_tail;
}

int k10d_cpucom_enabled(void)
{
    static int on = -1;                       /* called every instruction: read the env once */
    if (on < 0) { const char *s = getenv("FRN_DSP_MODEL"); on = !(s && s[0] == '0'); }
    return on;
}

void k10d_cpucom_txn_start(FILE *out)
{
    if (!st_init) init(out);
    /* the finished transaction: if it was a status poll, keep the main CPU's status */
    if (st_txlen >= 2 && st_tx[0] == 0x01) {
        st_last_status_len = st_txlen - 2 > 8 ? 8 : st_txlen - 2;
        memcpy(st_last_status, st_tx + 2, st_last_status_len);
        if (!st_acked_a && st_last_status_len >= 4 && (st_last_status[3] & 0x20)) {
            st_acked_a = 1;
            if (st_log) fprintf(st_out, "[dsp] main CPU acknowledged status (poll status byte3=0x%02x)\n",
                                st_last_status[3]);
        }
    } else if (st_txlen >= 1 && st_tx[0] == 0x04 && !st_post_done) {
        st_post_done = 1;
        if (st_log) fprintf(st_out, "[dsp] POST handshake (Cmd:04) done: status messages may start\n");
    }
    if (st_txlen >= 1 && st_log && st_tx[0] != 0x01) {
        fprintf(st_out, "[dsp] main CPU sent Cmd:%02x out_size=%u:", st_tx[0], st_txlen > 1 ? st_tx[1] : 0);
        for (int i = 2; i < st_txlen && i < 2 + 16; i++) fprintf(st_out, " %02x", st_tx[i]);
        fprintf(st_out, "%s\n", st_txlen > 18 ? " ..." : "");
    }
    if (st_txlen >= 3 && st_tx[0] == 0x02 && st_tx[2] == 0x01 && getenv("FRN_DSP_ON02")) {
        /* experiment: after a release request (Cmd 0x02, 01 00) queue status letter(s) */
        for (const char *q = getenv("FRN_DSP_ON02"); *q; q++)
            if (letter_size(*q) >= 0 && late_tail - late_head < LATE_MAX) {
                Msg m; build_status(*q, &m); late_due[late_tail++ % LATE_MAX] = m;
                if (st_log) fprintf(st_out, "[dsp] queued '%c' after release request\n", *q);
            }
        st_attn_sent = 0;
    }
    st_txlen = 0; st_pos = 0; st_cmd = -1;
    st_attn_sent = 0;              /* a transaction happened: may signal again if still pending */
}

/* One-shot external interrupt requests (FRN_MSG_FILE line "!<vec>"), consumed by frn_deliver. */
static volatile uint64_t ext_vec_req;
void k10d_cpucom_raise_vec(int v) { if (v >= 0 && v < 64) __atomic_or_fetch(&ext_vec_req, 1ull << v, __ATOMIC_SEQ_CST); }
/* Forced companion input lines on port 0x50000106 (FRN_MSG_FILE "+<hex>" / "-<hex>"). */
volatile uint32_t k10d_cpucom_hold106;
void k10d_cpucom_hold_lines(uint32_t set, uint32_t clr) { k10d_cpucom_hold106 = (k10d_cpucom_hold106 | set) & ~clr; }
uint64_t k10d_cpucom_take_vecs(void) { return ext_vec_req ? __atomic_exchange_n(&ext_vec_req, 0, __ATOMIC_SEQ_CST) : 0; }

/* Attention (vector 31): asserted while the model has a status message to deliver,
 * as one edge per completed transaction. Returns 1 when the caller should raise it. */
int k10d_cpucom_attention(void)
{
    static int on = -1; if (on < 0) on = getenv("FRN_DSP_ATTN") != NULL;
    if (st_init && !st_attn_sent && st_acked_a && late_head < late_tail) {
        st_attn_sent = 1;
        if (st_log) fprintf(st_out, "[dsp] attention (vector 31): timed message pending\n");
        return 1;
    }
    if (!on || !st_init || st_attn_sent) return 0;
    if (!st_post_done) return 0;
    int pending = (!st_acked_a && !st_a_sent) || (st_acked_a && st_qi < st_qn);
    if (!pending) return 0;
    st_attn_sent = 1;
    if (st_log) fprintf(st_out, "[dsp] attention (vector 31): %s pending\n",
                        !st_acked_a ? "'A'" : "boot status");
    return 1;
}

void k10d_cpucom_tx(uint8_t v)
{
    if (st_txlen < (int)sizeof st_tx) st_tx[st_txlen++] = v;
}

/* The RX byte for position st_pos. The reply is chosen when byte 0 is read; by then
 * the command byte (TX byte 0) has been written. */
uint8_t k10d_cpucom_rx(FILE *out)
{
    if (!st_init) init(out);
    if (st_pos == 0) {
        st_cmd = st_txlen > 0 ? st_tx[0] : 0xff;
        memset(&st_cur, 0, sizeof st_cur);
        if (st_cmd == 0x00 || st_cmd == 0x01) {
            /* Cmd 0x00 = the main CPU reading the message we signalled (vector 31);
             * Cmd 0x01 = its status poll. Either carries our next status message. 'A' is
             * repeated on polls until the main CPU acknowledges it (bit 0x20). */
            if (st_post_done && st_pi < st_pn) build_status(st_pre[st_pi++], &st_cur);
            else if (st_post_done && !st_acked_a && st_a_count < 2 && (st_cmd == 0x01 || !st_a_sent)) {
                build_status('A', &st_cur); st_a_sent = 1;
                if (++st_a_count >= 2) st_acked_a = 1;     /* 'A' at most twice (boot needed a second) */
            }
            else if (st_acked_a && st_qi < st_qn) build_status(st_queue[st_qi++], &st_cur);
            else if (st_acked_a && late_head < late_tail) st_cur = late_due[late_head++ % LATE_MAX];
            else if (st_cmd == 0x01) {
                static const uint8_t echo01[] = { 0x01, 0x04, 0xa1, 0xa2, 0xa3, 0xa4 };
                memcpy(st_cur.b, echo01, sizeof echo01); st_cur.len = sizeof echo01;
                /* Nothing to report: resp0 FRN_DSP_IDLE (default 0x00, an unregistered code,
                 * which the response dispatcher drops, so the poll chain ends). An echo 0x01
                 * goes to the poll context, which re-polls at once when no module listens
                 * (cpucom_ctx_notify_listeners 0x104645e4): an endless storm that keeps the
                 * CPUCOM task (priority 8, busy-waiting on each transfer) running and starves
                 * every lower-priority task. INFERRED: the real chip cannot answer that way;
                 * 0x00 is the simplest reply consistent with the firmware, not an observation.
                 * With it the screen-manager task resumes and renders. FRN_DSP_IDLE=01 = old echo. */
                static int idle = -2;
                if (idle == -2) { const char *e = getenv("FRN_DSP_IDLE"); idle = e ? (int)strtol(e, NULL, 16) : 0x00; }
                if (idle == 0x01) idle = -1;      /* FRN_DSP_IDLE=01: the old immediate echo */
                if (idle >= 0 && st_acked_a && st_qi >= st_qn) { st_cur.b[0] = (uint8_t)idle; st_cur.b[1] = 0; st_cur.len = 2; }
            } else { st_cur.b[0] = 0x00; st_cur.b[1] = 0; st_cur.len = 2; }
            if (st_log && st_cur.b[0] > 0x01)
                fprintf(st_out, "[dsp] status message '%c' (%d bytes) on Cmd:%02x\n",
                        st_cur.b[0], st_cur.len - 2, st_cmd);
        } else if (st_cmd == 0x04) {
            st_cur.b[0] = 0x01; st_cur.len = 1;        /* POST: known-good 0x01 then 0xff */
        } else if (st_cmd == 0x05 || st_cmd == 0x06 || st_cmd == 0x07 || st_cmd == 0x1f || st_cmd == 0x2f) {
            /* This family (table 0x105a7a3c, class cls_105a7a9c) is registered in the
             * response registry only under 0x07: its replies must carry resp0 = 0x07. */
            st_cur.b[0] = 0x07; st_cur.b[1] = 0; st_cur.len = 2;
        } else if (st_cmd == 0x02 && getenv("FRN_DSP_R02")) {
            /* experiment: resp0 for Cmd 0x02 (release request) */
            st_cur.b[0] = (uint8_t)strtoul(getenv("FRN_DSP_R02"), NULL, 16); st_cur.b[1] = 0; st_cur.len = 2;
        } else {
            st_cur.b[0] = (uint8_t)st_cmd; st_cur.b[1] = 0; st_cur.len = 2;   /* echo, no data */
        }
    }
    uint8_t b = st_pos < st_cur.len ? st_cur.b[st_pos] : 0xff;
    st_pos++;
    return b;
}
