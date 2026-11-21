/*
 * Fujitsu FR interpreter helper — faithful C port of fremu.py _execute.
 * Executes exactly one instruction at env->pc per call, carrying the FR branch
 * delay slot across calls via env->delay_armed/delay_pc. Memory goes through
 * QEMU's softmmu accessors (big-endian, matching FR), so RAM/ROM/MMIO/devices
 * all work "for free". Validated against fremu by PC/state parity.
 *
 * NOTE (bring-up scope): the Milbeaut timer tick + interrupt delivery and the
 * stateful 0x67000000 / timer-reg side effects are NOT modelled here yet (they
 * become real QEMU devices). The heap is NOT stubbed — real SDRAM means the
 * firmware's own allocator runs.
 * SPDX-License-Identifier: LGPL-2.0-or-later
 */
#include "qemu/osdep.h"
#include "cpu.h"
#include "exec/helper-proto.h"
#include "accel/tcg/cpu-ldst.h"
#include "k10d_cpucom.h"
#include "k10d_flash.h"
#include "k10d_imgproc.h"

/* Direct host access to the board's plain-RAM regions (hw/frn/k10d.c sets these). The
 * interpreter runs every guest instruction through helpers, and QEMU's softmmu lookup for
 * each fetch and load was the dominant cost. Only ROM (0x10000000, 16 MiB), SDRAM
 * (0x80000000, 256 MiB) and work RAM (0x6a000000, 1 MiB) use this; all device models and
 * debug hooks still run before the load. */
extern uint8_t *k10d_host_lowram, *k10d_host_rom, *k10d_host_sdram, *k10d_host_wram;
static inline const uint8_t *frn_host(uint32_t a, unsigned n)
{
    if (a - 0x80000000u <= 0x10000000u - n) return k10d_host_sdram ? k10d_host_sdram + (a - 0x80000000u) : NULL;
    if (a - 0x10000000u <= 0x01000000u - n) return k10d_host_rom ? k10d_host_rom + (a - 0x10000000u) : NULL;
    if (a - 0x6a000000u <= 0x00100000u - n) return k10d_host_wram ? k10d_host_wram + (a - 0x6a000000u) : NULL;
    return NULL;
}
static inline uint32_t frn_ld16(CPUFRNState *e, uint32_t a)
{
    const uint8_t *h = frn_host(a, 2);
    return h ? (uint32_t)(h[0] << 8 | h[1]) : cpu_lduw_be_data(e, a);
}
static inline uint32_t frn_ld32(CPUFRNState *e, uint32_t a)
{
    const uint8_t *h = frn_host(a, 4);
    return h ? ((uint32_t)h[0] << 24 | h[1] << 16 | h[2] << 8 | h[3]) : cpu_ldl_be_data(e, a);
}
/* Low-RAM control registers read every instruction (timer 0x4e/0x4f, ICR 0x440-0x47f). */
static inline uint32_t frn_icr(CPUFRNState *e, uint32_t a)
{
    return k10d_host_lowram ? k10d_host_lowram[a] : cpu_ldub_data(e, a);
}
static CPUFRNState *k10d_img_env;
static uint32_t k10d_img_ram16(uint32_t a) { return cpu_lduw_be_data(k10d_img_env, a); }
static uint32_t k10d_img_ram32(uint32_t a) { return cpu_ldl_be_data(k10d_img_env, a); }
static void k10d_img_st8(uint32_t a, uint8_t v) { cpu_stb_data(k10d_img_env, a, v); }
static uint8_t k10d_img_ld8(uint32_t a) { const uint8_t *h = frn_host(a, 1); return h ? *h : cpu_ldub_data(k10d_img_env, a); }

#define M32 0xffffffffu
#define FW_BASE 0x10000000u
#define FW_END  0x11000000u   /* ROM window top (approx; exact = base+fw_size) */
#define TIMER_VECTOR 24u
#define TIMER_ICR    0x448u
#define DELAYED_VEC  63u
/* Watch-counter / RTC: vec41 = ICR index 25 => ICR reg 0x440+25 = 0x459. The
 * firmware's watch-counter ISR drives the clock tick and (clock-unset) the
 * "Date Adjust" first-boot screen. Fire it periodically once enabled. */
#define WC_VECTOR    41u
#define WC_ICR       0x459u
#define WC_PERIOD    200000u   /* instructions between watch-counter ticks */

static void frn_timer_reg_written(CPUFRNState *e);

/* -------------------------------------------------------------------------
 * Inspectability: env-gated execution tracer (gold-standard core goal).
 * Performance is deliberately secondary; every interrupt and watched call is
 * observable. Controlled entirely by environment variables, parsed once:
 *   FRN_TRACE_FILE=path   send trace output here (default stderr)
 *   FRN_TRACE_IRQ=1       log every interrupt dispatch (vec, handler, from, ilm)
 *   FRN_TRACE_CALLS=hex,hex,...   log each time PC reaches one of these
 *                         addresses, with args r4-r7 and return addr (rp)
 * ------------------------------------------------------------------------- */
#define FRN_WATCH_MAX 32
static int      frn_tr_ready;
static FILE    *frn_tr_out;
static int      frn_tr_irq;
static uint32_t frn_tr_watch[FRN_WATCH_MAX];
static int      frn_tr_watch_n;

static void frn_trace_setup(void)
{
    const char *f, *s;
    if (frn_tr_ready) {
        return;
    }
    frn_tr_ready = 1;
    frn_tr_out = stderr;
    f = getenv("FRN_TRACE_FILE");
    if (f && *f) {
        FILE *fp = fopen(f, "w");
        if (fp) {
            frn_tr_out = fp;
            setvbuf(fp, NULL, _IOLBF, 0);
        }
    }
    frn_tr_irq = (getenv("FRN_TRACE_IRQ") != NULL);
    s = getenv("FRN_TRACE_CALLS");
    while (s && *s && frn_tr_watch_n < FRN_WATCH_MAX) {
        char *end;
        unsigned long v = strtoul(s, &end, 16);
        if (end == s) {
            break;
        }
        frn_tr_watch[frn_tr_watch_n++] = (uint32_t)v;
        s = (*end == ',') ? end + 1 : end;
    }
}

static inline int frn_tr_watched(uint32_t pc)
{
    for (int i = 0; i < frn_tr_watch_n; i++) {
        if (frn_tr_watch[i] == pc) {
            return 1;
        }
    }
    return 0;
}

/*
 * Memory snapshot for inspection. FRN_SNAP=path and FRN_SNAP_AT=<million insns>
 * dump the whole 64 MiB SDRAM (0x80000000..0x84000000) to a raw file once the
 * instruction count crosses the threshold, so the framebuffer can be rendered
 * offline. Written directly from the interpreter (no fragile monitor). A comma
 * list in FRN_SNAP_AT takes successive snapshots (path gets a .N suffix).
 */
/*
 * PC histogram (inspectability): when FRN_HIST is set, count executed PCs in
 * 16-byte buckets and dump the hottest to <FRN_SNAP>.hist.<idx> at snapshot
 * time, so we can see where the running task actually spends its cycles / what
 * loop it is parked in. Keyed by (pc>>4)&0xfffff -> the firmware's 16 MiB window.
 */
#define FRN_HIST_SZ (1u << 20)
static uint32_t *frn_hist;
static int frn_hist_on = -1;

static inline void frn_hist_tick(uint32_t pc)
{
    if (frn_hist_on < 0) {
        frn_hist_on = getenv("FRN_HIST") ? 1 : 0;
        if (frn_hist_on) {
            frn_hist = calloc(FRN_HIST_SZ, sizeof(uint32_t));
            if (!frn_hist) frn_hist_on = 0;
        }
    }
    if (frn_hist_on) {
        frn_hist[(pc >> 4) & (FRN_HIST_SZ - 1)]++;
    }
}

static void frn_hist_dump(const char *path, int idx)
{
    if (!frn_hist_on || !frn_hist) return;
    char fn[512];
    snprintf(fn, sizeof fn, "%s.hist.%d", path, idx);
    FILE *f = fopen(fn, "w");
    if (!f) return;
    /* FRN_HIST_ALL=1 dumps every non-zero bucket (for full boot-chain coverage);
     * otherwise the top 50 by hit-count. */
    if (getenv("FRN_HIST_ALL")) {
        for (uint32_t i = 0; i < FRN_HIST_SZ; i++) {
            if (frn_hist[i]) fprintf(f, "0x%08x  %u\n", 0x10000000u | (i << 4), frn_hist[i]);
        }
    } else {
        for (int top = 0; top < 50; top++) {
            uint32_t best = 0, bi = 0;
            for (uint32_t i = 0; i < FRN_HIST_SZ; i++) {
                if (frn_hist[i] > best) { best = frn_hist[i]; bi = i; }
            }
            if (best == 0) break;
            fprintf(f, "0x%08x  %u\n", 0x10000000u | (bi << 4), best);
            frn_hist[bi] = 0;
        }
    }
    fclose(f);
    fprintf(stderr, "[frn] PC histogram %d -> %s\n", idx, fn);
}

/* Write-address histogram (inspectability): FRN_WRHIST counts writes per 4 KiB
 * page so the most-written region (the framebuffer) is found without guessing. */
static uint32_t *frn_wrhist;
static int frn_wrhist_on = -1;
static inline void frn_wr_hist(uint32_t a)
{
    if (frn_wrhist_on < 0) {
        frn_wrhist_on = getenv("FRN_WRHIST") ? 1 : 0;
        if (frn_wrhist_on) {
            frn_wrhist = calloc(1u << 20, sizeof(uint32_t));
            if (!frn_wrhist) frn_wrhist_on = 0;
        }
    }
    if (frn_wrhist_on) frn_wrhist[(a >> 12) & 0xfffff]++;
}

/* Read-address histogram for MMIO polls (FRN_RDHIST): the register the firmware
 * busy-polls (the wait gate) shows up as the hottest MMIO read. */
static uint32_t *frn_rdhist;
static int frn_rdhist_on = -1;
static inline int frn_is_mmio(uint32_t a)
{
    return (a >= 0x40000000u && a < 0x50000000u) ||
           (a >= 0x67000000u && a < 0x67100000u) ||
           (a >= 0x01000000u && a < 0x10000000u);
}
static inline void frn_rd_hist(uint32_t a)
{
    if (frn_rdhist_on < 0) {
        frn_rdhist_on = getenv("FRN_RDHIST") ? 1 : 0;
        if (frn_rdhist_on) {
            frn_rdhist = calloc(1u << 20, sizeof(uint32_t));
            if (!frn_rdhist) frn_rdhist_on = 0;
        }
    }
    if (frn_rdhist_on && frn_is_mmio(a)) frn_rdhist[(a >> 4) & 0xfffff]++;
}

/* Read-before-write detector (FRN_LOG_RBW=lo-hi): find addresses the firmware READS
 * before ever WRITING them in [lo,hi) -- i.e. DATA it expects to have been pre-
 * initialized (by a boot-ROM stage we don't emulate). Logs addr+PC+value, deduped.
 * Byte-granularity written-bitmap over the window. (Andrew: "missing RAM/ROM data".) */
static uint8_t *frn_rbw_bm; static uint32_t frn_rbw_lo, frn_rbw_hi; static int frn_rbw_init = 0;
static void frn_rbw_setup(void)
{
    frn_rbw_init = 1;
    const char *s = getenv("FRN_LOG_RBW");
    if (!s) return;
    char *e; frn_rbw_lo = (uint32_t)strtoul(s, &e, 16);
    frn_rbw_hi = (*e == '-') ? (uint32_t)strtoul(e + 1, NULL, 16) : frn_rbw_lo + 0x800000;
    size_t n = (frn_rbw_hi - frn_rbw_lo + 7) / 8;
    frn_rbw_bm = calloc(n, 1);
    if (!frn_rbw_bm) frn_rbw_lo = frn_rbw_hi = 0;
}
static inline void frn_rbw_mark(uint32_t a, unsigned sz)
{
    if (!frn_rbw_init) frn_rbw_setup();
    if (!frn_rbw_bm) return;
    for (unsigned i = 0; i < sz; i++) { uint32_t x = a + i;
        if (x >= frn_rbw_lo && x < frn_rbw_hi) { uint32_t o = x - frn_rbw_lo; frn_rbw_bm[o >> 3] |= 1u << (o & 7); } }
}
static inline void frn_rbw_check(CPUFRNState *e, uint32_t a, unsigned sz, uint32_t v)
{
    if (!frn_rbw_init) frn_rbw_setup();
    if (!frn_rbw_bm) return;
    if (a < frn_rbw_lo || a >= frn_rbw_hi) return;
    uint32_t o = a - frn_rbw_lo;
    if (frn_rbw_bm[o >> 3] & (1u << (o & 7))) return;     /* already written */
    /* mark now so we log each address only once */
    for (unsigned i = 0; i < sz; i++) { uint32_t x = a + i; if (x >= frn_rbw_lo && x < frn_rbw_hi) {
        uint32_t oo = x - frn_rbw_lo; frn_rbw_bm[oo >> 3] |= 1u << (oo & 7); } }
    static int n;
    if (n++ < 4000)
        fprintf(frn_tr_out ? frn_tr_out : stderr,
                "[rbw] read-before-write 0x%08x (sz%u) = 0x%08x  pc~0x%08x\n", a, sz, v, e->pc);
}

static void frn_rdhist_dump(const char *path, int idx)
{
    if (!frn_rdhist_on || !frn_rdhist) return;
    char fn[512];
    snprintf(fn, sizeof fn, "%s.rdhist.%d", path, idx);
    FILE *f = fopen(fn, "w");
    if (!f) return;
    for (int top = 0; top < 40; top++) {
        uint32_t best = 0, bi = 0;
        for (uint32_t i = 0; i < (1u << 20); i++) {
            if (frn_rdhist[i] > best) { best = frn_rdhist[i]; bi = i; }
        }
        if (best == 0) break;
        fprintf(f, "0x%08x  %u reads\n", bi << 4, best);
        frn_rdhist[bi] = 0;
    }
    fclose(f);
    fprintf(stderr, "[frn] MMIO read histogram %d -> %s\n", idx, fn);
}

static void frn_wrhist_dump(const char *path, int idx)
{
    if (!frn_wrhist_on || !frn_wrhist) return;
    char fn[512];
    snprintf(fn, sizeof fn, "%s.wrhist.%d", path, idx);
    FILE *f = fopen(fn, "w");
    if (!f) return;
    for (int top = 0; top < 40; top++) {
        uint32_t best = 0, bi = 0;
        for (uint32_t i = 0; i < (1u << 20); i++) {
            if (frn_wrhist[i] > best) { best = frn_wrhist[i]; bi = i; }
        }
        if (best == 0) break;
        fprintf(f, "0x%08x  %u writes\n", bi << 12, best);
        frn_wrhist[bi] = 0;
    }
    fclose(f);
    fprintf(stderr, "[frn] write histogram %d -> %s\n", idx, fn);
}

static void frn_snapshot(CPUFRNState *e)
{
    static const char *path;
    static long counts[8];
    static int n_at, idx, setup;
    static long insns;
    if (!setup) {
        setup = 1;
        path = getenv("FRN_SNAP");
        const char *at = getenv("FRN_SNAP_AT");
        while (at && *at && n_at < 8) {
            char *end; long v = strtol(at, &end, 10);
            if (end == at) break;
            counts[n_at++] = v * 1000000L;
            at = (*end == ',') ? end + 1 : end;
        }
        if (n_at == 0) { counts[n_at++] = 2000L * 1000000L; }
    }
    if (!path || idx >= n_at) {
        return;
    }
    if (++insns < counts[idx]) {
        return;
    }
    char fn[512];
    uint8_t buf[4096];
    snprintf(fn, sizeof fn, "%s.%d", path, idx);
    FILE *f = fopen(fn, "wb");
    if (f) {
        for (uint32_t a = 0x80000000u; a != 0x84000000u; a += 4096) {
            for (int i = 0; i < 4096; i++) {
                buf[i] = cpu_ldub_data(e, a + i);
            }
            fwrite(buf, 1, 4096, f);
        }
        fclose(f);
        fprintf(stderr, "[frn] SDRAM snapshot %d -> %s (after %ld insns)\n",
                idx, fn, insns);
    }
    /* FRN_SNAP_RANGE=hexstart,hexlen: also dump that range to <path>.range.<idx> (e.g. the
     * display layer buffers near the top of SDRAM, outside the 64 MiB dump above). */
    {
        const char *r = getenv("FRN_SNAP_RANGE");
        if (r) {
            char *end; uint32_t ra = (uint32_t)strtoul(r, &end, 16);
            uint32_t rl = (*end == ',') ? (uint32_t)strtoul(end + 1, NULL, 16) : 0x100000;
            snprintf(fn, sizeof fn, "%s.range.%d", path, idx);
            f = fopen(fn, "wb");
            if (f) {
                for (uint32_t o = 0; o < rl; o++) { uint8_t c = cpu_ldub_data(e, ra + o); fwrite(&c, 1, 1, f); }
                fclose(f);
            }
        }
    }
    /* also dump WRAM (0x6a000000, 1 MiB): TCBs + RTOS lists live here */
    snprintf(fn, sizeof fn, "%s.wram.%d", path, idx);
    f = fopen(fn, "wb");
    if (f) {
        for (uint32_t a = 0x6a000000u; a != 0x6a100000u; a += 4096) {
            for (int i = 0; i < 4096; i++) {
                buf[i] = cpu_ldub_data(e, a + i);
            }
            fwrite(buf, 1, 4096, f);
        }
        fclose(f);
        fprintf(stderr, "[frn] WRAM snapshot %d -> %s\n", idx, fn);
    }
    frn_hist_dump(path, idx);
    /* FRN_HIST_RESET: fully zero the PC histogram after each snapshot dump so the
     * NEXT snapshot's histogram is the delta since this one - isolates what a button
     * press (injected between snapshots) actually causes, instead of boot noise. */
    if (frn_hist_on && frn_hist && getenv("FRN_HIST_RESET"))
        memset(frn_hist, 0, FRN_HIST_SZ * sizeof(uint32_t));
    frn_wrhist_dump(path, idx);
    frn_rdhist_dump(path, idx);
    idx++;
}

/* ---- memory (big-endian via target config) ----
 * Low control regs (<0x50) carry timer/DICR side effects and the timer-count
 * read (0x4A/0x4B), matching fremu's read_u8/write_u8; multi-byte accesses to
 * that window decompose to bytes so the side effects fire. */
/* Read-watchpoint (FRN_RDWATCH=hex): log PC whenever the firmware reads from the
 * 64-byte window at that address. Used to tell whether a code path (e.g. the
 * "Date Adjust" string access) is ever reached. */
static uint32_t frn_rdwatch = 0;
static int frn_rdwatch_init = 0;
static inline void frn_rd_watch(CPUFRNState *e, uint32_t a)
{
    if (!frn_rdwatch_init) {
        frn_rdwatch_init = 1;
        const char *s = getenv("FRN_RDWATCH");
        if (s) frn_rdwatch = (uint32_t)strtoul(s, NULL, 16);
    }
    if (frn_rdwatch) {
        static long len = -1;
        if (len < 0) { const char *l = getenv("FRN_RDWATCH_LEN"); len = l ? strtol(l, NULL, 0) : 64; }
        if (a >= frn_rdwatch && a < frn_rdwatch + len) {
            static int n;
            if (n++ < 200) {
                fprintf(frn_tr_out ? frn_tr_out : stderr,
                        "[rdwatch] read 0x%08x (+0x%lx) from pc~0x%08x\n",
                        a, (long)(a - frn_rdwatch), e->pc);
                /* FRN_RDWATCH_STACK=1: also list the code addresses on the stack (caller chain). */
                if (getenv("FRN_RDWATCH_STACK")) {
                    FILE *o = frn_tr_out ? frn_tr_out : stderr;
                    fprintf(o, "[rdwatch]   rp 0x%08x stack:", e->rp);
                    for (int k = 0; k < 256; k++) {
                        uint32_t sv = cpu_ldl_be_data(e, e->regs[15] + k * 4);
                        if (sv >= 0x10000000u && sv < 0x10560000u) fprintf(o, " 0x%08x", sv);
                    }
                    fprintf(o, "\n");
                }
            }
        }
    }
    /* FRN_RDAT_PC=hex: when the PC is within [pc, pc+0x20), log the distinct
     * addresses this instruction window reads (the word a poll-loop spins on). */
    {
        static int rdat_init = 0; static uint32_t rdat_pc = 0;
        if (!rdat_init) { rdat_init = 1; const char *s = getenv("FRN_RDAT_PC");
            if (s) rdat_pc = (uint32_t)strtoul(s, NULL, 16); }
        if (rdat_pc && e->pc >= rdat_pc && e->pc < rdat_pc + 0x20) {
            static uint32_t seen[32]; static int nseen = 0; int found = 0;
            for (int i = 0; i < nseen; i++) if (seen[i] == a) { found = 1; break; }
            if (!found && nseen < 32) {
                seen[nseen++] = a;
                fprintf(frn_tr_out ? frn_tr_out : stderr,
                        "[rdat] pc 0x%08x reads addr 0x%08x\n", e->pc, a);
            }
        }
    }
}

/* Read-override (FRN_FORCE="addr:val,addr:val,…", up to 8): return val for a
 * read at addr. Lets me force a specific flag (e.g. the date-set bit) to a value
 * to test a gate hypothesis without patching the ROM. Width-agnostic: the value
 * is returned for the covering access. */
/* Execution steering, for exploring code the natural run never reaches.
 *   FRN_STEER=pc[:nth]:t|f[,...]          force the conditional branch at pc taken (t)
 *                                          or fall-through (f); nth (decimal, 1-based)
 *                                          limits it to that execution, else every one.
 *   FRN_STEER_CALL=pc[:nth]:target[,...]  at call @Ri / call:D @Ri at pc, call target
 *                                          (hex) instead of Ri — walks vtable slots.
 * Every steered event is logged "[steer]" so a trace records its counterfactuals. */
#define FRN_STEER_MAX 256
typedef struct { uint32_t pc, nth, val, seen; } FrnSteer;
static FrnSteer frn_steer_br[FRN_STEER_MAX], frn_steer_cl[FRN_STEER_MAX];
static int frn_steer_br_n = -1, frn_steer_cl_n = -1;
static FILE *frn_ft_fp;   /* defined with the FRN_FT tracer below */

/* --- Argument recorder (FRN_ARGS) ---------------------------------------------
 * FRN_ARGS=path: for every called function, classify the argument registers r4-r7
 * at the callee's first instruction (after any call:D delay slot) and count the
 * loads/stores the callee itself makes in [arg, arg+0x400): proof that an argument
 * is a pointer, with the largest field offset used. Frames are a shadow call stack
 * popped when execution reaches a frame's return address; accesses count only while
 * SP is within the frame's stack (a task switch runs on another stack).
 * Each call is filed as natural or steered: steered once any FRN_STEER/FRN_STEER_CALL
 * has overridden the firmware's own choice, since later state is not the firmware's.
 * The summary file is rewritten every FRN_ARGS_EVERY recorded calls (default 1M) and
 * at exit. Line format, one per (function, mode):
 *   <va> <natural|steered> calls=<n> a<i>=<zero>,<small>,<neg>,<rom>,<sdram>,<io>,<other>
 *        :deref=<n>:maxoff=0x<off>:sample=0x<v>   (i = 0..3 for r4..r7)
 *        ret=<r0>,<r1>,<r2>,<r3>  first distinct return addresses (call site = ret-2/-4) */
#define FA_CLS 7
#define FA_MAXOFF 0x400u
#define FA_DEPTH 256
typedef struct {
    uint32_t va, used, calls[2];
    uint32_t cls[2][4][FA_CLS], deref[2][4], maxoff[2][4], sample[2][4];
    uint32_t ret[4];   /* first distinct return addresses: the call sites (ret-2 / ret-4) */
} FaEnt;
typedef struct { uint32_t ret, sp, a[4]; FaEnt *e; int st; } FaFrame;
static int fa_on = -1, frn_steered = 0, fa_sp = 0;
static const char *fa_path;
static FaEnt *fa_tab; static uint32_t fa_cap = 1u << 16, fa_used = 0;
static uint64_t fa_n = 0, fa_every = 1000000;
static uint32_t fa_pending = 0xffffffffu, fa_pending_ret;
static FaFrame fa_stack[FA_DEPTH];
static uint32_t *fa_regs;

static int fa_class(uint32_t v)
{
    if (v == 0) return 0;
    if (v < 0x10000u) return 1;
    if (v >= 0xffff0000u) return 2;
    if (v >= 0x10000000u && v < 0x11000000u) return 3;
    if (v >= 0x80000000u && v < 0x90000000u) return 4;
    if (v >= 0x20000000u && v < 0x80000000u) return 5;
    return 6;
}
static void fa_dump(void)
{
    if (fa_on != 1) return;
    char tmp[600]; snprintf(tmp, sizeof tmp, "%s.tmp", fa_path);
    FILE *f = fopen(tmp, "w"); if (!f) return;
    for (uint32_t i = 0; i < fa_cap; i++) {
        FaEnt *e = &fa_tab[i]; if (!e->used) continue;
        for (int st = 0; st < 2; st++) {
            if (!e->calls[st]) continue;
            fprintf(f, "%08x %s calls=%u", e->va, st ? "steered" : "natural", e->calls[st]);
            for (int a = 0; a < 4; a++) {
                fprintf(f, " a%d=", a);
                for (int c = 0; c < FA_CLS; c++) fprintf(f, c ? ",%u" : "%u", e->cls[st][a][c]);
                fprintf(f, ":deref=%u:maxoff=0x%x:sample=0x%08x",
                        e->deref[st][a], e->maxoff[st][a], e->sample[st][a]);
            }
            fprintf(f, " ret=%08x,%08x,%08x,%08x\n", e->ret[0], e->ret[1], e->ret[2], e->ret[3]);
        }
    }
    fclose(f); rename(tmp, fa_path);
}
static int fa_init(void)
{
    if (fa_on >= 0) return fa_on;
    fa_path = getenv("FRN_ARGS");
    fa_on = (fa_path && fa_path[0]) ? 1 : 0;
    if (fa_on) {
        const char *s = getenv("FRN_ARGS_EVERY"); if (s) fa_every = strtoull(s, NULL, 0);
        fa_tab = calloc(fa_cap, sizeof(FaEnt));
        if (!fa_tab) fa_on = 0; else atexit(fa_dump);
    }
    return fa_on;
}
static FaEnt *fa_get(uint32_t va)
{
    if (fa_used * 2 >= fa_cap) return NULL;          /* table full: stop adding */
    uint32_t h = (va >> 1) * 2654435761u;
    for (uint32_t i = 0; i < fa_cap; i++) {
        FaEnt *e = &fa_tab[(h + i) & (fa_cap - 1)];
        if (e->used && e->va == va) return e;
        if (!e->used) { e->used = 1; e->va = va; fa_used++; return e; }
    }
    return NULL;
}
/* do_call: remember the target; the arguments are read when it is reached. */
static inline void fa_call(uint32_t target, uint32_t ret)
{
    if (fa_init() != 1) return;
    fa_pending = target; fa_pending_ret = ret;
}
/* Every instruction, before it executes. */
static inline void fa_step(uint32_t pc, uint32_t *r)
{
    if (fa_on != 1) return;
    fa_regs = r;
    for (int k = fa_sp - 1; k >= 0 && k >= fa_sp - 8; k--)
        if (fa_stack[k].ret == pc) { fa_sp = k; break; }
    if (pc != fa_pending) return;
    fa_pending = 0xffffffffu;
    FaEnt *e = fa_get(pc); if (!e) return;
    int st = frn_steered;
    e->calls[st]++;
    for (int k = 0; k < 4; k++) {
        if (e->ret[k] == fa_pending_ret) break;
        if (!e->ret[k]) { e->ret[k] = fa_pending_ret; break; }
    }
    if (fa_sp == FA_DEPTH) fa_sp = 0;                /* lost track (task switches): restart */
    FaFrame *fr = &fa_stack[fa_sp++];
    fr->ret = fa_pending_ret; fr->sp = r[15]; fr->e = e; fr->st = st;
    for (int a = 0; a < 4; a++) {
        uint32_t v = r[4 + a]; fr->a[a] = v;
        e->cls[st][a][fa_class(v)]++;
        if (fa_class(v) >= 3) e->sample[st][a] = v;
        else if (!e->sample[st][a]) e->sample[st][a] = v;
    }
    if (++fa_n % fa_every == 0) fa_dump();
}
/* Every load/store the firmware makes. */
static inline void fa_mem(uint32_t addr)
{
    if (fa_on != 1 || !fa_sp || !fa_regs) return;
    FaFrame *fr = &fa_stack[fa_sp - 1];
    uint32_t sp = fa_regs[15];
    if (sp > fr->sp || fr->sp - sp > 0x4000u) return;   /* not this frame's stack */
    for (int a = 0; a < 4; a++) {
        uint32_t v = fr->a[a];
        if (fa_class(v) < 3) continue;                   /* small/zero/negative: not a base */
        if (addr >= v && addr - v < FA_MAXOFF) {
            fr->e->deref[fr->st][a]++;
            if (addr - v > fr->e->maxoff[fr->st][a]) fr->e->maxoff[fr->st][a] = addr - v;
        }
    }
}

/* --- Branch-outcome recorder (FRN_BRANCHES) ------------------------------------
 * FRN_BRANCHES=path: per conditional branch PC, how often it was taken and how often
 * it fell through, split natural/steered like FRN_ARGS. One line per (pc, mode):
 *   <pc> <target> <natural|steered> taken=<n> fall=<n>
 * Rewritten every FRN_ARGS_EVERY calls by fa_dump's cadence and at exit. Used to find
 * branch sides the firmware never takes (frontier) without a full FRN_FT trace.   */
typedef struct { uint32_t pc, target, used, n[2][2]; } FbEnt;
static int fb_on = -1; static const char *fb_path;
static FbEnt *fb_tab; static uint32_t fb_cap = 1u << 18, fb_used = 0;
static void fb_dump(void)
{
    if (fb_on != 1) return;
    char tmp[600]; snprintf(tmp, sizeof tmp, "%s.tmp", fb_path);
    FILE *f = fopen(tmp, "w"); if (!f) return;
    for (uint32_t i = 0; i < fb_cap; i++) {
        FbEnt *e = &fb_tab[i]; if (!e->used) continue;
        for (int st = 0; st < 2; st++)
            if (e->n[st][0] || e->n[st][1])
                fprintf(f, "%08x %08x %s taken=%u fall=%u\n", e->pc, e->target,
                        st ? "steered" : "natural", e->n[st][1], e->n[st][0]);
    }
    fclose(f); rename(tmp, fb_path);
}
static void fb_record(uint32_t pc, uint32_t target, int take)
{
    if (fb_on < 0) {
        fb_path = getenv("FRN_BRANCHES"); fb_on = (fb_path && fb_path[0]) ? 1 : 0;
        if (fb_on) { fb_tab = calloc(fb_cap, sizeof(FbEnt)); if (!fb_tab) fb_on = 0; else atexit(fb_dump); }
    }
    if (fb_on != 1 || fb_used * 2 >= fb_cap) return;
    uint32_t h = (pc >> 1) * 2654435761u;
    for (uint32_t i = 0; i < fb_cap; i++) {
        FbEnt *e = &fb_tab[(h + i) & (fb_cap - 1)];
        if (!e->used) { e->used = 1; e->pc = pc; e->target = target; fb_used++; }
        if (e->pc == pc) { e->n[frn_steered][take ? 1 : 0]++; break; }
    }
    static uint64_t k; if (++k % 20000000 == 0) fb_dump();
}

/* --- Per-task position recorder (FRN_TASKS) ------------------------------------
 * FRN_TASKS=path: tracks the current task (low 16 bits of the word at 0x6a003758 hold
 * id<<16|prio; we use the id) and, per task, the last PC it executed outside the kernel
 * (0x1000c000-0x10012000) on its own (user, S=1) stack, plus that moment's rp. At exit (and every 50M instructions)
 * writes one line per task: id, instructions run, switches in, last PC, rp — where each
 * task is parked. Kernel addresses: K10D REALOS image layout.                       */
static int ft_on = -1; static const char *ft_path;
static uint32_t ft_last_pc[64], ft_last_rp[64]; static uint64_t ft_ins[64], ft_in[64];
static int ft_cur = -1; static uint64_t ft_n;
static void ft_dump(void)
{
    if (ft_on != 1) return;
    FILE *f = fopen(ft_path, "w"); if (!f) return;
    for (int i = 0; i < 64; i++)
        if (ft_ins[i]) fprintf(f, "task %2d ins=%llu switches_in=%llu last_pc=%08x rp=%08x\n", i,
                               (unsigned long long)ft_ins[i], (unsigned long long)ft_in[i], ft_last_pc[i], ft_last_rp[i]);
    fclose(f);
}
static inline void ft_step(CPUFRNState *env, uint32_t pc)
{
    if (ft_on < 0) { ft_path = getenv("FRN_TASKS"); ft_on = (ft_path && ft_path[0]) ? 1 : 0; if (ft_on) atexit(ft_dump); }
    if (ft_on != 1) return;
    int id = (int)((cpu_ldl_be_data(env, 0x6a003758u) >> 16) & 0x3f);
    if (id != ft_cur) { ft_cur = id; ft_in[id]++; }
    ft_ins[id]++;
    /* Task code runs on the user stack (S=1); interrupt handlers on the system stack. */
    if ((env->sf & 1) && (pc < 0x1000c000u || pc >= 0x10012000u)) { ft_last_pc[id] = pc; ft_last_rp[id] = env->rp; }
    if (++ft_n % 50000000 == 0) ft_dump();
}

/* Steer events go into the FRN_FT trace when it is open, so a trace records
 * its own counterfactuals; otherwise to the IRQ-trace stream. */
static FILE *frn_steer_out(void)
{
    return frn_ft_fp ? frn_ft_fp : (frn_tr_out ? frn_tr_out : stderr);
}

static int frn_steer_parse(const char *s, FrnSteer *tab, int is_call)
{
    int n = 0;
    while (s && *s && n < FRN_STEER_MAX) {
        char *e;
        unsigned long pc = strtoul(s, &e, 16);
        if (e == s || *e != ':') break;
        s = e + 1;
        unsigned long nth = 0, val;
        /* optional decimal nth: present iff another ':' follows the next field */
        const char *colon = strchr(s, ':'), *comma = strchr(s, ',');
        if (colon && (!comma || colon < comma)) {
            nth = strtoul(s, &e, 10);
            if (e == s || *e != ':') break;
            s = e + 1;
        }
        if (is_call) {
            val = strtoul(s, &e, 16);
            if (e == s) break;
            s = e;
        } else {
            if (*s != 't' && *s != 'f') break;
            val = (*s == 't');
            s++;
        }
        tab[n].pc = (uint32_t)pc; tab[n].nth = (uint32_t)nth;
        tab[n].val = (uint32_t)val; tab[n].seen = 0;
        n++;
        if (*s != ',') break;
        s++;
    }
    return n;
}

static int frn_steer_lookup(FrnSteer *tab, int n, uint32_t pc, uint32_t *out)
{
    for (int i = 0; i < n; i++) {
        if (tab[i].pc != pc) continue;
        tab[i].seen++;
        if (tab[i].nth == 0 || tab[i].seen == tab[i].nth) { *out = tab[i].val; return 1; }
    }
    return 0;
}

static int frn_steer_branch(uint32_t pc, int natural, int *take)
{
    if (frn_steer_br_n < 0) frn_steer_br_n = frn_steer_parse(getenv("FRN_STEER"), frn_steer_br, 0);
    uint32_t v;
    if (!frn_steer_br_n || !frn_steer_lookup(frn_steer_br, frn_steer_br_n, pc, &v)) return 0;
    *take = (int)v;
    if ((int)v != (natural != 0)) frn_steered = 1;
    fprintf(frn_steer_out(), "[steer] branch pc=%08x forced=%c natural=%c\n",
            pc, v ? 't' : 'f', natural ? 't' : 'f');
    return 1;
}

static uint32_t frn_steer_call(uint32_t pc, uint32_t natural)
{
    if (frn_steer_cl_n < 0) frn_steer_cl_n = frn_steer_parse(getenv("FRN_STEER_CALL"), frn_steer_cl, 1);
    uint32_t v;
    if (!frn_steer_cl_n || !frn_steer_lookup(frn_steer_cl, frn_steer_cl_n, pc, &v)) return natural;
    fprintf(frn_steer_out(), "[steer] call pc=%08x forced=%08x natural=%08x\n",
            pc, v, natural);
    if (v != natural) frn_steered = 1;
    return v;
}

#define FRN_FORCE_MAX 8
static uint32_t frn_force_a[FRN_FORCE_MAX], frn_force_v[FRN_FORCE_MAX];
static int frn_force_n = -1;
static int frn_force_lookup(uint32_t a, uint32_t *out)
{
    if (frn_force_n < 0) {
        frn_force_n = 0;
        const char *s = getenv("FRN_FORCE");
        while (s && *s && frn_force_n < FRN_FORCE_MAX) {
            char *e1; unsigned long ad = strtoul(s, &e1, 16);
            if (e1 == s || *e1 != ':') break;
            char *e2; unsigned long va = strtoul(e1 + 1, &e2, 16);
            frn_force_a[frn_force_n] = (uint32_t)ad;
            frn_force_v[frn_force_n] = (uint32_t)va;
            frn_force_n++;
            s = (*e2 == ',') ? e2 + 1 : e2;
        }
    }
    for (int i = 0; i < frn_force_n; i++) {
        if (frn_force_a[i] == a) { *out = frn_force_v[i]; return 1; }
    }
    return 0;
}

/* --- Black-box DSP reply feeder (FRN_DSP_REPLY=hexbytes) ------------------
 * The CPUCOM task sends a command over TDR(0x58) then waits for the DSP's reply.
 * There is no DSP, so the reply never arrives (InSize=0 -> timeout). This models
 * the DSP as a black box: after the firmware writes the command to TDR, offer the
 * configured reply bytes on RDR(0x58) reads and assert RDRF in SSR(0x5e); fire
 * vec26 (FRN_FIRE_VECS=26) to drive the RX ISR. Discover the reply the firmware
 * accepts empirically by watching the cmd_handler transaction struct (FRN_DUMP_CMDH). */
static uint8_t  frn_dsp_reply[64]; static int frn_dsp_reply_len = -1;
static int      frn_dsp_pos = 0, frn_dsp_armed = 0;
static int      frn_dsp_rdrf = 0x10;      /* candidate RDRF bit; override FRN_SCI_RDRF */
static long     frn_dsp_feeds = 0, frn_dsp_maxfeeds = 0;
static void frn_dsp_init(void)
{
    if (frn_dsp_reply_len >= 0) return;
    frn_dsp_reply_len = 0;
    const char *s = getenv("FRN_DSP_REPLY");
    while (s && *s && frn_dsp_reply_len < 64) {
        while (*s==' '||*s==',') s++;
        if (!*s) break;
        char buf[3]={0}; int n=0; while (n<2 && isxdigit((unsigned char)*s)) buf[n++]=*s++;
        if (!n) break;
        frn_dsp_reply[frn_dsp_reply_len++] = (uint8_t)strtoul(buf,NULL,16);
    }
    const char *r = getenv("FRN_SCI_RDRF"); if (r) frn_dsp_rdrf = (int)strtoul(r,NULL,16);
    const char *m = getenv("FRN_DSP_MAXFEEDS"); frn_dsp_maxfeeds = m ? strtol(m,NULL,0) : 2000;
}
/* --- Black-box DSP: CPUCOM SPI/CSIO at 0x5c004040(status)/0x5c004043(data) ----
 * The Cmd:04 handshake is a full-duplex SPI transfer (cpucom_spi_xfer 0x10465958):
 * firmware writes a TX byte to the data reg then reads the simultaneous RX byte;
 * the status reg bit10(0x400)=BUSY is polled until clear. The regs are in the
 * 0x5c block (RAM-backed -> read 0 -> all-zero reply -> validation times out). This
 * models the DSP: never-busy status, and a per-byte response stream. The firmware
 * sends [Cmd][Size][data...] and reads [resp0][InSize][data...]; discover the reply
 * that makes the transfer validate (result 0) empirically via FRN_SPI_REPLY. */
#define SPI_STATUS 0x5c004040u
#define SPI_DATA   0x5c004043u
static uint8_t frn_spi_reply[64]; static int frn_spi_reply_len = -1;
static int frn_spi_pos = 0; static int frn_spi_on = 0;
static int frn_spi_busy = 0;   /* pulses 1 after a start, cleared on next status read */
/* TX capture: the firmware writes [Cmd][OutSize][data...] to SPI_DATA. Record it so
 * the reply can be selected PER-COMMAND (the DSP answers Cmd:01 differently from
 * Cmd:04). frn_spi_tx[0]=Cmd, [1]=OutSize, [2..]=data. Reset on txn start. */
static uint8_t frn_spi_tx[64]; static int frn_spi_txlen = 0;
/* Per-command reply for Cmd:01 (the periodic DSP status poll). The full-duplex RX
 * stream is [ack][in-size][payload...]. The flat default stub returns ack=0x01 then
 * 0xff fill -> in-size reads 0xff -> firmware clamps it to 0 (sentinel) -> empty
 * payload -> the type-1 response handler never gets DSP status -> the poll repeats
 * forever and boot never advances past DSP init. So Cmd:01 MUST get a real in-size
 * (!=0xff) plus that many real payload bytes. Values are handler-defined (RAM vtable,
 * not statically known) -> probe via FRN_SPI_R01 (hex bytes, full RX stream incl. the
 * leading ack + in-size). Default: ack=01, in-size=04, payload a1 a2 a3 a4 (probe). */
static uint8_t frn_spi_r01[64]; static int frn_spi_r01_len = -1;
static uint8_t frn_hs_reqprev = 0, frn_hs_pendack = 0; static int frn_hs_busy[3];  /* 0x50000106 handshake: req edges -> ack pulse */
static void frn_spi_init(void)
{
    if (frn_spi_reply_len >= 0) return;
    frn_spi_reply_len = 0;
    const char *s = getenv("FRN_SPI_REPLY");
    /* The DSP/companion chip is ALWAYS physically present on the camera, so its
     * CPUCOM reply is permanent model behavior — not opt-in. Default ON (opt out
     * with FRN_NO_DSP for A/B testing). FRN_SPI_REPLY still overrides the reply
     * bytes. Without it, default to a single 0x01 ack (the known-good handshake
     * value) so the Cmd:04 transfer returns In Size:5 and POST passes. */
    frn_spi_on = (getenv("FRN_NO_DSP") == NULL);
    while (s && *s && frn_spi_reply_len < 64) {
        while (*s==' '||*s==',') s++;
        if (!*s) break;
        char buf[3]={0}; int n=0; while (n<2 && isxdigit((unsigned char)*s)) buf[n++]=*s++;
        if (!n) break;
        frn_spi_reply[frn_spi_reply_len++] = (uint8_t)strtoul(buf,NULL,16);
    }
    if (frn_spi_reply_len == 0) { frn_spi_reply[0] = 0x01; frn_spi_reply_len = 1; }
    /* Cmd:01 per-command reply (full RX stream): FRN_SPI_R01, else default probe. */
    frn_spi_r01_len = 0;
    const char *s1 = getenv("FRN_SPI_R01");
    while (s1 && *s1 && frn_spi_r01_len < 64) {
        while (*s1==' '||*s1==',') s1++;
        if (!*s1) break;
        char buf[3]={0}; int n=0; while (n<2 && isxdigit((unsigned char)*s1)) buf[n++]=*s1++;
        if (!n) break;
        frn_spi_r01[frn_spi_r01_len++] = (uint8_t)strtoul(buf,NULL,16);
    }
    if (frn_spi_r01_len == 0) {
        static const uint8_t def01[] = { 0x01, 0x04, 0xa1, 0xa2, 0xa3, 0xa4 };
        memcpy(frn_spi_r01, def01, sizeof def01); frn_spi_r01_len = sizeof def01;
    }
}

/* --- Full execution + memory trace (FRN_FT) --------------------------------
 * Windowed by instruction count so volume stays sane. Set:
 *   FRN_FT=path          output file (default stderr)
 *   FRN_FT_FROM=<n> FRN_FT_TO=<n>   log only instructions [from,to] (raw count)
 *   FRN_FT_PC=<hex>      alternative: start logging when PC first reaches this,
 *                        for FRN_FT_WIN instructions (default 200000)
 * Emits one line per instruction: "<ic> PC=0x.. r4=.. r5=.. r13=..", and per
 * memory access within the window: "  R/W sz@0x.. =0x..". This is the full path +
 * RAM/MMIO access log to pinpoint exactly where boot diverges. */
static long     frn_ic = 0;              /* global instruction counter */
static int      frn_ft_on = -1, frn_ft_active = 0;
static long     frn_ft_from = 0, frn_ft_to = 0, frn_ft_win = 200000, frn_ft_pcstart = 0, frn_ft_started = 0;
static int      frn_ft_fullregs = 0;     /* FRN_FT_FULLREGS=1: log all 16 regs per line */
static FILE    *frn_ft_fp = NULL;
static void frn_ft_init(void)
{
    if (frn_ft_on >= 0) return;
    const char *s = getenv("FRN_FT");
    frn_ft_on = (s != NULL);
    if (!frn_ft_on) return;
    frn_ft_fp = (s[0] && strcmp(s,"1")) ? fopen(s, "w") : NULL;
    if (!frn_ft_fp) frn_ft_fp = stderr;
    const char *a = getenv("FRN_FT_FROM"); if (a) frn_ft_from = strtol(a, NULL, 0);
    const char *b = getenv("FRN_FT_TO");   if (b) frn_ft_to   = strtol(b, NULL, 0);
    const char *p = getenv("FRN_FT_PC");   if (p) frn_ft_pcstart = strtoul(p, NULL, 16);
    const char *w = getenv("FRN_FT_WIN");  if (w) frn_ft_win = strtol(w, NULL, 0);
    const char *f = getenv("FRN_FT_FULLREGS"); if (f) frn_ft_fullregs = 1;
    if (getenv("FRN_FT_GO") && !frn_ft_pcstart) frn_ft_pcstart = 1;   /* wait for the GO file (pc 1 never matches) */
}
static inline void frn_ft_mem(char kind, uint32_t a, uint32_t v, int sz)
{
    fa_mem(a);
    if (!frn_ft_active) return;
    if (kind == 'W') fprintf(frn_ft_fp, "  W%d @0x%08x =0x%08x\n", sz, a, v);
    else             fprintf(frn_ft_fp, "  R%d @0x%08x\n", sz, a);
}
/* --- Reload-timer bank at 0x5c002000-0x5c00203f (4 channels, stride 0x10) --------
 * Semantics come from the firmware's own timer driver (vtable 0x105a05a0; objects
 * at 0x805520b4/8c/64/3c, ctrl ptr at +0x18, count ptr at +0x1c):
 *   +0 ctrl (16-bit): bit0 EN (start/run), bit1 set by every configure (0x1002),
 *     bit2 UF (expired; writing 1 keeps it, writing 0 clears it), bit3 INTE,
 *     bit4 reload/periodic, bit11 prescale (set = /16: 2.0625 MHz, ms units via
 *     n*0x80e-1; clear = 33 MHz, us units via n*0x21-1), bit12 held during load.
 *   +8 count/reload (32-bit).
 * The delay routine FUN_1043c7b8 starts a channel and spins until UF; the timer
 * interrupt (vec56, ISR 0x1043ce50) posts event 0x2c+ch for each channel with
 * INTE|UF set and the ISR rewrites ctrl to clear UF.
 * Time base: instructions. FRN_TMR_IPT = instructions per 33 MHz tick (default 1). */
#define FRN_TMR_BASE 0x5c002000u
#define FRN_TMR_VEC  56
static long frn_tmr_deadline[4];
static uint8_t frn_tmr_run[4], frn_tmr_uf[4];
static long frn_tmr_ipt = -1;
static void frn_tmr_poll(CPUFRNState *e, int ch)
{
    if (!frn_tmr_run[ch] || frn_ic < frn_tmr_deadline[ch]) return;
    frn_tmr_uf[ch] = 1;
    uint32_t ctrl = cpu_lduw_be_data(e, FRN_TMR_BASE + ch * 0x10);
    if (ctrl & 0x10) {             /* reload mode: next period */
        uint32_t rl = cpu_ldl_be_data(e, FRN_TMR_BASE + ch * 0x10 + 8);
        long per = ((long)rl + 1) * ((ctrl & 0x800) ? 16 : 1) * frn_tmr_ipt;
        frn_tmr_deadline[ch] += per > 0 ? per : 1;
    } else {
        frn_tmr_run[ch] = 0;
    }
}
static int frn_tmr_ch(uint32_t a)
{
    return (a >= FRN_TMR_BASE && a < FRN_TMR_BASE + 0x40 && (a & 0xf) == 0) ? (int)((a - FRN_TMR_BASE) >> 4) : -1;
}
/* After the firmware's ctrl write has been stored. */
static void frn_tmr_ctrl_written(CPUFRNState *e, int ch, uint32_t v)
{
    if (frn_tmr_ipt < 0) { const char *s = getenv("FRN_TMR_IPT"); frn_tmr_ipt = s ? strtol(s, NULL, 0) : 1;
                           if (frn_tmr_ipt < 1) frn_tmr_ipt = 1; }
    frn_tmr_poll(e, ch);
    { static int dbg = -1; if (dbg < 0) dbg = getenv("FRN_TMR_DBG") != NULL;
      if (dbg) fprintf(stderr, "[tmr] ch%d ctrl<-%04x run=%d uf=%d ic=%ld rl=%u pc=%08x\n", ch, v, frn_tmr_run[ch],
                       frn_tmr_uf[ch], frn_ic, cpu_ldl_be_data(e, FRN_TMR_BASE + ch * 0x10 + 8), e->pc); }
    if (!(v & 0x4)) frn_tmr_uf[ch] = 0;
    /* Fujitsu reload timer TMCSR: bit1 CNTE (count enable), bit0 TRG (software trigger, reads 0).
     * The firmware clears UF with a read-modify-write; if TRG read back as 1 that write retriggered
     * the one-shot forever (release sequencer 0x1040fbc8 never finished). FRN_TMR_OLD=1: old rule. */
    static int old = -1; if (old < 0) old = getenv("FRN_TMR_OLD") != NULL;
    if (!old) {
        if (!(v & 0x2)) { frn_tmr_run[ch] = 0; return; }
        if (!(v & 0x1) || (v & 0x1000)) return;
        uint32_t rl = cpu_ldl_be_data(e, FRN_TMR_BASE + ch * 0x10 + 8);
        frn_tmr_deadline[ch] = frn_ic + ((long)rl + 1) * ((v & 0x800) ? 16 : 1) * frn_tmr_ipt;
        frn_tmr_run[ch] = 1;
        cpu_stw_be_data(e, FRN_TMR_BASE + ch * 0x10, v & ~0x1u);   /* TRG is write-only */
        return;
    }
    if (!(v & 0x1)) { frn_tmr_run[ch] = 0; return; }
    if (!frn_tmr_run[ch] && !(v & 0x1000)) {
        uint32_t rl = cpu_ldl_be_data(e, FRN_TMR_BASE + ch * 0x10 + 8);
        frn_tmr_deadline[ch] = frn_ic + ((long)rl + 1) * ((v & 0x800) ? 16 : 1) * frn_tmr_ipt;
        frn_tmr_run[ch] = 1;
    }
}
static uint32_t frn_tmr_ctrl_read(CPUFRNState *e, int ch, uint32_t stored)
{
    frn_tmr_poll(e, ch);
    return (stored & ~0x4u) | (frn_tmr_uf[ch] ? 0x4u : 0);
}
/* vec56 level: any channel with INTE and UF. */
static int frn_tmr_irq(CPUFRNState *e)
{
    int any = 0;
    for (int ch = 0; ch < 4; ch++) {
        frn_tmr_poll(e, ch);
        if (frn_tmr_uf[ch] && (cpu_lduw_be_data(e, FRN_TMR_BASE + ch * 0x10) & 0x8)) any = 1;
    }
    return any;
}

static inline uint32_t rd8(CPUFRNState *e, uint32_t a)
{
    if (a == 0x5c004023u || a == 0x5c004024u) return 0xffu;      /* serial channel 2 RX (idle bus) */
    if (a == 0x5c004003u || a == 0x5c004004u) return 0xffu;      /* SR actuator SPI RX (idle) */

    frn_ft_mem('R', a, 0, 1);
    frn_rd_hist(a);
    frn_rd_watch(e, a);
    /* Black-box DSP GPIO handshake at 0x50000106: the firmware sets bit 0x40 ("byte
     * ready" req to DSP) and polls bit 0x01 ("DSP ready" ack). Model the DSP acking:
     * bit 0x01 mirrors bit 0x40 (ack follows req), so the per-byte handshake proceeds. */
    /* dev2 (settings EEPROM/serial on 0x5c005000) status: bit0x01=ready. RAM-backed ->
     * never sets -> firmware spins (FUN_1043fd24). Report ready so transfers proceed. */
    if (a == 0x5c005000u) { frn_spi_init();
        if (frn_spi_on) return cpu_ldub_data(e, a) | 0x01u; }
    /* FRN_GPIO107=hex: main-CPU input pins on port 0x50000107, ORed into reads. Bits 0x20 /
     * 0x80 / 0x40 are the active-low inputs the screen manager reports as status items
     * 0x2b / 0x2c / 0x2d (flag objects at screen manager +0x68/+0x6c/+0x70); the port is
     * RAM-backed and reads 0 (= all asserted) without this. Default 0x80: item 0x2c released.
     * With it asserted, every companion status update sends the mode controller to mode 0
     * (rear display off) instead of passing keys to the UI. 0x40 is left asserted (with it
     * released the key messages are not processed); 0x20 unknown. FRN_GPIO107=0 = old behaviour. */
    if (a == 0x50000107u) { static int g = -2;
        if (g == -2) { const char *e = getenv("FRN_GPIO107"); g = e ? (int)strtol(e, NULL, 16) : 0x80; }
        if (g) return cpu_ldub_data(e, a) | (uint32_t)g; }
    if (a == 0x50000106u) { frn_spi_init();
        if (frn_spi_on) { uint32_t b = cpu_ldub_data(e, a);
            /* Companion handshake lines (code-derived): the main CPU drives request bits
             * 0x20/0x40/0x80; the companion answers on 0x01/0x02/0x04. A transfer step is
             * req up -> wait ack clear, req down -> wait ack set. Line 0x01 is idle clear with a
             * short busy pulse after request 0x20 falls: the capture task's start-up
             * (0x10506bc0 -> 0x10466f00, no timeout) waits for 0x01 to be clear, and with the
             * old inverse-of-request rule it never was. FRN_HS_OLD=1: the old rule for all lines. */
            static int old = -1; if (old < 0) old = getenv("FRN_HS_OLD") ? 1 : 0;
            if (old) return (b & 0xf8u) | (((~b) >> 5) & 0x07u);
            /* Only line 0x01 changes: busy pulse after request 0x20 falls, idle clear.
             * Lines 0x02/0x04 keep the inverse-of-request rule (boot handshake depends on it). */
            uint32_t ack = ((~b) >> 5) & 0x06u;
            if (frn_hs_busy[0] > 0) { ack |= 0x01; frn_hs_busy[0]--; }
            return (b & 0xf8u) | ack | (k10d_cpucom_hold106 & 0x07u); } }
    if (a == SPI_DATA) { frn_spi_init();
        if (frn_spi_on) {
            /* Select the reply by the captured command byte (frn_spi_tx[0]). Cmd:01 is
             * the periodic status poll and needs a real in-size + payload; everything
             * else keeps the flat default (ack 0x01 then 0xff), which the tolerant
             * Cmd:04 POST accepts. */
            uint8_t b;
            uint8_t cmd = (frn_spi_txlen > 0) ? frn_spi_tx[0] : 0xff;
            /* Companion-CPU model (k10d_cpucom.c) unless a legacy probe is configured. */
            static int use_model = -1;
            if (use_model < 0) use_model = k10d_cpucom_enabled() && !getenv("FRN_SPI_INJ")
                                           && !getenv("FRN_SPI_R01") && !getenv("FRN_SPI_REPLY");
            if (use_model) {
                b = k10d_cpucom_rx(frn_tr_out ? frn_tr_out : stderr);
            } else if (cmd == 0x01) {
                /* FRN_SPI_INJ=N:hexbytes[;N:hexbytes...] — answer the N-th Cmd:01 poll (1-based)
                 * with this full RX stream instead: a message the DSP originates, routed by its
                 * first byte through the response registry (e.g. 41 09 ... = command 'A'). */
                static int inj_k = -1, txn = 0; static int inj_n[8], inj_len[8]; static uint8_t inj[8][80];
                if (inj_k < 0) {
                    inj_k = 0; const char *q = getenv("FRN_SPI_INJ");
                    while (q && *q && inj_k < 8) {
                        inj_n[inj_k] = (int)strtol(q, (char **)&q, 0); if (*q == ':') q++;
                        inj_len[inj_k] = 0;
                        while (*q && *q != ';' && inj_len[inj_k] < 80) { while (*q == ' ' || *q == ',') q++;
                            char hb[3] = {0}; int k = 0; while (k < 2 && isxdigit((unsigned char)*q)) hb[k++] = *q++;
                            if (!k) break; inj[inj_k][inj_len[inj_k]++] = (uint8_t)strtoul(hb, NULL, 16); }
                        inj_k++; if (*q == ';') q++;
                    }
                }
                if (frn_spi_pos == 0) txn++;
                int hit = -1;
                for (int k = 0; k < inj_k; k++) if (inj_n[k] == txn) hit = k;
                if (hit >= 0) {
                    b = (frn_spi_pos < inj_len[hit]) ? inj[hit][frn_spi_pos] : 0xff;
                    if (frn_spi_pos == 0) fprintf(frn_tr_out ? frn_tr_out : stderr,
                        "[spi] injected DSP message on Cmd:01 poll #%d (resp0=0x%02x, %d bytes)\n", txn, inj[hit][0], inj_len[hit]);
                } else
                b = (frn_spi_pos < frn_spi_r01_len) ? frn_spi_r01[frn_spi_pos] : 0xff;
            } else {
                b = (frn_spi_pos < frn_spi_reply_len) ? frn_spi_reply[frn_spi_pos] : 0xff;
            }
            if (getenv("FRN_SPI_LOG")) fprintf(frn_tr_out?frn_tr_out:stderr,
                "[spi] RX byte[%d]=0x%02x (cmd=0x%02x) pc=0x%08x\n", frn_spi_pos, b, cmd, e->pc);
            frn_spi_pos++;
            return b;
        }
    }
    { uint32_t fv; if (frn_force_lookup(a, &fv)) return fv & 0xff; }
    if (a == 0x4A) return (e->tmr_count >> 8) & 0xff;
    if (a == 0x4B) return e->tmr_count & 0xff;
    /* Debug UART status reg at 0x60: bit3 (0x08) = TX buffer ready/empty. The
     * firmware's serial puts() (FUN_103b764c) busy-waits on this before writing
     * the TX data reg 0x61. Unmodeled -> infinite wait. Report TX always ready. */
    if (a == 0x60) return 0x08;
    { uint32_t r = cpu_ldub_data(e, a); frn_rbw_check(e, a, 1, r); return r; }
}
/* Write-watchpoint (FRN_WRWATCH=hex[,FRN_WRWATCH_LEN]): log PC+value on writes
 * into the window — to find the code that populates a struct (e.g. the settings
 * load that reveals the persistent-store interface). */
static uint32_t frn_wrwatch = 0; static long frn_wrwatch_len = 0; static int frn_wrwatch_init = 0;
static inline void frn_wr_watch(CPUFRNState *e, uint32_t a, uint32_t v)
{
    if (!frn_wrwatch_init) {
        frn_wrwatch_init = 1;
        const char *s = getenv("FRN_WRWATCH");
        if (s) frn_wrwatch = (uint32_t)strtoul(s, NULL, 16);
        const char *l = getenv("FRN_WRWATCH_LEN"); frn_wrwatch_len = l ? strtol(l, NULL, 0) : 4;
    }
    if (frn_wrwatch && a >= frn_wrwatch && a < frn_wrwatch + frn_wrwatch_len) {
        static int nzinit = 0, nzonly = 0;
        if (!nzinit) { nzinit = 1; nzonly = getenv("FRN_WRWATCH_NZ") ? 1 : 0; }
        if (nzonly && v == 0) return;
        static int n;
        if (n++ < 2000000) {
            fprintf(frn_tr_out ? frn_tr_out : stderr,
                    "[wrwatch] write 0x%08x (+0x%lx) = 0x%08x from pc~0x%08x rp 0x%08x\n",
                    a, (long)(a - frn_wrwatch), v, e->pc, e->rp);
            fflush(frn_tr_out ? frn_tr_out : stderr);
        }
    }
    /* FRN_WRVAL=hex: log any store whose VALUE equals this (find where a pointer is bound). */
    {
        static int vinit = 0; static uint32_t wval = 0;
        if (!vinit) { vinit = 1; const char *s = getenv("FRN_WRVAL"); if (s) wval = (uint32_t)strtoul(s, NULL, 16); }
        if (wval && v == wval) {
            static int vn;
            if (vn++ < 2000)
                fprintf(frn_tr_out ? frn_tr_out : stderr,
                        "[wrval] 0x%08x stored to 0x%08x from pc~0x%08x rp 0x%08x\n", v, a, e->pc, e->rp);
        }
    }
    /* FRN_WRAT_PC=hex[,len]: when PC is within [pc, pc+len) (default 0x40), log
     * the distinct addresses this code window WRITES — finds a rasterizer's
     * pixel target. Histograms targets into 0x10000-granular buckets. */
    {
        static int init = 0; static uint32_t wrat_pc = 0; static long wrat_len = 0x40;
        if (!init) { init = 1; const char *s = getenv("FRN_WRAT_PC");
            if (s) { char *e2; wrat_pc = (uint32_t)strtoul(s, &e2, 16);
                     if (e2 && *e2==',') wrat_len = strtol(e2+1, NULL, 0); } }
        if (wrat_pc && e->pc >= wrat_pc && e->pc < wrat_pc + wrat_len) {
            static uint32_t bk[64]; static uint32_t cnt[64]; static int nb = 0;
            uint32_t b = a & 0xffff0000u; int i;
            for (i = 0; i < nb; i++) if (bk[i] == b) { cnt[i]++; break; }
            if (i == nb && nb < 64) { bk[nb] = b; cnt[nb] = 1; nb++;
                fprintf(frn_tr_out ? frn_tr_out : stderr,
                        "[wrat] pc-window writes region 0x%08x (first val 0x%08x from pc 0x%08x)\n",
                        b, v, e->pc); }
        }
    }
}

static inline void wr8(CPUFRNState *e, uint32_t a, uint32_t v)
{
    if ((a == 0x5c004023u || a == 0x5c004024u)) { static int lg = -1, n; if (lg < 0) lg = getenv("FRN_CH2_LOG") ? 1 : 0;
        if (lg && n++ < 400) fprintf(stderr, "[ch2] tx 0x%02x (reg %x) pc~0x%08x\n", v & 0xff, a & 0xff, e->pc); }

    if ((a - 0x40020000u) < 0x2000u || (a - 0x400f0000u) < 0x2000u) k10d_img_write8(a, v);   /* converter LUT bytes */
    if ((a >> 24) == 0x10 && k10d_flash_write(e, a, v, 1)) { frn_wr_watch(e, a, v); return; }
    frn_ft_mem('W', a, v, 1);
    frn_wr_hist(a);
    frn_wr_watch(e, a, v);
    cpu_stb_data(e, a, v & 0xff); frn_rbw_mark(a, 1);
    if (a == 0x44) {
        e->dicr_pending = v & 1;
    } else if (a >= 0x48 && a <= 0x4F) {
        frn_timer_reg_written(e);
    } else if (a == 0x50000106u) {
        /* DSP handshake: a req bit (0x20/0x40/0x80) rising schedules one ack pulse
         * (req>>5) that the next read of this reg will deliver then consume. */
        frn_spi_init();
        if (frn_spi_on) { uint8_t nv = v & 0xff;
            uint8_t rising = (uint8_t)(nv & 0xe0) & (uint8_t)~frn_hs_reqprev;
            uint8_t falling = frn_hs_reqprev & (uint8_t)~(nv & 0xe0);
            frn_hs_pendack |= (uint8_t)((rising >> 5) & 0x07u);
            for (int k = 0; k < 3; k++) {
                if (falling & (0x20 << k)) frn_hs_busy[k] = 4;     /* busy pulse after req falls */
                if (nv & (0x20 << k)) frn_hs_busy[k] = 0;          /* req up: ack clear */
            }
            frn_hs_reqprev = nv & 0xe0; }
    } else if (a == SPI_DATA) {
        /* CPUCOM TX byte: record it so the per-command responder can see which
         * command the firmware is sending. [0]=Cmd, [1]=OutSize, [2..]=data. */
        frn_spi_init();
        if (frn_spi_on && frn_spi_txlen < (int)sizeof frn_spi_tx) {
            frn_spi_tx[frn_spi_txlen++] = v & 0xff;
            if (frn_spi_txlen == 1 && (v & 0xff) == 0x02 && getenv("FRN_DSP_STACK")) {
                /* debug: who sends CPUCOM Cmd 0x02? print code-looking words from the stack */
                fprintf(stderr, "[stack] Cmd:02 sent, pc=0x%08x rp=0x%08x sp=0x%08x\n   ", e->pc, e->rp, e->regs[15]);
                for (int k = 0; k < 96; k++) {
                    uint32_t w = cpu_ldl_be_data(e, e->regs[15] + k * 4);
                    if (w >= 0x10000000u && w < 0x10800000u) fprintf(stderr, " %08x", w);
                }
                fprintf(stderr, "\n");
            }
            k10d_cpucom_tx(v & 0xff);
            if (getenv("FRN_SPI_LOG")) fprintf(frn_tr_out ? frn_tr_out : stderr,
                "[spi] TX byte[%d]=0x%02x pc=0x%08x\n", frn_spi_txlen - 1, v & 0xff, e->pc);
        }
    } else if (a == 0x61) {
        /* Debug UART TX data reg: capture the firmware's serial output so boot
         * progress / debug banners are visible. Gated by FRN_UART (default on). */
        static int uinit = -1; if (uinit < 0) uinit = getenv("FRN_UART_OFF") ? 0 : 1;
        if (uinit) { fputc(v & 0xff, frn_tr_out ? frn_tr_out : stderr);
                     fflush(frn_tr_out ? frn_tr_out : stderr); }
    }
}
static inline uint32_t rd16(CPUFRNState *e, uint32_t a)
{
    /* Serial channel 2 at 0x5c004020 (same layout as the companion link at 0x5c004040:
     * +0 control/status, bit 0x100 start, bit 0x800 transfer done; data +3). The capture
     * task's start-up (0x1041dc02 -> 0x104115ec) talks to a device on it and busy-waits on
     * bit 0x800 with no timeout. Model: transfers complete at once (device not identified;
     * received bytes read 0xff). FRN_CH2_LOG=1 logs the bytes sent. */
    if (a == 0x5c004020u) return cpu_lduw_be_data(e, a) | 0x0800u;
    /* CSIO channel 0 at 0x5c004000 = the SR actuator SPI link (status +0, data +3; bit 0x800
     * = transfer done). The SR/display-enable path (0x1048f826 -> 0x10440548) busy-waits on
     * it with no timeout. Model transfers as instant (completion bit always set); RX 0xff.
     * The actuator semantics are not modelled, only the handshake. */
    if (a == 0x5c004000u) return cpu_lduw_be_data(e, a) | 0x0800u;

    if (a < 0x50) return (rd8(e, a) << 8) | rd8(e, a + 1);
    frn_ft_mem('R', a, 0, 2);
    frn_rd_hist(a); frn_rd_watch(e, a);
    { uint32_t fv; if (frn_force_lookup(a, &fv)) return fv & 0xffff; }
    { uint32_t iv; if (k10d_img_read16(a, &iv)) return iv & 0xffff; }   /* image-processor model */
    /* CPUCOM (main<->DSP) SCI status reg at 0x5e: bit2 (0x0004) = TX-complete. The
     * send loop (cpucom_sci_send_byte 0x1043c186) busy-waits while((st & 4)==0);
     * 0x5e is RAM so bit2 never sets -> spin. Report TX-complete so the send
     * progresses and the DSP handshake can proceed. Gated by FRN_DSP_OFF to disable. */
    { int ch = frn_tmr_ch(a); if (ch >= 0) {
        uint32_t r = frn_tmr_ctrl_read(e, ch, cpu_lduw_be_data(e, a));
        if (frn_ft_active) fprintf(frn_ft_fp, "  R2 @0x%08x =0x%08x\n", a, r);
        return r; } }
    if (a == SPI_STATUS) { frn_spi_init();
        uint32_t r = cpu_lduw_be_data(e, a);
        if (frn_spi_on) r &= ~0x0400u;   /* black-box DSP: transfer completes instantly (busy clear) */
        /* Hold BUSY for N status reads after each start (FRN_SPI_BUSY=N, default 20;
         * 0 = instant completion). Real transfers take time; while BUSY the firmware
         * polls its 50 ms timeout timer (FUN_10466234 -> timer channel 0). */
        { static int hold = -1; if (hold < 0) { const char *h = getenv("FRN_SPI_BUSY"); hold = h ? atoi(h) : 20; }
          if (frn_spi_on && hold > 0 && frn_spi_busy > 0) {
              if (frn_spi_busy++ <= hold) r |= 0x0400u; else frn_spi_busy = 0; } }
        return r; }
    if (a == 0x5e) { static int off = -1; if (off < 0) off = getenv("FRN_DSP_OFF") ? 1 : 0;
        frn_dsp_init();
        uint32_t r = cpu_lduw_be_data(e, a); if (!off) r |= 0x0004;
        /* assert RDRF while a black-box reply byte is pending */
        if (frn_dsp_armed && frn_dsp_pos < frn_dsp_reply_len) r |= frn_dsp_rdrf;
        return r; }
    /* RDR(0x58) read: hand the next black-box reply byte to the firmware's RX reader */
    if (a == 0x58) { frn_dsp_init();
        if (frn_dsp_armed && frn_dsp_pos < frn_dsp_reply_len) {
            uint32_t b = frn_dsp_reply[frn_dsp_pos++]; frn_dsp_feeds++;
            if (frn_dsp_pos >= frn_dsp_reply_len) frn_dsp_armed = 0;
            if (getenv("FRN_DSP_LOG")) fprintf(frn_tr_out?frn_tr_out:stderr,
                "[dsp-reply] RDR read -> byte 0x%02x (%d/%d) pc=0x%08x\n", b, frn_dsp_pos, frn_dsp_reply_len, e->pc);
            return b; } }
    { uint32_t r = frn_ld16(e, a); frn_rbw_check(e, a, 2, r); return r; }
}
static inline uint32_t rd32(CPUFRNState *e, uint32_t a)
{
    if (a < 0x50) return (rd8(e, a) << 24) | (rd8(e, a + 1) << 16)
                       | (rd8(e, a + 2) << 8) | rd8(e, a + 3);
    fa_mem(a);
    frn_rd_hist(a); frn_rd_watch(e, a);
    { uint32_t iv; if (k10d_img_read32(a, &iv)) return iv; }   /* image-processor model */
    { uint32_t fv; if (frn_force_lookup(a, &fv)) {
        if (frn_ft_active) fprintf(frn_ft_fp, "  R4 @0x%08x =0x%08x\n", a, fv);
        return fv; } }
    { uint32_t r = frn_ld32(e, a); frn_rbw_check(e, a, 4, r);
      if (frn_ft_active) fprintf(frn_ft_fp, "  R4 @0x%08x =0x%08x\n", a, r);
      return r; }
}
static inline uint32_t rd32(CPUFRNState *e, uint32_t a);
static inline void wr32(CPUFRNState *e, uint32_t a, uint32_t v);
/* DMA channel at 0xd60 (the SD driver's block mover, class vtable 0x105c1218, start
 * 0x104e6920): +0 config (0x813), +2 status (bit 15 busy, bit 8 done, 0x800/0x1000
 * error), +4 control (bit 15 start), +8 source, +0xc destination, +0x18 byte count.
 * The SD read path copies from the host's buffer port 0x67000020 (fixed address) into
 * memory. Model: the copy happens at once in 32-bit units through the normal memory
 * path (so device models see the port accesses); an address inside 0x67000000-0x67000fff
 * is held fixed, others increment; then status = done. */
/* Pending SD-port DMA that was armed before its command (see frn_dma_d60_start):
 * 0 = none, 1 = read (src = port), 2 = write (dst = port). */
static int frn_dma_pending;
static uint32_t frn_dma_p_src, frn_dma_p_dst, frn_dma_p_n;

static void frn_dma_d60_xfer(CPUFRNState *e, uint32_t src, uint32_t dst, uint32_t n)
{
    int sfix = (src >> 12) == 0x67000, dfix = (dst >> 12) == 0x67000;
    static int lg = -1; if (lg < 0) lg = getenv("FRN_DMA_LOG") ? 1 : 0;
    if (lg) fprintf(stderr, "[dma d60] 0x%08x -> 0x%08x  %u bytes\n", src, dst, n);
    { static int pc = -1; if (pc < 0) pc = getenv("FRN_DMA_PC") ? 1 : 0;
      if (pc) { fprintf(stderr, "[dma d60]   pc 0x%08x rp 0x%08x stack:", e->pc, e->rp);
          for (int k = 0; k < 160; k++) {
              uint32_t sv = cpu_ldl_be_data(e, e->regs[15] + k*4);
              if (sv >= 0x10000000u && sv < 0x11000000u) fprintf(stderr, " 0x%08x", sv);
          }
          fprintf(stderr, "\n"); } }
    if (n > 0x1000000) n = 0;
    for (uint32_t i = 0; i < n; i += 4)
        wr32(e, dfix ? dst : dst + i, rd32(e, sfix ? src : src + i));
    cpu_stw_be_data(e, 0xd62, 0x0100);
}

/* Run a DMA that was deferred until the card was positioned by its command. Called from the
 * SDHC command path (hw/frn/k10d.c): flush_read after a CMD17/18, flush_write after a
 * CMD24/25. No-op unless a pending DMA of the matching direction is held. */
static void frn_dma_run_pending(CPUFRNState *e)
{
    extern void k10d_sd_clear_read_fresh(void);
    extern void k10d_sd_clear_write_fresh(void);
    int dir = frn_dma_pending;
    frn_dma_pending = 0;
    if (dir == 1) k10d_sd_clear_read_fresh(); else if (dir == 2) k10d_sd_clear_write_fresh();
    frn_dma_d60_xfer(e, frn_dma_p_src, frn_dma_p_dst, frn_dma_p_n);
}
void frn_dma_d60_flush_read(CPUFRNState *e)  { if (frn_dma_pending == 1) frn_dma_run_pending(e); }
void frn_dma_d60_flush_write(CPUFRNState *e) { if (frn_dma_pending == 2) frn_dma_run_pending(e); }

static void frn_dma_d60_start(CPUFRNState *e)
{
    extern int k10d_sd_read_cmd_fresh(void);  extern void k10d_sd_clear_read_fresh(void);
    extern int k10d_sd_write_cmd_fresh(void); extern void k10d_sd_clear_write_fresh(void);
    uint32_t src = cpu_ldl_be_data(e, 0xd68), dst = cpu_ldl_be_data(e, 0xd6c), n = cpu_ldl_be_data(e, 0xd78);
    int sfix = (src >> 12) == 0x67000, dfix = (dst >> 12) == 0x67000;
    /* A still-pending deferred DMA when a new one is armed is flushed first, against the
     * current card state, as a safety net. */
    if (frn_dma_pending) frn_dma_run_pending(e);
    cpu_stw_be_data(e, 0xd64, cpu_lduw_be_data(e, 0xd64) & 0x7fff);
    /* A port DMA must transfer the data of the SD command that positions the card. The
     * multi-block / RMW transfer engines ARM the DMA before issuing their command
     * (process_sdhc_transfer_request 0x10449658; write_two_blocks_via_vtable 0x1053e0b0), so
     * running it now would hit the PREVIOUS command's stale card position - for a read it
     * copies stale data, for a write it is dropped (no active write command). The single-block
     * paths issue the command FIRST. Distinguish by whether a command of this direction is
     * already outstanding (read_cmd_fresh / write_cmd_fresh): run now if so, else defer until
     * the following command positions the card (frn_dma_d60_flush_read / _write). */
    if (sfix) {
        cpu_stw_be_data(e, 0xd62, 0x0100);
        if (k10d_sd_read_cmd_fresh()) { k10d_sd_clear_read_fresh(); frn_dma_d60_xfer(e, src, dst, n); }
        else { frn_dma_pending = 1; frn_dma_p_src = src; frn_dma_p_dst = dst; frn_dma_p_n = n; }
        return;
    }
    if (dfix) {
        cpu_stw_be_data(e, 0xd62, 0x0100);
        if (k10d_sd_write_cmd_fresh()) { k10d_sd_clear_write_fresh(); frn_dma_d60_xfer(e, src, dst, n); }
        else { frn_dma_pending = 2; frn_dma_p_src = src; frn_dma_p_dst = dst; frn_dma_p_n = n; }
        return;
    }
    frn_dma_d60_xfer(e, src, dst, n);
}
static inline void wr16(CPUFRNState *e, uint32_t a, uint32_t v)
{
    if ((a >> 24) == 0x10 && k10d_flash_write(e, a, v, 2)) { frn_wr_watch(e, a, v); return; }
    if (a < 0x50) { wr8(e, a, v >> 8); wr8(e, a + 1, v); return; }
    frn_ft_mem('W', a, v, 2);
    frn_wr_hist(a); frn_wr_watch(e, a, v);
    cpu_stw_be_data(e, a, v & 0xffff); frn_rbw_mark(a, 2);
    if (a == 0xd64 && (v & 0x8000)) frn_dma_d60_start(e);
    if ((a & 0xffff0000u) == 0x40060000u || (a - 0x40020000u) < 0x2000u || (a - 0x400f0000u) < 0x2000u) {   /* image-processor model */
        k10d_img_env = e; k10d_img_set_store(k10d_img_st8); k10d_img_set_load(k10d_img_ld8);
        k10d_img_write16(a, v & 0xffff, frn_tr_out ? frn_tr_out : stderr, k10d_img_ram16, k10d_img_ram32);
    }
    { int ch = frn_tmr_ch(a); if (ch >= 0) frn_tmr_ctrl_written(e, ch, v & 0xffff); }
    /* CPUCOM SPI black-box: status write with config bit 0x200 = a new transaction
     * is being set up -> reset the per-byte response position. */
    if (a == SPI_STATUS) { frn_spi_init(); if (frn_spi_on) {
        if (v & 0x200) { if (getenv("FRN_SPI_LOG")) fprintf(frn_tr_out?frn_tr_out:stderr,
                "[spi] txn start (status<-0x%04x) reset pos\n", v & 0xffff);
            frn_spi_pos = 0; frn_spi_txlen = 0;
            k10d_cpucom_txn_start(frn_tr_out ? frn_tr_out : stderr); }
        if (v & 0x100) frn_spi_busy = 1;   /* bit8 start -> transfer in progress */
    } }
    /* DSP black-box: the firmware just wrote a byte to TDR(0x58) = sent a command
     * byte. Arm the reply (reset position) so the configured reply is offered on
     * the subsequent RDR reads once the firmware enters its receive state. */
    if (a == 0x58) { frn_dsp_init();
        if (frn_dsp_reply_len > 0 && (frn_dsp_maxfeeds==0 || frn_dsp_feeds < frn_dsp_maxfeeds)) {
            frn_dsp_armed = 1; frn_dsp_pos = 0; } }
}
uint64_t frn_lcd_writes;      /* debug: count of LCD-reg writes */
uint32_t frn_lcd_scanout;     /* debug: scanout base once programmed */
static inline void wr32(CPUFRNState *e, uint32_t a, uint32_t v)
{
    if ((a >> 24) == 0x10 && k10d_flash_enabled()) {
        k10d_flash_write(e, a, v >> 16, 2); k10d_flash_write(e, a + 2, v & 0xffff, 2); frn_wr_watch(e, a, v); return; }
    if (a < 0x50) { wr8(e, a, v >> 24); wr8(e, a + 1, v >> 16);
                    wr8(e, a + 2, v >> 8); wr8(e, a + 3, v); return; }
    frn_ft_mem('W', a, v, 4);
    frn_wr_hist(a); frn_wr_watch(e, a, v);
    if ((a & 0xffff0000u) == 0x40060000u || (a - 0x40020000u) < 0x2000u || (a - 0x400f0000u) < 0x2000u) {   /* image-processor model: two halfwords */
        k10d_img_env = e; k10d_img_set_store(k10d_img_st8); k10d_img_set_load(k10d_img_ld8);
        k10d_img_write16(a, v >> 16, frn_tr_out ? frn_tr_out : stderr, k10d_img_ram16, k10d_img_ram32);
        k10d_img_write16(a + 2, v & 0xffff, frn_tr_out ? frn_tr_out : stderr, k10d_img_ram16, k10d_img_ram32);
    }
    if (a >= 0x40100000 && a < 0x40101000) {
        frn_lcd_writes++;
        if (a == 0x40100800 && v && !frn_lcd_scanout) {
            frn_lcd_scanout = v;
            fprintf(stderr, "[LCD] *** scanout base programmed: 0x40100800 <- %08x (lcd_writes=%llu) ***\n",
                    v, (unsigned long long)frn_lcd_writes);
        }
    }
    cpu_stl_be_data(e, a, v); frn_rbw_mark(a, 4);
}

/* ---- arithmetic helpers (match fremu free helpers) ---- */
static inline int32_t  s32(uint32_t v) { return (int32_t)v; }
static inline int carry32(uint32_t a, uint32_t b)  { return ((uint64_t)a + (uint64_t)b) > M32; }
static inline int scarry32(uint32_t a, uint32_t b) { int64_t r = (int64_t)s32(a) + (int64_t)s32(b); return r < -2147483648LL || r > 2147483647LL; }
static inline int sborrow32(uint32_t a, uint32_t b){ int64_t r = (int64_t)s32(a) - (int64_t)s32(b); return r < -2147483648LL || r > 2147483647LL; }
static inline uint32_t sx8(uint32_t v)  { v &= 0xff; return (v & 0x80) ? v - 0x100 : v; }
static inline uint32_t sext(uint32_t v, int bits) {
    uint32_t m = (bits == 32) ? M32 : ((1u << bits) - 1);
    v &= m;
    if (v & (1u << (bits - 1))) { v |= ~m; }
    return v;
}

static inline void resflags(CPUFRNState *e, uint64_t res, int width) {
    uint64_t m = (width >= 64) ? ~0ULL : ((1ULL << width) - 1);
    e->cc_n = (res >> (width - 1)) & 1;
    e->cc_z = (res & m) == 0;
}

static uint32_t lsr_op(CPUFRNState *e, uint32_t val, int sh) {
    uint32_t mask = (sh == 0) ? 0 : (1u << (sh - 1));
    e->cc_c = (mask & val) != 0;
    uint32_t res = (sh >= 32) ? 0 : (val >> sh);
    resflags(e, res, 32); return res;
}
static uint32_t asr_op(CPUFRNState *e, uint32_t val, int sh) {
    uint32_t mask = (sh == 0) ? 0 : (1u << (sh - 1));
    e->cc_c = (mask & val) != 0;
    uint32_t res = (uint32_t)(s32(val) >> (sh >= 32 ? 31 : sh));
    resflags(e, res, 32); return res;
}
static uint32_t addc_op(CPUFRNState *e, uint32_t a, uint32_t b) {
    uint32_t cf = e->cc_c;
    e->cc_c = carry32(a, b); e->cc_v = scarry32(a, b);
    uint32_t r = a + b;
    e->cc_c = e->cc_c | carry32(r, cf);
    e->cc_v = e->cc_v ^ scarry32(r, cf);
    return r + cf;
}
static uint32_t subc_op(CPUFRNState *e, uint32_t a, uint32_t b) {
    uint32_t cf = e->cc_c;
    e->cc_c = (a < b); e->cc_v = sborrow32(a, b);
    uint32_t r = a - b;
    e->cc_c = e->cc_c | (r < cf);
    e->cc_v = e->cc_v ^ sborrow32(r, cf);
    return r - cf;
}

static int cond(CPUFRNState *e, int op_b) {
    switch (op_b) {
    case 2:  return e->cc_z == 1;
    case 3:  return e->cc_z == 0;
    case 4:  return e->cc_c == 1;
    case 5:  return e->cc_c == 0;
    case 6:  return e->cc_n == 1;
    case 7:  return e->cc_n == 0;
    case 8:  return e->cc_v == 1;
    case 9:  return e->cc_v == 0;
    case 10: return (e->cc_v ^ e->cc_n) == 1;
    case 11: return (e->cc_v ^ e->cc_n) == 0;
    case 12: return ((e->cc_v ^ e->cc_n) | e->cc_z) == 1;
    case 13: return ((e->cc_v ^ e->cc_n) | e->cc_z) == 0;
    case 14: return (e->cc_c | e->cc_z) == 1;
    case 15: return (e->cc_c | e->cc_z) == 0;
    default: return 0;
    }
}

static uint32_t pack_ccr(CPUFRNState *e) {
    return ((e->sf & 1) << 5) | ((e->i_flag & 1) << 4) | ((e->cc_n & 1) << 3)
         | ((e->cc_z & 1) << 2) | ((e->cc_v & 1) << 1) | (e->cc_c & 1);
}
static void set_sflag(CPUFRNState *e, int new_s) {
    new_s &= 1;
    if (new_s != (int)e->sf) {
        if (e->sf == 0) { e->ssp = e->regs[15]; e->regs[15] = e->usp; }
        else            { e->usp = e->regs[15]; e->regs[15] = e->ssp; }
    }
    e->sf = new_s;
}
static void unpack_ccr(CPUFRNState *e, uint32_t v) {
    set_sflag(e, (v >> 5) & 1);
    e->i_flag = (v >> 4) & 1;
    e->cc_n = (v >> 3) & 1; e->cc_z = (v >> 2) & 1;
    e->cc_v = (v >> 1) & 1; e->cc_c = v & 1;
}
static uint32_t pack_ps(CPUFRNState *e) { return (e->ilm << 16) | pack_ccr(e); }
static void unpack_ps(CPUFRNState *e, uint32_t v) {
    uint32_t new_ilm = (v >> 16) & 0x1f;
    if ((e->ilm >> 4) & 1) { new_ilm |= 0x10; }  /* FR ilm4-sticky */
    e->ilm = new_ilm;
    unpack_ccr(e, v & 0x3f);
}

static uint32_t get_sr(CPUFRNState *e, int idx) {
    switch (idx) {
    case 0: return e->tbr;
    case 1: return e->rp;
    case 2: return (e->sf == 0) ? e->regs[15] : e->ssp;
    case 3: return (e->sf == 1) ? e->regs[15] : e->usp;
    case 4: return e->mdh;  case 5: return e->mdl;
    case 6: return e->bp;   case 7: return e->fcr;
    case 8: return e->esr;  case 15: return e->dbr;
    default: return 0;
    }
}
static void set_sr(CPUFRNState *e, int idx, uint32_t val) {
    switch (idx) {
    case 0: e->tbr = val; break;
    case 1: e->rp = val; break;
    case 2: if (e->sf == 0) e->regs[15] = val; else e->ssp = val; break;
    case 3: if (e->sf == 1) e->regs[15] = val; else e->usp = val; break;
    case 4: e->mdh = val; break;  case 5: e->mdl = val; break;
    case 6: e->bp = val; break;   case 7: e->fcr = val; break;
    case 8: e->esr = val; break;  case 15: e->dbr = val; break;
    default: break;
    }
}

static inline void push32(CPUFRNState *e, uint32_t v) {
    e->regs[15] -= 4; wr32(e, e->regs[15], v);
}
/* arm a transfer: delayed => fire after next insn; else immediate */
static inline void go(CPUFRNState *e, uint32_t target, int delayed) {
    if (delayed) { e->delay_armed = 1; e->delay_pc = target; }
    else { e->pc = target; }
}
static inline void do_call(CPUFRNState *e, uint32_t target, uint32_t ret, int delayed) {
    e->rp = ret; fa_call(target, ret); go(e, target, delayed);
}

/* ---- Milbeaut reload timer + FR interrupt delivery (fremu port) ---- */
static void frn_timer_reg_written(CPUFRNState *e)
{
    uint32_t csr = (cpu_ldub_data(e, 0x4E) << 8) | cpu_ldub_data(e, 0x4F);
    e->tmr_reload = (cpu_ldub_data(e, 0x48) << 8) | cpu_ldub_data(e, 0x49);
    int cnte = (csr >> 1) & 1, trg = csr & 1;
    if (cnte && trg) { e->tmr_count = e->tmr_reload; e->tmr_running = 1; e->tmr_div = 0; }
    else if (!cnte) { e->tmr_running = 0; }
}

static void frn_timer_tick(CPUFRNState *e)
{
    if (!e->tmr_running) return;
    e->tmr_div++;
    if (e->tmr_div < 1) return;        /* TIMER_STEPS_PER_TICK = 1 */
    e->tmr_div = 0;
    uint32_t csr = (frn_icr(e, 0x4E) << 8) | frn_icr(e, 0x4F);
    int inte = (csr >> 3) & 1, reld = (csr >> 4) & 1;
    if (e->tmr_count == 0) {
        cpu_stb_data(e, 0x4F, frn_icr(e, 0x4F) | 0x04);   /* UF, raw */
        if (inte && !e->pending_valid) {
            e->pending_vec = TIMER_VECTOR;
            e->pending_level = frn_icr(e, TIMER_ICR) & 0x1F;
            e->pending_valid = 1;
        }
        e->tmr_count = reld ? e->tmr_reload : 0xFFFF;
    } else {
        e->tmr_count = (e->tmr_count - 1) & 0xFFFF;
    }
}

/* Watch-counter / RTC tick: once the firmware has enabled ICR25 (level != the
 * masked value 0x1f), raise vec41 every WC_PERIOD instructions. The ISR reads
 * its device regs at 0x40090000 (background MMIO => 0xffffffff => status/clock
 * bits set) and posts the clock event. Delivery itself is gated by ilm>level in
 * frn_deliver, so a masked ICR25 simply never fires. */
static void frn_watch_tick(CPUFRNState *e)
{
    uint32_t icr = frn_icr(e, WC_ICR) & 0x1F;
    if (icr == 0x1F) return;              /* not enabled by firmware yet */
    if (++e->wc_div < WC_PERIOD) return;
    e->wc_div = 0;
    e->wc_pending = 1;
}

/* Generic periodic-IRQ firer (FRN_FIRE_VECS="43,46,47,..."): fire each listed
 * vector periodically once the firmware has enabled its ICR (level != 0x1f).
 * This is RE-from-firmware: the K10D's imaging peripherals have no datasheet, so
 * we discover which autonomous interrupts advance the boot by firing the armed
 * ones (exactly how the watch-counter/vec41 was found) and watching the effect. */
#define FRN_FIRE_MAX 16
static uint32_t frn_fire_vec[FRN_FIRE_MAX], frn_fire_div[FRN_FIRE_MAX];
static uint8_t  frn_fire_pending[FRN_FIRE_MAX];
static int frn_fire_n = -1;
static long frn_fire_period = 200000;
static void frn_fire_tick(CPUFRNState *e)
{
    if (frn_fire_n < 0) {
        frn_fire_n = 0;
        const char *s = getenv("FRN_FIRE_VECS");
        const char *p = getenv("FRN_FIRE_PERIOD"); if (p) frn_fire_period = strtol(p, NULL, 0);
        while (s && *s && frn_fire_n < FRN_FIRE_MAX) {
            char *end; long v = strtol(s, &end, 0);
            if (end == s) break;
            frn_fire_vec[frn_fire_n++] = (uint32_t)v;
            s = (*end == ',') ? end + 1 : end;
        }
    }
    for (int i = 0; i < frn_fire_n; i++) {
        uint32_t icr = frn_icr(e, 0x440 + (frn_fire_vec[i] - 16)) & 0x1F;
        if (icr == 0x1F) continue;            /* not enabled yet */
        if (++frn_fire_div[i] < (uint32_t)frn_fire_period) continue;
        frn_fire_div[i] = 0;
        frn_fire_pending[i] = 1;
    }
}

/* Built-in autonomous (free-running) timers the firmware unmasks. On real
 * hardware the 32-bit free-run timer (vec43) and the base timers (vec48/49/50)
 * count on their own clock and raise their IRQ periodically once enabled; they
 * are NOT kicked by a task. So, exactly like the watch-counter (vec41), fire
 * each one periodically once the firmware unmasks its ICR (level != 0x1f). This
 * is the peripheral IMPLEMENTATION (always on), distinct from the FRN_FIRE_VECS
 * debug knob. Disable with FRN_NO_AUTOTIMER; retune with FRN_AUTOTIMER_PERIOD.
 * vec41 stays handled by frn_watch_tick. */
/* vec56 = OSDC SUB display IRQ (armed by firmware but never raised = no HW source
 * in emu). Its ISR (0x1043ce50) reads OSDC status 0x5c002000/10/20/30 (bits 0xc =
 * frame ready, modeled in k10d.c) and dispatches OSDC events 0x2c-0x2f; event 0x2d
 * sets Task23's render eventflag 0x804a976c. vec53 (OSDC MAIN) is NOT armed in this
 * boot (autotimer skips masked ICRs); vec56 is the live display IRQ. */
#define FRN_AUTOTIMER_N 5
static const uint32_t frn_autotimer_vec[FRN_AUTOTIMER_N] = { 43, 48, 49, 50, 53 };   /* vec56 = timer bank, modeled (frn_tmr_*) */
static uint32_t frn_autotimer_div[FRN_AUTOTIMER_N];
static uint8_t  frn_autotimer_pending[FRN_AUTOTIMER_N];
static long frn_autotimer_period = 200000;
static int  frn_autotimer_init = 0;
static void frn_autotimer_tick(CPUFRNState *e)
{
    if (!frn_autotimer_init) {
        frn_autotimer_init = 1;
        const char *p = getenv("FRN_AUTOTIMER_PERIOD");
        if (p) frn_autotimer_period = strtol(p, NULL, 0);
        if (getenv("FRN_NO_AUTOTIMER")) frn_autotimer_period = 0;   /* disable */
    }
    if (frn_autotimer_period <= 0) return;
    for (int i = 0; i < FRN_AUTOTIMER_N; i++) {
        uint32_t icr = frn_icr(e, 0x440 + (frn_autotimer_vec[i] - 16)) & 0x1F;
        if (icr == 0x1F) continue;                 /* not unmasked by firmware */
        if (++frn_autotimer_div[i] < (uint32_t)frn_autotimer_period) continue;
        frn_autotimer_div[i] = 0;
        frn_autotimer_pending[i] = 1;
    }
}

static void frn_deliver(CPUFRNState *e)
{
    if (!e->i_flag) return;
    /* fixed sources: timer, dicr, watch-counter, timer bank, cpucom, imgproc, 2 x rescon */
    /* static: QEMU builds with -ftrivial-auto-var-init=zero, which zero-filled these locals on
     * every instruction (75% of this function's time). One vCPU thread uses them. */
    static uint32_t lev[16 + FRN_FIRE_MAX + FRN_AUTOTIMER_N], vec[16 + FRN_FIRE_MAX + FRN_AUTOTIMER_N];
    static int kind[16 + FRN_FIRE_MAX + FRN_AUTOTIMER_N];
    int n = 0;
    if (e->pending_valid) { lev[n] = e->pending_level; vec[n] = e->pending_vec; kind[n] = 0; n++; }
    if (e->dicr_pending)  { lev[n] = frn_icr(e, 0x46f) & 0x1F; vec[n] = DELAYED_VEC; kind[n] = 1; n++; }
    if (e->wc_pending)    { lev[n] = frn_icr(e, WC_ICR) & 0x1F; vec[n] = WC_VECTOR; kind[n] = 2; n++; }
    for (int i = 0; i < frn_fire_n; i++) {
        if (frn_fire_pending[i]) {
            lev[n] = frn_icr(e, 0x440 + (frn_fire_vec[i] - 16)) & 0x1F;
            vec[n] = frn_fire_vec[i]; kind[n] = 10 + i; n++;
        }
    }
    for (int i = 0; i < FRN_AUTOTIMER_N; i++) {
        if (frn_autotimer_pending[i]) {
            lev[n] = frn_icr(e, 0x440 + (frn_autotimer_vec[i] - 16)) & 0x1F;
            vec[n] = frn_autotimer_vec[i]; kind[n] = 30 + i; n++;
        }
    }
    if (frn_tmr_irq(e)) {
        lev[n] = frn_icr(e, 0x440 + (FRN_TMR_VEC - 16)) & 0x1F;
        vec[n] = FRN_TMR_VEC; kind[n] = 3; n++;
    }
    /* Companion-CPU attention line (k10d_cpucom.c): vector 31, level from ICR15. */
    static int cpucom_attn = 0;
    if (!cpucom_attn && k10d_cpucom_enabled() && k10d_cpucom_attention()) cpucom_attn = 1;
    if (cpucom_attn) { lev[n] = frn_icr(e, 0x44f) & 0x1F; vec[n] = 31; kind[n] = 4; n++; }
    /* One-shot vectors requested via FRN_MSG_FILE "!<vec>". External INT ch k = vector 30+k
     * (ch1 = vec31 = cpucom attention), so also latch EIRR (0x38) bit k for those. */
    static uint64_t ext_pend = 0;
    uint64_t nv = k10d_cpucom_take_vecs();
    if (nv) {
        ext_pend |= nv;
        for (int v = 30; v < 38; v++) if (nv & (1ull << v)) wr8(e, 0x38, rd8(e, 0x38) | (1u << (v - 30)));
    }
    for (int v = 16, m = 0; v < 64 && ext_pend && m < 8; v++) if (ext_pend & (1ull << v)) {
        lev[n] = frn_icr(e, 0x440 + (v - 16)) & 0x1F; vec[n] = v; kind[n] = 7; n++; m++;
    }
    /* Image-processor operation engine (k10d_imgproc.c): vector 35, level from ICR19,
     * level-triggered while an enabled status bit is pending. */
    if (k10d_img_irq()) {
        lev[n] = frn_icr(e, 0x453) & 0x1F; vec[n] = 35; kind[n] = 5; n++; }
    /* Resolution converters (k10d_imgproc.c): vectors 39 / 40, levels ICR23 / ICR24. */
    for (int u = 0; u < 2; u++)
        if (k10d_rc_irq(u)) { lev[n] = frn_icr(e, 0x457 + u) & 0x1F; vec[n] = 39 + u; kind[n] = 6; n++; }
    if (n == 0) return;
    /* insertion sort ascending by level (highest priority = lowest number first) */
    for (int i = 1; i < n; i++) {
        uint32_t tl = lev[i], tv = vec[i]; int tk = kind[i];
        int j = i - 1;
        while (j >= 0 && lev[j] > tl) {
            lev[j+1] = lev[j]; vec[j+1] = vec[j]; kind[j+1] = kind[j]; j--;
        }
        lev[j+1] = tl; vec[j+1] = tv; kind[j+1] = tk;
    }
    for (int i = 0; i < n; i++) {
        if (!(e->ilm > lev[i])) continue;
        uint32_t handler = rd32(e, e->tbr + 0x3FC - vec[i] * 4);
        if (!(handler >= FW_BASE && handler < FW_END)) continue;
        if (kind[i] == 0) e->pending_valid = 0;  /* DICR stays until FW clears 0x44 */
        if (kind[i] == 2) e->wc_pending = 0;
        if (kind[i] == 4) cpucom_attn = 0;
        if (kind[i] == 7) ext_pend &= ~(1ull << vec[i]);
        if (kind[i] >= 10 && kind[i] < 30) frn_fire_pending[kind[i] - 10] = 0;
        if (kind[i] >= 30) frn_autotimer_pending[kind[i] - 30] = 0;
        uint32_t saved_ps = pack_ps(e);  /* FR: save pre-trap PS (user S=1) BEFORE entering system mode */
        set_sflag(e, 0);
        push32(e, saved_ps);
        push32(e, e->pc);
        e->ilm = lev[i];
        e->pc = handler;
        if (frn_tr_irq) {
            fprintf(frn_tr_out, "[irq] vec%-2u %-9s -> 0x%08x  ilm->%-2u  "
                    "from 0x%08x\n", vec[i],
                    kind[i]==0?"timer":kind[i]==3?"tmrbank":kind[i]==1?"dicr":kind[i]==2?"watch-cnt":kind[i]==4?"cpucom":kind[i]==5?"imgproc":kind[i]==6?"rescon":kind[i]==7?"ext":kind[i]>=30?"autotmr":"fire",
                    handler, lev[i], rd32(e, e->regs[15]));
        }
        return;
    }
}

/* UI-wake diagnostic (FRN_WAKE=flagobj_hex[,FRN_WAKE_PAT=pattern][,FRN_WAKE_AT=idle-hits]):
 * once the firmware has settled into the idle task (pc=0x10491512), inject a call to
 * the set_flg wrapper FUN_10459708(flagobj, pattern, 0, 0) to wake a task blocked on
 * that eventflag. Breaks the circular init cascade (no peripheral events -> no task
 * runs -> nothing gets wired) by posting the first event by hand, to discover which
 * eventflag drives the UI/compositor. Returns to idle after (rp=idle). */
#define FRN_IDLE_PC 0x10491512u
#define FRN_SETFLG  0x104596ccu   /* real set_flg wrapper (d309 Sable): set_flg(short* idptr, pat). NOT 0x10459708=wai_flg */
#define FRN_WAKE_SCRATCH 0x8ff00000u   /* unused high SDRAM: holds the injected flag id */
static void frn_wake_inject(CPUFRNState *e)
{
    static int init = 0, done = 0; static uint32_t flagobj = 0, pattern = 0xffffffff;
    static long delay = 2000, cnt = 0, next_fire = 0, period = 0, fires = 0, maxfires = 0;
    static long flagid = -1, call_fn = -1, call_arg = 0;
    static long call_fn2 = -1, call_arg2 = 0, gap2 = 3000;  /* optional 2nd sequential call after the 1st returns to idle */
    static uint32_t setflg_addr = FRN_SETFLG;
    if (!init) { init = 1;
        const char *s = getenv("FRN_WAKE"); if (s) flagobj = (uint32_t)strtoul(s, NULL, 16);
        const char *i = getenv("FRN_WAKE_ID"); if (i) flagid = strtol(i, NULL, 0);
        const char *p = getenv("FRN_WAKE_PAT"); if (p) pattern = (uint32_t)strtoul(p, NULL, 16);
        const char *d = getenv("FRN_WAKE_AT"); if (d) delay = strtol(d, NULL, 0);
        const char *pe = getenv("FRN_WAKE_PERIOD"); if (pe) period = strtol(pe, NULL, 0);   /* re-fire every N idle hits (emulate the key-scan timer tick) */
        const char *mf = getenv("FRN_WAKE_MAXFIRES"); if (mf) maxfires = strtol(mf, NULL, 0);
        const char *sf = getenv("FRN_SETFLG"); if (sf) setflg_addr = (uint32_t)strtoul(sf, NULL, 16);
        const char *c = getenv("FRN_CALL");
        if (c) { char *e2; call_fn = strtol(c, &e2, 16); if (*e2==':') call_arg = strtol(e2+1, NULL, 16); }
        const char *c2 = getenv("FRN_CALL2");
        if (c2) { char *e2; call_fn2 = strtol(c2, &e2, 16); if (*e2==':') call_arg2 = strtol(e2+1, NULL, 16); }
        const char *g2 = getenv("FRN_CALL2_GAP"); if (g2) gap2 = strtol(g2, NULL, 0);
        next_fire = delay;
    }
    if ((!flagobj && flagid < 0 && call_fn < 0) || done) return;
    { static uint32_t idle_pc = 0; if (!idle_pc) { const char *ip = getenv("FRN_IDLE_PC");
        idle_pc = ip ? (uint32_t)strtoul(ip, NULL, 16) : FRN_IDLE_PC; }
      if (e->pc != idle_pc) return; }       /* only from the settled idle task (FRN_IDLE_PC overridable) */
    if (cnt++ < next_fire) return;          /* wait until the next scheduled fire */
    /* schedule next fire: periodic (if period>0 and under maxfires) else one-shot */
    if (call_fn2 > 0 && fires == 0) next_fire = cnt + gap2;   /* schedule the 2nd sequential call */
    else if (period > 0 && (maxfires == 0 || fires + 1 < maxfires)) next_fire = cnt + period;
    else done = 1;
    fires++;
    if (call_fn > 0) {                       /* call an arbitrary func(arg) from idle */
        long cfn = (fires == 2 && call_fn2 > 0) ? call_fn2 : call_fn;
        long carg = (fires == 2 && call_fn2 > 0) ? call_arg2 : call_arg;
        e->regs[4] = (uint32_t)carg; e->regs[5] = 0; e->regs[6] = 0; e->regs[7] = 0;
        /* optional extra register args for non-standard ABIs (e.g. TA_ACT uses r8/r9) */
        { const char *s5=getenv("FRN_CALL_R5"); if(s5) e->regs[5]=(uint32_t)strtoul(s5,NULL,16);
          const char *s8=getenv("FRN_CALL_R8"); if(s8) e->regs[8]=(uint32_t)strtoul(s8,NULL,16);
          const char *s9=getenv("FRN_CALL_R9"); if(s9) e->regs[9]=(uint32_t)strtoul(s9,NULL,16);
          const char *s12=getenv("FRN_CALL_R12"); if(s12) e->regs[12]=(uint32_t)strtoul(s12,NULL,16);
          const char *ssp=getenv("FRN_CALL_SP"); if(ssp) e->regs[15]=(uint32_t)strtoul(ssp,NULL,16); }
        e->rp = FRN_IDLE_PC; e->pc = (uint32_t)cfn;
        fprintf(frn_tr_out ? frn_tr_out : stderr,
                "[wake] inject CALL 0x%08lx(r4=0x%08lx r8=0x%08x r9=0x%08x) from idle (fire %ld)\n",
                cfn, carg, e->regs[8], e->regs[9], fires);
        return;
    }
    uint32_t pobj = flagobj;
    if (flagid >= 0) {                      /* raw id: stash as 32-bit word (set_flg does ld @r4,r4 then extsh = low16), point param_1 there */
        cpu_stl_be_data(e, FRN_WAKE_SCRATCH, (uint32_t)(flagid & 0xffff));
        pobj = FRN_WAKE_SCRATCH;
    }
    e->regs[4] = pobj; e->regs[5] = pattern; e->regs[6] = 0; e->regs[7] = 0;
    e->rp = FRN_IDLE_PC;                     /* return to idle after set_flg */
    e->pc = setflg_addr;
    fprintf(frn_tr_out ? frn_tr_out : stderr,
            "[wake] inject set_flg@0x%08x(param1=0x%08x id=%ld pat=0x%08x) fire %ld\n",
            setflg_addr, pobj, flagid, pattern, fires);
}

/* FRN_POKE="addr:val[,addr:val]" : one-shot (or periodic via FRN_POKE_PERIOD) memory writes,
 * applied from the settled idle task. Used to feed the RTOS operational-phase trigger, e.g.
 * FRN_POKE=6a0036c4:1 writes task-id 1 into the act_tsk trigger slot so the tick handler
 * activates it through the firmware's own path. FRN_POKE_AT=idle-hits delay, FRN_POKE_SZ=1/2/4. */
static void frn_poke_tick(CPUFRNState *e)
{
    static int init = 0; static int n = 0; static uint32_t pa[32], pv[32];
    static long delay = 1500, cnt = 0, next = 0, period = 0, fires = 0, maxf = 0; static int sz = 4;
    if (!init) { init = 1;
        const char *s = getenv("FRN_POKE");
        while (s && *s && n < 32) { char *e2; uint32_t a=(uint32_t)strtoul(s,&e2,16);
            if (e2==s||*e2!=':') break; uint32_t v=(uint32_t)strtoul(e2+1,&e2,16);
            pa[n]=a; pv[n]=v; n++; s=(*e2==',')?e2+1:e2; }
        const char *d=getenv("FRN_POKE_AT"); if(d) delay=strtol(d,NULL,0);
        const char *p=getenv("FRN_POKE_PERIOD"); if(p) period=strtol(p,NULL,0);
        const char *m=getenv("FRN_POKE_MAXFIRES"); if(m) maxf=strtol(m,NULL,0);
        const char *z=getenv("FRN_POKE_SZ"); if(z) sz=atoi(z);
        next=delay;
    }
    if (n==0) return;
    static int anypc = -1; if (anypc < 0) anypc = getenv("FRN_POKE_ANYPC") ? 1 : 0;
    if (!anypc) {
        static uint32_t poke_pc = 0; if (!poke_pc) { const char *ip=getenv("FRN_IDLE_PC");
            poke_pc = ip ? (uint32_t)strtoul(ip,NULL,16) : 0x1000f530u; }  /* real idle = bra-self 0x1000f530 */
        if (e->pc != poke_pc) return;
    }  /* FRN_POKE_ANYPC: fire by instruction-boundary count (FRN_POKE_AT), not gated on a specific PC */
    if (cnt++ < next) return;
    if (period>0 && (maxf==0 || fires+1<maxf)) next=cnt+period; else next=0x7fffffffffffffffL;
    fires++;
    for (int i=0;i<n;i++){
        if (sz==1) cpu_stb_data(e,pa[i],(uint8_t)pv[i]);
        else if (sz==2) cpu_stw_be_data(e,pa[i],(uint16_t)pv[i]);
        else cpu_stl_be_data(e,pa[i],pv[i]);
    }
    fprintf(frn_tr_out?frn_tr_out:stderr,"[poke] fire %ld: wrote %d pair(s) sz%d (e.g. 0x%08x=0x%08x)\n",
            fires,n,sz,pa[0],pv[0]);
}

static void frn_interp_one(CPUFRNState *env)
{
    uint32_t *r = env->regs;
    /* FRN_DERAIL=1: keep the last 64 PCs (with r1/rp) and dump them once, the first time
     * execution lands in 0x0-0xfff (a wild jump), to see where the firmware derailed. */
    /* FRN_NO_REBOOT=1: halt the emulator at the first wild jump (<0x1000) instead of letting the
     * firmware reset and boot-loop — so a trace captures exactly ONE boot cycle up to the crash. */
    { static int dr = -1, nrb = -1; static uint32_t ring[64][3]; static unsigned ri; static int dumped;
      if (dr < 0) { dr = getenv("FRN_DERAIL") ? 1 : 0; nrb = getenv("FRN_NO_REBOOT") ? 1 : 0; }
      if (dr || nrb) {
          if (env->pc < 0x1000 && !dumped) { dumped = 1;
              if (dr) { fprintf(stderr, "[derail] pc=0x%08x; last PCs (oldest first):\n", env->pc);
                  for (unsigned k = 0; k < 64; k++) { unsigned j = (ri + k) % 64;
                      fprintf(stderr, "  0x%08x r4=%08x rp=%08x\n", ring[j][0], ring[j][1], ring[j][2]); } }
              if (nrb) { fprintf(stderr, "[no-reboot] halting at first crash pc=0x%08x (cycle 1)\n", env->pc);
                  fflush(NULL); exit(0); } }
          ring[ri % 64][0] = env->pc; ring[ri % 64][1] = r[4]; ring[ri % 64][2] = env->rp; ri++;
      } }
    if (!frn_tr_ready) {
        frn_trace_setup();
    }
    if (!env->delay_armed) {       /* instruction boundary (not a delay slot) */
        frn_timer_tick(env);
        frn_watch_tick(env);
        frn_fire_tick(env);
        frn_autotimer_tick(env);
        frn_deliver(env);          /* may set env->pc to an ISR handler */
        frn_wake_inject(env);      /* diagnostic: post a chosen eventflag from idle */
        frn_poke_tick(env);        /* diagnostic: one-shot/periodic memory writes from idle */
    }
    frn_snapshot(env);
    uint32_t pc = env->pc;
    /* FRN_POKE=pc:reg:val[,pc:reg:val...] — force register `reg` to `val` just BEFORE the
     * instruction at `pc` executes. Used to prove whether a specific register value is
     * load-bearing (e.g. simulate a recompiled callee's lost live-out in the stock firmware). */
    {
        static int fp_n = -2; static uint32_t fp_pc[8], fp_val[8]; static int fp_reg[8];
        if (fp_n == -2) {
            fp_n = 0; const char *s = getenv("FRN_POKE");
            while (s && *s && fp_n < 8) {
                unsigned long a, rg, v;
                if (sscanf(s, "%lx:%lu:%lx", &a, &rg, &v) == 3) {
                    fp_pc[fp_n] = (uint32_t)a; fp_reg[fp_n] = (int)rg; fp_val[fp_n] = (uint32_t)v; fp_n++;
                }
                s = strchr(s, ','); if (s) s++;
            }
        }
        for (int i = 0; i < fp_n; i++)
            if (pc == fp_pc[i]) r[fp_reg[i]] = fp_val[i];
    }
    fa_step(pc, r);
    ft_step(env, pc);
    k10d_img_tick();                                  /* image-processor operation timing */
    k10d_cpucom_tick();                               /* timed companion-CPU messages */
    k10d_flash_tick();                                /* deferred flash image save */
    frn_hist_tick(pc);
    /* Full execution + memory trace (windowed). */
    frn_ft_init();
    frn_ic++;   /* always: also the reload-timer time base (frn_tmr_*); was counted only under FRN_FT */
    if (frn_ft_on) {
        if (frn_ft_pcstart && !frn_ft_started && pc == frn_ft_pcstart) {
            frn_ft_started = 1; frn_ft_from = frn_ic; frn_ft_to = frn_ic + frn_ft_win;
        }
        /* FRN_FT_GO=path: start the FRN_FT_WIN window once this file exists (checked every
         * 2^20 instructions), so a trace can be armed from outside right before an action. */
        { static const char *go = (const char *)1;
          if (go == (const char *)1) go = getenv("FRN_FT_GO");
          if (go && !frn_ft_started && (frn_ic & 0xfffff) == 0 && access(go, F_OK) == 0) {
              frn_ft_pcstart = 1; frn_ft_started = 1; frn_ft_from = frn_ic; frn_ft_to = frn_ic + frn_ft_win;
              fprintf(stderr, "[ft] FRN_FT_GO: window starts at ic %ld\n", frn_ic);
          } }
        frn_ft_active = (frn_ic >= frn_ft_from &&
                         (frn_ft_to == 0 || frn_ic <= frn_ft_to) &&
                         (!frn_ft_pcstart || frn_ft_started));
        /* FRN_FT_FUNCS=file ("0xADDR name" lines): only log entries to listed PCs. */
        static int fn_init = 0; static uint32_t *fn_tab = NULL; static int fn_n = 0;
        if (!fn_init) {
            fn_init = 1; const char *ff = getenv("FRN_FT_FUNCS");
            FILE *fp = ff ? fopen(ff, "r") : NULL;
            if (fp) { char ln[256]; int cap = 0;
                while (fgets(ln, sizeof ln, fp)) { if (strncmp(ln, "0x", 2)) continue;
                    if (fn_n == cap) { cap = cap ? cap * 2 : 4096; fn_tab = g_renew(uint32_t, fn_tab, cap); }
                    fn_tab[fn_n++] = (uint32_t)strtoul(ln, NULL, 16); }
                fclose(fp); }
        }
        if (frn_ft_active && fn_tab) {
            int lo = 0, hi = fn_n - 1, hit = 0;   /* index is sorted */
            while (lo <= hi) { int m = (lo + hi) / 2;
                if (fn_tab[m] == pc) { hit = 1; break; } if (fn_tab[m] < pc) lo = m + 1; else hi = m - 1; }
            if (hit) fprintf(frn_ft_fp, "%ld F=0x%08x r4=%08x r5=%08x r6=%08x rp=%08x\n",
                             frn_ic, pc, r[4], r[5], r[6], env->rp);
        } else if (frn_ft_active) {
            if (frn_ft_fullregs)
                fprintf(frn_ft_fp, "%ld PC=0x%08x r0=%08x r1=%08x r2=%08x r3=%08x r4=%08x r5=%08x r6=%08x r7=%08x r8=%08x r9=%08x r10=%08x r11=%08x r12=%08x r13=%08x r14=%08x r15=%08x\n",
                        frn_ic, pc, r[0],r[1],r[2],r[3],r[4],r[5],r[6],r[7],r[8],r[9],r[10],r[11],r[12],r[13],r[14],r[15]);
            else
                fprintf(frn_ft_fp, "%ld PC=0x%08x r4=%08x r5=%08x r8=%08x r13=%08x\n",
                        frn_ic, pc, r[4], r[5], r[8], r[13]);
        }
    }
    /* FRN_LOG_USER: holistic handover map — log every transition of the live S-flag
     * (env->sf): 0->1 = entry to USER mode (userland handover), 1->0 = back to system.
     * If sf never becomes 1, the kernel never hands any task to userland (the root). */
    { static int lu = -1; if (lu < 0) lu = getenv("FRN_LOG_USER") ? 1 : 0;
      if (lu) { static int prev = -1; static int n = 0;
        int cur = (int)(env->sf & 1);
        if (cur != prev) {
            if (n++ < 60) fprintf(frn_tr_out?frn_tr_out:stderr,
                "[user] sf %d->%d at pc=0x%08x curtask=0x%08x\n", prev<0?0:prev, cur, pc,
                cpu_ldl_be_data(env, 0x6a003758u));
            prev = cur;
        }
      } }
    /* FRN_LOG_FLG: log the eventflag id (low16 of *(r4)) at wai_flg/set_flg/clr_flg entry,
     * to discover the REAL ids the firmware waits/sets (e.g. what task23 blocks on). */
    { static int lf = -1; if (lf < 0) lf = getenv("FRN_LOG_FLG") ? 1 : 0;
      /* Kernel semaphore services: twai_sem 0x100113dc (r4 = id, r5 = timeout) and
       * sig_sem 0x10010b38 (r4 = id); rp is the wrapper's caller chain entry. */
      if (lf && (pc == 0x100113dcu || pc == 0x10010b38u))
        fprintf(frn_tr_out ? frn_tr_out : stderr, "[sem] %s id=0x%04x tmo=%d rp~0x%08x\n",
                pc == 0x100113dcu ? "twai" : "sig ", r[4] & 0xffff, pc == 0x100113dcu ? (int)r[5] : 0, env->rp);
      /* Mailbox wrappers: mbx_send_message 0x10459864 (r4 = mailbox object, *r4 low16 = id,
       * r5 = 32-bit message word, r6 = 16-bit tag in its low half) and mbx_receive_message
       * 0x104598e8 (r4 = mailbox object). */
      if (lf && (pc == 0x10459864u || pc == 0x104598e8u)) {
        uint32_t idp = r[4], idw = 0;
        if ((idp >= 0x80000000u && idp < 0x84000000u) || (idp >= 0x6a000000u && idp < 0x6a100000u))
            idw = cpu_ldl_be_data(env, idp);
        if (pc == 0x10459864u)
            fprintf(frn_tr_out ? frn_tr_out : stderr, "[mbx] send id=0x%04x (obj=0x%08x) msg=0x%08x tag=0x%04x from rp~0x%08x\n",
                    (idw >> 16) & 0xffff, idp, r[5], r[6] & 0xffff, env->rp);
        else
            fprintf(frn_tr_out ? frn_tr_out : stderr, "[mbx] recv id=0x%04x (obj=0x%08x) from rp~0x%08x\n",
                    (idw >> 16) & 0xffff, idp, env->rp);
      }
      /* Kernel twai_flg service itself (0x100112a4: r4=flgid, r5=waiptn, r6=wfmode,
       * r7=p_flgptn, timeout on the stack): catches waits that bypass the wrappers. */
      if (lf && pc == 0x100112a4u)
        fprintf(frn_tr_out ? frn_tr_out : stderr,
            "[flg] twai_flg_svc id=0x%04x pat=0x%08x mode=%u tmo=%d from rp~0x%08x\n",
            r[4] & 0xffff, r[5], r[6], (int)cpu_ldl_be_data(env, r[15]), env->rp);
      if (lf && (pc == 0x10459708u || pc == 0x104596ccu || pc == 0x104596e6u)) {
        uint32_t idp = r[4]; uint32_t idw = 0;
        if (idp >= 0x80000000u && idp < 0x84000000u) idw = cpu_ldl_be_data(env, idp);
        else if (idp >= 0x6a000000u && idp < 0x6a100000u) idw = cpu_ldl_be_data(env, idp);
        const char *nm = pc==0x10459708u?"wai_flg":(pc==0x104596ccu?"set_flg":"clr_flg");
        fprintf(frn_tr_out ? frn_tr_out : stderr,
            "[flg] %s id=0x%04x (idptr=0x%08x word=0x%08x) pat=0x%08x from rp~0x%08x\n",
            nm, idw & 0xffff, idp, idw, r[5], env->rp);
      } }
    /* FRN_LOG_GATE: log the scheduler-start gate inputs each time rtos_can_dispatch
     * (0x1000e758) or rtos_sched_start_gate (0x1000d208) runs, to see whether the gate
     * ever passes (ret 0) and which term fails. FR is big-endian. */
    { static int lg = -1; if (lg < 0) lg = getenv("FRN_LOG_GATE") ? 1 : 0;
      if (lg && (pc == 0x1000e758u || pc == 0x1000d208u)) {
        static int n;
        if (n++ < 400) {
            uint32_t ctxp = cpu_ldl_be_data(env, 0x6a003774u);
            uint8_t d4d = 0, d4f = 0;
            if (ctxp >= 0x6a000000u && ctxp < 0x6a100000u) {
                d4d = cpu_ldub_data(env, ctxp + 0x4d);
                d4f = cpu_ldub_data(env, ctxp + 0x4f);
            } else if (ctxp >= 0x80000000u && ctxp < 0x90000000u) {
                d4d = cpu_ldub_data(env, ctxp + 0x4d);
                d4f = cpu_ldub_data(env, ctxp + 0x4f);
            }
            uint8_t aa8 = cpu_ldub_data(env, 0x6a003aa8u);
            int d3a2 = (d4d == 0x1f && (d4f & 0x30) == 0x30) ? 0 : 1;
            int gate = (d3a2 != 0 || aa8 != 0) ? 1 : 0;
            fprintf(frn_tr_out ? frn_tr_out : stderr,
                "[gate] %s ctx=0x%08x +0x4d=0x%02x +0x4f=0x%02x aa8=0x%02x d3a2=%d gate=%d %s from rp~0x%08x\n",
                pc==0x1000e758u?"can_dispatch":"sched_start", ctxp, d4d, d4f, aa8, d3a2, gate,
                gate? "IDLE":"SCHEDULE", env->rp);
        }
      } }
    /* FRN_SET38=1: at the task frame-builder FUN_1000d3fe(entry=r4, sp=r5), set the
     * task's TCB+0x38 (resume fn, which cre_tsk never sets) = its ENTRY (r4), so the
     * dispatcher chain-walk resumes the sub-task into its body (first-run dispatch)
     * instead of calling NULL. Finds id by matching sp against SP-array 0x6a0018c0.
     * Skips id6 (garbage SP). Build: faithful first-run resume for sub-tasks. */
    { static int s38 = -1; if (s38 < 0) s38 = getenv("FRN_SET38") ? 1 : 0;
      if (s38 && pc == 0x1000d3feu) {
        uint32_t entry = r[4], sp = r[5];
        for (uint32_t id = 0; id < 34; id++) {
            if (id == 6) continue;
            uint32_t slot = cpu_ldl_be_data(env, 0x6a0018c0u + id * 4);
            if (slot == sp && sp >= 0x6a000000u) {
                uint32_t tcb38 = 0x6a001be8u + id * 0x44u + 0x38u;
                cpu_stl_be_data(env, tcb38, entry);
                static int nn; if (nn++ < 40) fprintf(frn_tr_out?frn_tr_out:stderr,
                    "[set38] task%u TCB+0x38 <- entry 0x%08x (sp 0x%08x)\n", id, entry, sp);
                break;
            }
        }
      } }
    /* FRN_LOG_TEXT: dump the string drawn by glyph_draw FUN_10492fde (r5 = char*),
     * to capture the ACTUAL menu text the firmware renders (e.g. "Date Adjust"),
     * independent of whether the pixel composite reaches a scanout surface. */
    { static int lt = -1; if (lt < 0) lt = getenv("FRN_LOG_TEXT") ? 1 : 0;
      if (lt && pc == 0x10492fdeu) {
        static int n;
        if (n++ < 300) {
            uint32_t sp = r[5]; char s[80]; int k = 0;
            if (sp >= 0x10000000u && sp < 0x90000000u) {
                for (; k < 79; k++) { uint8_t c = cpu_ldub_data(env, sp + k); if (!c) break;
                    s[k] = (c >= 0x20 && c < 0x7f) ? (char)c : '.'; }
            }
            s[k] = 0;
            if (k > 0) fprintf(frn_tr_out ? frn_tr_out : stderr,
                "[text] glyph_draw r4=0x%08x str@0x%08x = \"%s\"\n", r[4], sp, s);
        }
      } }
    /* FRN_LOG_DRAW: count the natural-boot render-path milestones to find where the
     * app-main-synchronous draw bails. r4 = first arg (the screen-mgr obj). */
    { static int ld = -1; if (ld < 0) ld = getenv("FRN_LOG_DRAW") ? 1 : 0;
      if (ld) {
        static long c_disp, c_vis, c_mark, c_draw; static int shown;
        if (pc == 0x10467a3eu) c_disp++;
        else if (pc == 0x10448a08u) {
            c_vis++;
            uint32_t mgr = r[4]; uint8_t dc = 0;
            if (mgr >= 0x80000000u && mgr < 0x90000000u) dc = cpu_ldub_data(env, mgr + 0xdc);
            if (c_vis <= 12) fprintf(frn_tr_out?frn_tr_out:stderr,
                "[draw] vis_gate mgr=0x%08x +0xdc=0x%02x (0=>can-mark)\n", mgr, dc);
        }
        else if (pc == 0x1044b346u) c_mark++;
        else if (pc == 0x10481298u) c_draw++;
        if (pc == 0x10491510u && !shown) { shown = 1;   /* reached idle: dump the tally */
            fprintf(frn_tr_out?frn_tr_out:stderr,
                "[draw] TALLY at idle: rear_draw_dispatch=%ld vis_gate=%ld mark_visible=%ld draw_substep=%ld\n",
                c_disp, c_vis, c_mark, c_draw);
        }
      } }
    /* FRN_DUMP_CMDH: at cpucom cmd_handler 0x10430554, dump the transaction struct
     * at r9 (fields per error_print: +0=OutCode,+4=InCmd,+8=InSize,+0xc=OutCmd,
     * +0x10=OutSize) so a PASSING txn (code 0x10003) can be compared to the failing
     * Cmd:04 - revealing exactly which field the black-box DSP must supply. */
    if (pc == 0x10430554u && getenv("FRN_DUMP_CMDH")) {
        uint32_t s = env->regs[9];
        fprintf(frn_tr_out ? frn_tr_out : stderr,
            "[cmdh] r5(code)=0x%08x r9=0x%08x  struct: OutCode=0x%08x InCmd=0x%02x InSize=0x%08x OutCmd=0x%02x OutSize=0x%08x\n",
            env->regs[5], s, cpu_ldl_be_data(env, s), cpu_ldub_data(env, s+4),
            cpu_ldl_be_data(env, s+8), cpu_ldub_data(env, s+0xc), cpu_ldl_be_data(env, s+0x10));
    }
    /* FRN_DUMP_SPI: at cpucom_spi_xfer 0x10465958 entry, dump the LIVE txn (r4) flag
     * objects so the exact completion-flag memory bit (addr+mask) is known. flag obj
     * layout: +0x10 = byte* to the flag memory, +0x1c = mask byte. */
    if (pc == 0x10465958u && getenv("FRN_DUMP_SPI")) {
        uint32_t t = env->regs[4];
        uint32_t fa = cpu_ldl_be_data(env, t+0x10), fb = cpu_ldl_be_data(env, t+0x14);
        fprintf(frn_tr_out ? frn_tr_out : stderr,
            "[spixfer] txn=0x%08x flagA(+0x10)=0x%08x[addr=0x%08x mask=0x%02x] flagB(+0x14)=0x%08x[addr=0x%08x mask=0x%02x] ch=0x%08x\n",
            t, fa, fa?cpu_ldl_be_data(env,fa+0x10):0, fa?cpu_ldub_data(env,fa+0x1c):0,
            fb, fb?cpu_ldl_be_data(env,fb+0x10):0, fb?cpu_ldub_data(env,fb+0x1c):0,
            cpu_ldl_be_data(env, t+0xc));
    }
    /* FRN_DUMP_FLAG: at the per-byte DSP-ready waiter FUN_10465f24 (0x10465f24),
     * dump the flag object it polls (*(txn+0x14)): active(+0x10c), byte-addr(+0x10),
     * mask(+0x1c), and the live byte value - so the handshake flag is known exactly. */
    if (pc == 0x10465f24u && getenv("FRN_DUMP_FLAG")) {
        uint32_t t = env->regs[4];
        uint32_t fb = cpu_ldl_be_data(env, t+0x14);
        uint32_t active = fb?cpu_ldl_be_data(env, fb+0x10c):0;
        uint32_t ba = fb?cpu_ldl_be_data(env, fb+0x10):0;
        uint32_t mask = fb?cpu_ldub_data(env, fb+0x1c):0;
        uint32_t val = ba?cpu_ldub_data(env, ba):0;
        fprintf(frn_tr_out ? frn_tr_out : stderr,
            "[flag] txn=0x%08x flagB=0x%08x active(+0x10c)=0x%08x byteaddr(+0x10)=0x%08x mask=0x%02x val@addr=0x%02x\n",
            t, fb, active, ba, mask, val);
    }
    /* FRN_DUMP_TF: at test_flag_clear/set (0x104398ac/0x104398c0), log the EXACT
     * dereference the firmware does - obj(r4), the byte-pointer *(obj+0x10), the
     * mask *(obj+0x1c), and the live byte - so the handshake flag's real binding is
     * ground-truth (no hand offset math). */
    /* FRN_DUMP_DEV2: at dev2 ready-poll FUN_1043fd24 (0x1043fd24), log its status-reg
     * addr *(obj+0x1c), the live byte, and data-reg addr *(obj+0x34) - the device the
     * firmware spins on after CPUCOM POST (looks like a settings EEPROM: cmd 0xe0/0x65 + 16B read). */
    if (pc == 0x1043fd24u && getenv("FRN_DUMP_DEV2")) {
        static int n; if (n++ < 6) { uint32_t o = env->regs[4];
            uint32_t sa = cpu_ldl_be_data(env, o+0x1c), da = cpu_ldl_be_data(env, o+0x34);
            fprintf(frn_tr_out ? frn_tr_out : stderr,
                "[dev2] obj=0x%08x statusreg=0x%08x byte=0x%02x datareg=0x%08x\n",
                o, sa, (sa>=0x40&&sa<0x90000000u)?cpu_ldub_data(env,sa):0xff, da); }
    }
    /* FRN_DUMP_FLG: log set_flag(0x1043986a)/clear_flag(0x10439822) that target
     * 0x50000106 - the main's req bit (addr+mask), to pair with the poller's ack bit. */
    if ((pc == 0x1043986au || pc == 0x10439822u) && getenv("FRN_DUMP_FLG")) {
        uint32_t o = env->regs[4];
        uint32_t ad = cpu_ldl_be_data(env, o+0x10), mk = cpu_ldub_data(env, o+0x1c);
        if (ad == 0x50000106u) { static int n; if (n++ < 20)
            fprintf(frn_tr_out ? frn_tr_out : stderr, "[flg] %s addr=0x%08x mask=0x%02x\n",
                pc==0x1043986au?"SET  ":"CLEAR", ad, mk); }
    }
    if ((pc == 0x104398acu || pc == 0x104398c0u) && getenv("FRN_DUMP_TF")) {
        static int nn; if (nn++ < 60) {
            uint32_t o = env->regs[4];
            uint32_t bp = cpu_ldl_be_data(env, o+0x10);
            uint32_t mask = cpu_ldub_data(env, o+0x1c);
            uint32_t val = (bp>=0x40 && bp<0x90000000u) ? cpu_ldub_data(env, bp) : 0xdead;
            fprintf(frn_tr_out ? frn_tr_out : stderr,
                "[tf] %s obj=0x%08x byteptr=0x%08x mask=0x%02x byte=0x%02x -> %s\n",
                pc==0x104398c0u?"SET ":"CLR ", o, bp, mask, val,
                (val!=0xdead && (val&mask))?"bit-SET":"bit-clear");
        }
    }
    if (frn_tr_watch_n && frn_tr_watched(pc)) {
        static long minr6 = -1;
        if (minr6 < 0) {
            const char *m = getenv("FRN_TRACE_MINR6");
            minr6 = m ? atol(m) : 0;
        }
        static long maxhits = -1, hits;
        if (maxhits < 0) {
            const char *m = getenv("FRN_TRACE_MAXHITS");
            maxhits = m ? atol(m) : 0;   /* 0 = unlimited */
        }
        if ((long)r[6] >= minr6 && (maxhits == 0 || hits < maxhits)) {
            hits++;
            fprintf(frn_tr_out, "[call] 0x%08x  r4=0x%08x r5=0x%08x r6=0x%08x "
                    "r7=0x%08x r8=0x%08x r9=0x%08x r13=0x%08x r14=0x%08x  rp=0x%08x sp=0x%08x\n",
                    pc, r[4], r[5], r[6], r[7], r[8], r[9], r[13], r[14], env->rp, r[15]);
            /* walk the stack for firmware-range return addresses = call chain */
            fprintf(frn_tr_out, "       stack:");
            for (int k = 0; k < 96; k++) {
                uint32_t sv = cpu_ldl_be_data(env, r[15] + k * 4);
                if (sv >= FW_BASE && sv < FW_END) {
                    fprintf(frn_tr_out, " 0x%08x", sv);
                }
            }
            fprintf(frn_tr_out, "\n");
        }
    }
    uint32_t w = frn_host(pc, 2) ? frn_ld16(env, pc) : rd16(env, pc);   /* fetch: RAM fast path */
    uint32_t pending = env->delay_armed ? env->delay_pc : 0xffffffffu;
    int had_pending = env->delay_armed;
    env->delay_armed = 0;

    uint32_t hi8 = (w >> 8) & 0xff;
    uint32_t hi4 = (w >> 12) & 0xf;
    uint32_t t12 = (w >> 4) & 0xfff;
    int ri = w & 0xf;
    int rj = (w >> 4) & 0xf;
    uint32_t xc = (w >> 4) & 0xf;
    uint32_t td = w & 0xff;
    uint32_t op = hi8;

    env->pc = pc + 2;   /* default advance; overridden by transfers */

    /* FRN_ICALL_LO/HI=hex: log indirect calls (op 0x97 = call @r[ri]) over a PC
     * window, flagging targets that are null/garbage/non-ROM — a broken vtable
     * dispatch (object field uninitialized in the emulator) is the likely gate. */
    if (op == 0x97) {
        static int ic=0; static uint32_t lo=0,hi=0;
        if (!ic){ic=1; const char*l=getenv("FRN_ICALL_LO");const char*h=getenv("FRN_ICALL_HI");
            if(l)lo=(uint32_t)strtoul(l,NULL,16); if(h)hi=(uint32_t)strtoul(h,NULL,16);}
        if (lo && pc>=lo && pc<hi){
            uint32_t tgt=env->regs[ri];
            int bad = !(tgt>=0x10000000u && tgt<0x10600000u);
            fprintf(frn_tr_out?frn_tr_out:stderr,"[icall] pc=%08x call @r%d=%08x%s\n",
                    pc,ri,tgt, bad?"  <<BAD TARGET":"");
        }
    }

    /* FRN_DISAS_LO/HI=hex: per-instruction trace over a PC window — the real
     * interpreter narrating its own opcode stream, so I can read a function's
     * logic (e.g. act_tsk's bail) without a separate (fallible) disassembler. */
    {
        static int di = 0; static uint32_t dlo = 0, dhi = 0;
        if (!di) { di = 1; const char *l = getenv("FRN_DISAS_LO"); const char *h = getenv("FRN_DISAS_HI");
            if (l) dlo = (uint32_t)strtoul(l, NULL, 16); if (h) dhi = (uint32_t)strtoul(h, NULL, 16); }
        if (dlo && pc >= dlo && pc < dhi) {
            fprintf(frn_tr_out ? frn_tr_out : stderr,
                "[dis] pc=%08x w=%04x op=%02x ri=%x(%08x) rj=%x(%08x) td=%02x\n",
                pc, w, op, ri, env->regs[ri], rj, env->regs[rj], td);
        }
    }

    do {
    /* ---- full-word opcodes ---- */
    if (w == 0x9720) { env->pc = env->rp; break; }                 /* ret */
    if (w == 0x9F20) { go(env, env->rp, 1); break; }               /* ret:D */
    if (w == 0x9730) {                                             /* reti */
        uint32_t ptr = rd32(env, r[15]); r[15] += 4;
        uint32_t ps = rd32(env, r[15]); r[15] += 4;
        unpack_ps(env, ps); env->pc = ptr; break;
    }
    if (w == 0x9FA0) { break; }                                    /* nop */
    if (w == 0x9F90) { r[15] = r[14] + 4; r[14] = rd32(env, r[15] - 4); break; } /* leave */
    if (w == 0x0790) { unpack_ps(env, rd32(env, r[15])); r[15] += 4; break; }    /* ld @r15+,ps */
    if (w == 0x1790) { push32(env, pack_ps(env)); break; }         /* st ps,@-r15 */
    if (w == 0x9F60 || w == 0x9F70 || w == 0x9F30) { break; }      /* div3/div4s/u_inte nop */

    /* ---- 12-bit opcodes ---- */
    if (t12 == 0x9F8) { r[ri] = rd32(env, pc + 2); env->pc = pc + 6; break; }    /* ldi:32 */
    if (hi8 == 0x9B) { uint32_t xl = rd16(env, pc + 2); r[ri] = ((xc << 16) | xl) & 0xfffff; env->pc = pc + 4; break; } /* ldi:20 */
    if (t12 == 0x970) { env->pc = r[ri]; break; }                  /* jmp @ri */
    if (t12 == 0x9F0) { go(env, r[ri], 1); break; }                /* jmp:D @ri */
    if (t12 == 0x971) {
        if (pc >= 0x10439674 && pc <= 0x104396d0) {
            static uint32_t _vs[16]; static int _vn;
            int f = 0; for (int k = 0; k < _vn; k++) if (_vs[k] == r[ri]) f = 1;
            if (frn_tr_irq && !f && _vn < 16) { _vs[_vn++] = r[ri];
                fprintf(frn_tr_out ? frn_tr_out : stderr, "[task1-vtable] pc=%08x -> method=%08x (obj r4=%08x)\n", pc, r[ri], r[4]); }
        }
        do_call(env, frn_steer_call(pc, r[ri]), pc + 2, 0); break;
    }   /* call @ri */
    if (t12 == 0x9F1) { do_call(env, frn_steer_call(pc, r[ri]), pc + 4, 1); break; }   /* call:D @ri */
    if (t12 == 0x070) { r[ri] = rd32(env, r[15]); if (ri != 15) r[15] += 4; break; } /* ld @r15+,ri */
    if (t12 == 0x078) { set_sr(env, ri, rd32(env, r[15])); r[15] += 4; break; }  /* ld @r15+,Rs */
    if (t12 == 0x170) { push32(env, r[ri]); break; }               /* st ri,@-r15 */
    if (t12 == 0x178) { push32(env, get_sr(env, ri)); break; }     /* st Rs,@-r15 */
    if (t12 == 0x171) { r[ri] = pack_ps(env); break; }             /* mov ps,ri */
    if (t12 == 0x071) { unpack_ps(env, r[ri]); break; }            /* mov ri,ps */
    if (t12 == 0x974) { int32_t num = s32(env->mdl), d = s32(r[ri]); if (d) { env->mdl = num / d; env->mdh = num % d; } break; } /* div0s */
    if (t12 == 0x975) { uint32_t num = env->mdl, d = r[ri]; if (d) { env->mdl = num / d; env->mdh = num % d; } break; } /* div0u */
    if (t12 == 0x976 || t12 == 0x977) { break; }                   /* div1/div2 nop */
    if (t12 == 0x978) { r[ri] = sext(r[ri], 8); break; }           /* extsb */
    if (t12 == 0x979) { r[ri] = r[ri] & 0xff; break; }             /* extub */
    if (t12 == 0x97A) { r[ri] = sext(r[ri], 16); break; }          /* extsh */
    if (t12 == 0x97B) { r[ri] = r[ri] & 0xffff; break; }           /* extuh */
    if (t12 == 0x97C) { int i; uint32_t v = r[ri]; r[ri] = 32; for (i = 0; i < 32; i++) if (!(v & (0x80000000u >> i))) { r[ri] = i; break; } break; } /* srch0 */
    if (t12 == 0x97D) { int i; uint32_t v = r[ri]; r[ri] = 32; for (i = 0; i < 32; i++) if (v & (0x80000000u >> i)) { r[ri] = i; break; } break; }  /* srch1 */

    /* ---- branch family (hi4 E/F) ---- */
    if (hi4 == 0xE || hi4 == 0xF) {
        int op_b = (w >> 8) & 0xf;
        int32_t disp = (td & 0x80) ? (int32_t)td - 0x100 : (int32_t)td;
        uint32_t target = pc + 2 + disp * 2;
        int take = op_b == 0 || (op_b != 1 && cond(env, op_b));
        if (op_b >= 2) { frn_steer_branch(pc, take, &take); fb_record(pc, target, take); }
        if (take) {
            if (hi4 == 0xE) env->pc = target;
            else go(env, target, 1);
        }
        break;
    }

    /* ---- arithmetic (hi8) ---- */
    if (op == 0xA6) { uint32_t a = r[ri], b = r[rj]; env->cc_c = carry32(a, b); env->cc_v = scarry32(a, b); r[ri] = a + b; resflags(env, r[ri], 32); break; }
    if (op == 0xA4) { uint32_t a = r[ri]; env->cc_c = carry32(a, xc); env->cc_v = scarry32(a, xc); r[ri] = a + xc; resflags(env, r[ri], 32); break; }
    if (op == 0xA5) { uint32_t nx = (uint32_t)(-16 + (int)xc); uint32_t a = r[ri]; env->cc_c = carry32(a, nx); env->cc_v = scarry32(a, nx); r[ri] = a + nx; resflags(env, r[ri], 32); break; }
    if (op == 0xA7) { r[ri] = addc_op(env, r[ri], r[rj]); resflags(env, r[ri], 32); break; }
    if (op == 0xA2) { r[ri] = r[ri] + r[rj]; break; }
    if (op == 0xA0) { r[ri] = r[ri] + xc; break; }
    if (op == 0xA1) { r[ri] = r[ri] + (uint32_t)(-16 + (int)xc); break; }
    if (op == 0xAC) { uint32_t a = r[ri], b = r[rj]; env->cc_c = (a < b); env->cc_v = sborrow32(a, b); r[ri] = a - b; resflags(env, r[ri], 32); break; }
    if (op == 0xAD) { r[ri] = subc_op(env, r[ri], r[rj]); resflags(env, r[ri], 32); break; }
    if (op == 0xAE) { r[ri] = r[ri] - r[rj]; break; }
    if (op == 0xAA) { uint32_t a = r[ri], b = r[rj]; env->cc_c = (a < b); env->cc_v = sborrow32(a, b); resflags(env, a - b, 32); break; }
    if (op == 0xA8) { uint32_t a = r[ri]; env->cc_c = (a < xc); env->cc_v = sborrow32(a, xc); resflags(env, a - xc, 32); break; }
    if (op == 0xA9) { uint32_t nx = (uint32_t)(-16 + (int)xc), a = r[ri]; env->cc_c = (a < nx); env->cc_v = sborrow32(a, nx); resflags(env, a - nx, 32); break; }

    /* ---- logic ---- */
    if (op == 0x82) { r[ri] = r[ri] & r[rj]; resflags(env, r[ri], 32); break; }
    if (op == 0x84) { uint32_t v = rd32(env, r[ri]) & r[rj]; wr32(env, r[ri], v); resflags(env, v, 32); break; }
    if (op == 0x85) { uint32_t v = (rd16(env, r[ri]) & r[rj]) & 0xffff; wr16(env, r[ri], v); resflags(env, v, 16); break; }
    if (op == 0x86) { uint32_t v = (rd8(env, r[ri]) & r[rj]) & 0xff; wr8(env, r[ri], v); resflags(env, v, 8); break; }
    if (op == 0x92) { r[ri] = r[ri] | r[rj]; resflags(env, r[ri], 32); break; }
    if (op == 0x94) { uint32_t v = rd32(env, r[ri]) | r[rj]; wr32(env, r[ri], v); resflags(env, v, 32); break; }
    if (op == 0x95) { uint32_t v = (rd16(env, r[ri]) | r[rj]) & 0xffff; wr16(env, r[ri], v); resflags(env, v, 16); break; }
    if (op == 0x96) { uint32_t v = (rd8(env, r[ri]) | r[rj]) & 0xff; wr8(env, r[ri], v); resflags(env, v, 8); break; }
    if (op == 0x9A) { r[ri] = r[ri] ^ r[rj]; resflags(env, r[ri], 32); break; }
    if (op == 0x9C) { uint32_t v = rd32(env, r[ri]) ^ r[rj]; wr32(env, r[ri], v); resflags(env, v, 32); break; }
    if (op == 0x9D) { uint32_t v = (rd16(env, r[ri]) ^ r[rj]) & 0xffff; wr16(env, r[ri], v); resflags(env, v, 16); break; }
    if (op == 0x9E) { uint32_t v = (rd8(env, r[ri]) ^ r[rj]) & 0xff; wr8(env, r[ri], v); resflags(env, v, 8); break; }

    /* ---- bit ops on memory ---- */
    if (op == 0x80) { uint32_t t = rd8(env, r[ri]); wr8(env, r[ri], t & (xc + 0xf0)); break; }
    if (op == 0x81) { uint32_t t = rd8(env, r[ri]); wr8(env, r[ri], t & ((xc << 4) + 0x0f)); break; }
    if (op == 0x90) { uint32_t t = rd8(env, r[ri]); wr8(env, r[ri], t | (xc & 0x0f)); break; }
    if (op == 0x91) { uint32_t t = rd8(env, r[ri]); wr8(env, r[ri], t | ((xc << 4) & 0xf0)); break; }
    if (op == 0x98) { uint32_t t = rd8(env, r[ri]); wr8(env, r[ri], (xc ^ t) & 0xff); break; }
    if (op == 0x99) { uint32_t t = rd8(env, r[ri]); wr8(env, r[ri], ((xc << 4) ^ t) & 0xff); break; }
    if (op == 0x88) { uint32_t t = rd8(env, r[ri]); resflags(env, (xc & t) & 0x0f, 8); break; }
    if (op == 0x89) { uint32_t t = rd8(env, r[ri]); resflags(env, ((xc << 4) & t) & 0xffff, 16); break; }

    /* ---- mul ---- */
    if (op == 0xAF) { int64_t res = (int64_t)s32(r[ri]) * (int64_t)s32(r[rj]); uint64_t u = (uint64_t)res; resflags(env, u, 64); env->mdl = u & M32; env->mdh = (u >> 32) & M32; env->cc_v = (env->mdh != 0 && env->mdh != M32); break; }
    if (op == 0xAB) { uint64_t res = (uint64_t)r[ri] * (uint64_t)r[rj]; resflags(env, res, 64); env->mdl = res & M32; env->mdh = (res >> 32) & M32; env->cc_v = (env->mdh != 0); break; }
    if (op == 0xBF) { uint32_t res = (uint32_t)(sext(r[ri], 16) * sext(r[rj], 16)); resflags(env, res, 32); env->mdl = res; break; }
    if (op == 0xBB) { uint32_t res = (r[ri] & 0xffff) * (r[rj] & 0xffff); resflags(env, res, 32); env->mdl = res; break; }

    /* ---- shifts ---- */
    if (op == 0xB6) { int sh = r[rj] & 0xf; env->cc_c = (((uint64_t)0x100000000ULL >> sh) & r[ri]) != 0; r[ri] = (sh >= 32) ? 0 : (r[ri] << sh); resflags(env, r[ri], 32); break; }
    if (op == 0xB4) { int sh = xc; env->cc_c = (((uint64_t)0x100000000ULL >> sh) & r[ri]) != 0; r[ri] = (sh >= 32) ? 0 : (r[ri] << sh); resflags(env, r[ri], 32); break; }
    if (op == 0xB5) { int sh = xc + 16; env->cc_c = (((uint64_t)0x100000000ULL >> sh) & r[ri]) != 0; r[ri] = (sh >= 32) ? 0 : (r[ri] << sh); resflags(env, r[ri], 32); break; }
    if (op == 0xB2) { r[ri] = lsr_op(env, r[ri], r[rj] & 0x1f); break; }
    if (op == 0xB0) { r[ri] = lsr_op(env, r[ri], xc & 0x1f); break; }
    if (op == 0xB1) { r[ri] = lsr_op(env, r[ri], (xc + 16) & 0x1f); break; }
    if (op == 0xBA) { r[ri] = asr_op(env, r[ri], r[rj] & 0x1f); break; }
    if (op == 0xB8) { r[ri] = asr_op(env, r[ri], xc & 0x1f); break; }
    if (op == 0xB9) { r[ri] = asr_op(env, r[ri], (xc + 16) & 0x1f); break; }

    /* ---- ldi:8 ---- */
    if (hi4 == 0xC) { r[ri] = (w >> 4) & 0xff; break; }

    /* ---- loads ---- */
    if (op == 0x04) { r[ri] = rd32(env, r[rj]); break; }
    if (op == 0x00) { r[ri] = rd32(env, r[13] + r[rj]); break; }
    if (hi4 == 0x2) { r[ri] = rd32(env, r[14] + sx8((w >> 4) & 0xff) * 4); break; }
    if (op == 0x03) { r[ri] = rd32(env, r[15] + xc * 4); break; }
    if (op == 0x05) { r[ri] = rd16(env, r[rj]) & 0xffff; break; }
    if (op == 0x01) { r[ri] = rd16(env, r[13] + r[rj]) & 0xffff; break; }
    if (hi4 == 0x4) { r[ri] = rd16(env, r[14] + sx8((w >> 4) & 0xff) * 2) & 0xffff; break; }
    if (op == 0x06) { r[ri] = rd8(env, r[rj]) & 0xff; break; }
    if (op == 0x02) { r[ri] = rd8(env, r[13] + r[rj]) & 0xff; break; }
    if (hi4 == 0x6) { r[ri] = rd8(env, r[14] + sx8((w >> 4) & 0xff)) & 0xff; break; }

    /* ---- stores ---- */
    if (op == 0x14) { wr32(env, r[rj], r[ri]); break; }
    if (op == 0x10) { wr32(env, r[13] + r[rj], r[ri]); break; }
    if (hi4 == 0x3) { wr32(env, r[14] + sx8((w >> 4) & 0xff) * 4, r[ri]); break; }
    if (op == 0x13) { wr32(env, r[15] + xc * 4, r[ri]); break; }
    if (op == 0x15) { wr16(env, r[rj], r[ri]); break; }
    if (op == 0x11) { wr16(env, r[13] + r[rj], r[ri]); break; }
    if (hi4 == 0x5) { wr16(env, r[14] + sx8((w >> 4) & 0xff) * 2, r[ri]); break; }
    if (op == 0x16) { wr8(env, r[rj], r[ri]); break; }
    if (op == 0x12) { wr8(env, r[13] + r[rj], r[ri]); break; }
    if (hi4 == 0x7) { wr8(env, r[14] + sx8((w >> 4) & 0xff), r[ri]); break; }

    /* ---- moves ---- */
    if (op == 0x8B) { r[ri] = r[rj]; break; }
    if (op == 0xB7) { r[ri] = get_sr(env, rj); break; }
    if (op == 0xB3) { set_sr(env, rj, r[ri]); break; }

    /* ---- call direct ---- */
    if ((w >> 11) == 0x1A) { int32_t d = w & 0x7ff; if (d & 0x400) d -= 0x800; do_call(env, pc + 2 + d * 2, pc + 2, 0); break; }
    if ((w >> 11) == 0x1B) { int32_t d = w & 0x7ff; if (d & 0x400) d -= 0x800; do_call(env, pc + 2 + d * 2, pc + 4, 1); break; }

    /* ---- int #u8 ---- */
    if (op == 0x1F) {
        if (td == 0x40) {   /* DEBUG: log distinct REALOS service routines (r12) */
            static uint32_t _seen[128]; static int _ns;
            uint32_t svc = env->regs[12];
            int f = 0;
            for (int k = 0; k < _ns; k++) if (_seen[k] == svc) { f = 1; break; }
            if (frn_tr_irq && !f && _ns < 128) {
                _seen[_ns++] = svc;
                fprintf(frn_tr_out ? frn_tr_out : stderr, "[int40] service r12=%08x  r4=%08x r5=%08x  pc=%08x  vec=%08x\n",
                        svc, env->regs[4], env->regs[5], pc, rd32(env, env->tbr + 0x3FC - (td * 4)));
            }
            /* FRN_INT40_SVC=hex (comma list): log EVERY call to those REALOS services
             * with full args r4-r7 + rp = map a specific transaction (e.g. CPUCOM
             * snd_dtq/rcv_dtq). FRN_INT40_SVC=all logs all. */
            static long _if_init; static uint32_t _if[16]; static int _ifn; static int _ifall;
            if (!_if_init) { _if_init = 1; const char *s = getenv("FRN_INT40_SVC");
                if (s && (!strcmp(s,"all")||!strcmp(s,"ALL"))) _ifall = 1;
                while (s && *s && !_ifall && _ifn < 16) { char *e2; unsigned long v = strtoul(s,&e2,16);
                    if (e2==s) break; _if[_ifn++] = (uint32_t)v; s = (*e2==',')?e2+1:e2; } }
            int hit = _ifall;
            for (int k = 0; k < _ifn && !hit; k++) if (_if[k] == svc) hit = 1;
            if (hit) fprintf(frn_tr_out ? frn_tr_out : stderr,
                "[int40*] r12=%08x r4=%08x r5=%08x r6=%08x r7=%08x  pc=%08x rp=%08x\n",
                svc, env->regs[4], env->regs[5], env->regs[6], env->regs[7], pc, env->rp);
        }
        /* FRN_CPUCOM_ACK=<code hex>: EXPERIMENT. The CPUCOM task blocks in
         * rcv_mbx(id=4, TMO_FEVR) forever (no DSP posts to mailbox 4). When that
         * exact call happens, synthesize a success message instead of letting the
         * kernel primitive block: write msg{+0=next,+4=cmd,+8=code} to scratch,
         * set *r5=msgptr and ercd(r4)=0, and skip the real primitive. Observe
         * whether the firmware then advances to producing menu content. Gated on
         * the forever-timeout so normal polling receives are untouched. */
        if (td == 0x40 && env->regs[12] == 0x100111b0u) {
            static long ck_init = 0; static uint32_t ck_code = 0; static int ck_mbx = 4;
            static long ck_max = 0, ck_n = 0;
            if (!ck_init) { ck_init = 1;
                const char *c = getenv("FRN_CPUCOM_ACK"); if (c) ck_code = (uint32_t)strtoul(c, NULL, 16);
                const char *m = getenv("FRN_CPUCOM_ACK_MBX"); if (m) ck_mbx = (int)strtol(m, NULL, 0);
                const char *x = getenv("FRN_CPUCOM_ACK_N"); ck_max = x ? strtol(x, NULL, 0) : 32; }
            if (ck_code && env->regs[4] == (uint32_t)ck_mbx &&
                env->regs[6] == 0xffffffffu && (ck_max == 0 || ck_n < ck_max)) {
                uint32_t msg = 0x8ff00200u + (uint32_t)((ck_n & 7) * 0x40);
                wr32(env, msg + 0, 0);            /* next ptr */
                wr32(env, msg + 4, 0x04);         /* cmd */
                /* code field at +8 is read byte-wise and reassembled LITTLE-endian
                 * by 0x104598e8, so store it byte-swapped vs the BE wr32. */
                wr32(env, msg + 8, __builtin_bswap32(ck_code));  /* response Code (LE) */
                wr32(env, msg + 0xc, 0);
                wr32(env, msg + 0x10, 0);
                wr32(env, env->regs[5], msg);     /* *param_2 = msgptr */
                env->regs[4] = 0;                 /* ercd = E_OK */
                if (frn_tr_irq || getenv("FRN_CPUCOM_ACK_LOG"))
                    fprintf(frn_tr_out ? frn_tr_out : stderr,
                        "[cpucom-ack #%ld] rcv_mbx(%d) -> synth msg 0x%08x code=0x%08x  pc=%08x\n",
                        ck_n, ck_mbx, msg, ck_code, pc);
                ck_n++;
                env->pc = pc + 2;                 /* skip the real primitive */
                break;
            }
        }
        uint32_t ea = env->tbr + 0x3FC - (td * 4);
        uint32_t vec = rd32(env, ea);
        if (vec >= FW_BASE && vec < FW_END) {
            uint32_t saved_ps = pack_ps(env);  /* FR: save pre-trap PS (user S=1) BEFORE entering system mode */
            set_sflag(env, 0);
            push32(env, saved_ps);
            push32(env, pc + 2);
            env->i_flag = 0;
            env->pc = vec;
        } else {
            set_sflag(env, 0);
            env->i_flag = 0;
        }
        break;
    }

    /* ---- dmov (implicit r13) ---- */
    if (op == 0x08) { r[13] = rd32(env, td * 4); break; }
    if (op == 0x18) { wr32(env, td * 4, r[13]); break; }
    if (op == 0x0C) { wr32(env, r[13], rd32(env, td * 4)); r[13] += 4; break; }
    if (op == 0x1C) { wr32(env, td * 4, rd32(env, r[13])); r[13] += 4; break; }
    if (op == 0x0B) { r[15] -= 4; wr32(env, r[15], rd32(env, td * 4)); break; }
    if (op == 0x1B) { wr32(env, td * 4, rd32(env, r[15])); r[15] += 4; break; }
    if (op == 0x09) { r[13] = rd16(env, td * 2); break; }
    if (op == 0x19) { wr16(env, td * 2, r[13]); break; }
    if (op == 0x0D) { wr16(env, r[13], rd16(env, td * 2)); r[13] += 2; break; }
    if (op == 0x1D) { wr16(env, td * 2, rd16(env, r[13])); r[13] += 2; break; }
    if (op == 0x0A) { r[13] = rd8(env, td); break; }
    if (op == 0x1A) { wr8(env, td, r[13]); break; }
    if (op == 0x0E) { wr8(env, r[13], rd8(env, td)); r[13] += 1; break; }
    if (op == 0x1E) { wr8(env, td, rd8(env, r[13])); r[13] += 1; break; }

    /* ---- misc ---- */
    if (op == 0x83) { unpack_ccr(env, pack_ccr(env) & td); break; }
    if (op == 0x93) { unpack_ccr(env, pack_ccr(env) | td); break; }
    if (op == 0x87) { env->ilm = td & 0x1f; break; }
    if (op == 0xA3) { r[15] = r[15] + sx8(td) * 4; break; }
    if (op == 0x8A) { uint32_t tmp = r[ri] & 0xff; r[ri] = rd8(env, r[rj]) & 0xff; wr8(env, r[rj], tmp); break; }

    /* ---- ldm/stm/enter ---- */
    if (op == 0x8C) { for (int reg = 0; reg < 8; reg++) if (td & (1 << reg)) { r[reg] = rd32(env, r[15]); r[15] += 4; } break; }
    if (op == 0x8D) { for (int reg = 8; reg < 16; reg++) if (td & (1 << (reg - 8))) { r[reg] = rd32(env, r[15]); r[15] += 4; } break; }
    if (op == 0x8E) { for (int reg = 7; reg >= 0; reg--) if (td & (1 << (7 - reg))) { r[15] -= 4; wr32(env, r[15], r[reg]); } break; }
    if (op == 0x8F) { for (int reg = 15; reg > 7; reg--) if (td & (1 << (15 - reg))) { r[15] -= 4; wr32(env, r[15], r[reg]); } break; }
    if (op == 0x0F) { uint32_t ea = r[15] - 4; wr32(env, ea, r[14]); r[14] = ea; r[15] = r[15] - td * 4; break; }

    /* ---- unknown: leave pc advanced by 2 (skeleton tolerance) ---- */
    { static int lu=-1; static long ucnt=0;
      if(lu<0) lu=getenv("FRN_LOG_UNK")?1:0;
      if(lu){ uint32_t uw=rd16(env,pc);
        /* only log in the kernel/scheduler/activation range to cut noise; set FRN_LOG_UNK=all for everything */
        static int all=-1; if(all<0) all=getenv("FRN_LOG_UNK_ALL")?1:0;
        if(all || (pc>=0x1000c000u && pc<=0x10012000u))
          if(ucnt++ < 2000)
            fprintf(frn_tr_out?frn_tr_out:stderr,"[unk] pc=%08x w=%04x\n", pc, uw); } }
    } while (0);

    if (had_pending) {
        env->pc = pending;
    }
}

/* QEMU entry: one translation block = one call, which interprets a batch of guest
 * instructions (FRN_BATCH, default 64; 1 = the old one-instruction-per-block behaviour).
 * Every instruction still runs all per-instruction hooks (timers, interrupt delivery,
 * traces); batching only removes QEMU's block dispatch between instructions, which cost
 * about as much as the interpretation itself. QEMU regains control after each batch. */
void HELPER(frn_interp)(CPUFRNState *env)
{
    static int batch = -1;
    if (batch < 0) { const char *b = getenv("FRN_BATCH"); batch = b ? atoi(b) : 64; if (batch < 1) batch = 1; }
    for (int i = 0; i < batch; i++) frn_interp_one(env);
}
