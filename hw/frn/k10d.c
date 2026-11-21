/*
 * Pentax K10D (Fujitsu Milbeaut MB91683 / FR60Lite) bare-metal board.
 * Minimal bring-up board for the K10D firmware (FWDC162B.BIN). Maps the ROM,
 * SDRAM and work RAM, loads the firmware with -bios, and enters at the known
 * K10D entry point. Peripherals (Milbeaut timer, the stateful 0x67000000 block,
 * LCD) are added incrementally; unmapped MMIO reads-as-zero via an unimplemented
 * catch region for bring-up.
 * SPDX-License-Identifier: LGPL-2.0-or-later
 */
#include "qemu/osdep.h"
#include "qemu/error-report.h"
#include "qapi/error.h"
#include "hw/core/boards.h"
#include "hw/core/loader.h"
#include "hw/core/qdev.h"
#include "hw/core/sysbus.h"
#include "system/address-spaces.h"
#include "system/memory.h"
#include "qemu/timer.h"
#include "cpu.h"
#include "k10d_display.h"
#include "k10d_sd.h"
uint8_t *k10d_host_lowram, *k10d_host_rom, *k10d_host_sdram, *k10d_host_wram;

/*
 * Background MMIO: everything that is not RAM/ROM reads as 0xffffffff and
 * ignores writes — matching fremu.py's mmio_default ("all ready bits set",
 * benign for status polls). Stateful peripherals (timer, 0x67000000 block,
 * LCD) are added later as higher-priority device regions over this.
 */
/* Unmapped-access trap (FRN_LOG_UNMAPPED): every access that falls through to the
 * background handler is to a region we have NOT modeled -- reads return what was
 * written there, else a default (all-ones or 0); see frn_bg_store below. Log each distinct address once, with the
 * firmware PC, so missing peripheral/RAM regions announce themselves instead of
 * silently misbehaving (Andrew d308). */
static inline uint32_t frn_cur_pc(void)
{
    return current_cpu ? FRN_CPU(current_cpu)->env.pc : 0;
}
static void frn_log_unmapped(const char *kind, uint32_t addr, uint32_t val, unsigned size)
{
    static int on = -1;
    if (on < 0) on = getenv("FRN_LOG_UNMAPPED") ? 1 : 0;
    if (!on) return;
    static uint32_t seen[2048]; static int ns, nlog;
    if (nlog > 16000) return;
    for (int i = 0; i < ns; i++) if (seen[i] == addr) return;   /* dedup by addr */
    if (ns < 2048) seen[ns++] = addr;
    /* tag: is it in the "all-ones default MMIO" window (partly expected) or truly dark? */
    int periph = (addr >= 0x40000000 && addr < 0x50000000) ||
                 (addr >= 0x67000000 && addr < 0x67001000);
    fprintf(stderr, "[UNMAPPED %s%s] 0x%08x = 0x%08x (sz%u) pc~0x%08x\n",
            kind, periph ? "/periph" : "/DARK", addr, val, size, frn_cur_pc());
    nlog++;
}

/* Read-your-writes for unmodelled addresses (Andrew: "the firmware should be able to
 * read its own writes ... or simply treated as ram"). Every byte the firmware writes to
 * an address no device model claims is kept in a sparse store and read back exactly;
 * bytes never written keep the old defaults (all-ones in the MMIO windows, 0 elsewhere).
 * First writes per address are still reported by FRN_LOG_UNMAPPED. FRN_BG_RAM=0 restores
 * the old drop-writes behaviour. */
static GHashTable *frn_bg_store;          /* addr+1 -> byte+1 */
static int frn_bg_ram_on(void)
{
    static int on = -1;
    if (on < 0) { const char *s = getenv("FRN_BG_RAM"); on = !(s && s[0] == '0'); }
    return on;
}
static uint64_t frn_bg_stored(hwaddr addr, unsigned size, uint64_t dflt, int *any)
{
    uint64_t v = 0; *any = 0;
    for (unsigned i = 0; i < size; i++) {
        gpointer p = frn_bg_store ? g_hash_table_lookup(frn_bg_store, GUINT_TO_POINTER((uint32_t)addr + i + 1)) : NULL;
        uint8_t b = p ? (uint8_t)(GPOINTER_TO_UINT(p) - 1) : (uint8_t)(dflt >> (8 * (size - 1 - i)));
        if (p) *any = 1;
        v = (v << 8) | b;
    }
    return v;
}
static uint64_t frn_bg_read(void *opaque, hwaddr addr, unsigned size)
{
    static int dbg_keyrd = -1;
    if (dbg_keyrd < 0) dbg_keyrd = getenv("FRN_DBG_KEYRD") ? 1 : 0;
    if (dbg_keyrd) {
        static uint32_t seen2[64]; static int ns2;
        int f=0; for(int i=0;i<ns2;i++) if(seen2[i]==(uint32_t)addr){f=1;break;}
        if(!f && ns2<64){ seen2[ns2++]=(uint32_t)addr;
            fprintf(stderr, "[bgrd] 0x%08x sz%u\n", (uint32_t)addr, size); }
    }
    /* FRN_MMIO_ZERO=lo-hi : return 0 instead of all-ones in that range (test a
     * "first-boot blank persistent store" hypothesis for where the date-set flag
     * is sourced). */
    static long zlo = -2, zhi = 0;
    if (zlo == -2) {
        const char *s = getenv("FRN_MMIO_ZERO"); zlo = -1;
        if (s) { char *e; zlo = strtol(s, &e, 16); if (*e=='-') zhi = strtol(e+1, NULL, 16); }
    }
    if (zlo >= 0 && addr >= (uint64_t)zlo && addr < (uint64_t)zhi) {
        return 0;
    }
    /* FRN_LOG_RD=lo-hi : log each distinct read address in range (capped) to find
     * the key/button input poll register. */
    {
        static long rlo = -2, rhi = 0; static uint32_t seen[512]; static int ns, nlog;
        if (rlo == -2) { const char *s = getenv("FRN_LOG_RD"); rlo = -1;
            if (s) { char *e; rlo = strtol(s,&e,16); if (*e=='-') rhi = strtol(e+1,NULL,16); } }
        if (rlo >= 0 && addr >= (uint64_t)rlo && addr < (uint64_t)rhi && nlog < 4000) {
            int f = 0; for (int i=0;i<ns;i++) if (seen[i]==(uint32_t)addr){f=1;break;}
            if (!f && ns<512) { seen[ns++]=(uint32_t)addr;
                fprintf(stderr, "[rd] 0x%08x\n", (uint32_t)addr); nlog++; }
        }
    }
    /* FRN_KEYPULSE=addr:andmask:after:dur[,addr:...] — edge-triggered key
     * injection into the 0x40060000 GPIO key-port block. The key driver
     * (0x10451100-0x10451230) reads each 16-bit port every scan and detects a
     * press as an active-low HIGH->LOW transition (debounced over several
     * scans). A static FRN_FORCE can't make an edge, so we PULSE: counting reads
     * of the exact `addr`, for reads [after, after+dur) we return
     * (0xffff & ~andmask) (masked bits driven LOW = pressed); otherwise 0xffff
     * (released). That yields release->press->release so the debounce fires.
     * Units of after/dur = number of reads of that addr (~1 per frame scan). */
    {
        static int kp_init = 0;
        static uint32_t kp_a[8], kp_m[8]; static long kp_after[8], kp_dur[8], kp_cnt[8];
        static int kp_n = 0;
        if (!kp_init) { kp_init = 1;
            const char *s = getenv("FRN_KEYPULSE");
            while (s && *s && kp_n < 8) {
                char *e; uint32_t a = (uint32_t)strtoul(s, &e, 16);
                if (e == s || *e != ':') break;
                uint32_t m = (uint32_t)strtoul(e+1, &e, 16); if (*e==':') e++;
                long af = strtol(e, &e, 0); if (*e==':') e++;
                long du = strtol(e, &e, 0);
                kp_a[kp_n]=a; kp_m[kp_n]=m; kp_after[kp_n]=af; kp_dur[kp_n]=du; kp_cnt[kp_n]=0; kp_n++;
                s = (*e==',') ? e+1 : e;
            }
        }
        for (int i = 0; i < kp_n; i++) {
            if ((uint32_t)addr == kp_a[i]) {
                long c = kp_cnt[i]++;
                if (c >= kp_after[i] && c < kp_after[i] + kp_dur[i]) {
                    static int logged[8];
                    if (!logged[i]) { logged[i] = 1;
                        fprintf(stderr, "[keypulse] 0x%08x driven LOW (0x%04x) at read #%ld\n",
                                kp_a[i], (unsigned)(0xffffu & ~kp_m[i]), c); }
                    return (uint64_t)(0xffffu & ~kp_m[i]);
                }
                return 0xffffu;
            }
        }
    }
    /* fremu: MMIO ranges read as all-ones (mmio_default); everything else is
     * RAM that reads 0 when unwritten. */
    int mmio = (addr >= 0x01000000 && addr < 0x10000000) ||
               (addr >= 0x40000000 && addr < 0x50000000) ||
               (addr >= 0x67000000 && addr < 0x67001000);
    uint64_t dflt = mmio ? 0xffffffffffffffffULL : 0;
    /* Rear LCD controller 0x40070000: status +0x0c bit 0x80 acknowledges the enable bit
     * written to control +0x0e (app-main 0x104395f4 writes +0x0e = 0x80, then polls
     * +0x0c & 0x80 at 0x104395fc). With read-your-writes this status must reflect the
     * control register, not an earlier write to +0x0c. */
    if (frn_bg_ram_on() && frn_bg_store && addr == 0x4007000c && size == 2) {
        int any; uint64_t st = frn_bg_stored(addr, 2, 0xffff, &any);
        uint64_t ctl = frn_bg_stored(0x4007000e, 2, 0xffff, &any);
        return (st & ~0x80ULL) | (ctl & 0x80);
    }
    if (frn_bg_ram_on() && frn_bg_store) {
        int any; uint64_t v = frn_bg_stored(addr, size, dflt, &any);
        if (any) {
            static int lg = -1; static int nl;
            if (lg < 0) lg = getenv("FRN_LOG_BGRAM") ? 1 : 0;
            uint64_t m = size >= 8 ? ~0ULL : ((1ULL << (8 * size)) - 1);
            if (lg && v != (dflt & m) && nl++ < 200)
                fprintf(stderr, "[bgram] rd 0x%08x sz%u = 0x%llx (default 0x%llx) pc~0x%08x\n",
                        (uint32_t)addr, size, (unsigned long long)v, (unsigned long long)(dflt & m), frn_cur_pc());
            return v;
        }
    }
    if (mmio) return dflt;
    frn_log_unmapped("RD", (uint32_t)addr, 0, size);   /* truly-dark read -> 0 */
    return 0;
}
/* Imaging-engine completion model (FRN_ENGINE_DONE=0 disables). Found from the
 * capture pipeline (2026-11-21, local experiment):
 *  - pre-process/repack engine 0x400d0000: start = write 0x400d0004 with bit15;
 *    IRQ vec42 (hw_irq_source_demux case 0x1a) needs 0x400d0006 bit15 (W1C) and
 *    0x400d0004 bit15, then posts IRQ source 0x8000001a+... (0x80000014).
 *  - develop engine 0x40128000/0x40100000: start = write 0x40128100 with bit14
 *    (configure_sensor_readout_params_104f3de0); IRQ vec34 (case 0x12,
 *    clock_tick_post_a) reads status 0x40128004 & 0x301 (W1C) & enable 0x40128002.
 * The work itself completes instantly; only the done status + IRQ are modelled. */
extern void k10d_cpucom_raise_vec(int v);
static uint64_t frn_bg_stored(hwaddr addr, unsigned size, uint64_t dflt, int *any);
static int frn_engine_on(void)
{
    static int on = -1;
    if (on < 0) { const char *s = getenv("FRN_ENGINE_DONE"); on = !(s && s[0] == '0'); }
    return on;
}
static void frn_bg_put16(uint32_t a, uint32_t v)
{
    g_hash_table_insert(frn_bg_store, GUINT_TO_POINTER(a + 1), GUINT_TO_POINTER(((v >> 8) & 0xff) + 1));
    g_hash_table_insert(frn_bg_store, GUINT_TO_POINTER(a + 2), GUINT_TO_POINTER((v & 0xff) + 1));
}
static void frn_engine_done(uint32_t addr, uint32_t val, unsigned size)
{
    if (!frn_engine_on()) return;
    static int log = -1; if (log < 0) log = getenv("FRN_IMG_LOG") ? 1 : 0;
    static long n34, n42;
    int any;
    if (addr == 0x400d0004 && size == 2 && (val & 0x8000)) {
        frn_bg_put16(0x400d0006, frn_bg_stored(0x400d0006, 2, 0, &any) | 0x8000);
        k10d_cpucom_raise_vec(42);
        if (log && n42++ < 20) fprintf(stderr, "[eng] 0x400d0000 start -> done, vec42\n");
    } else if (addr == 0x40128100 && size == 2 && (val & 0x4000)) {
        static long bits = -2;
        if (bits == -2) { const char *e = getenv("FRN_ENG34_BITS"); bits = e ? strtol(e, NULL, 16) : 0x100; }
        uint32_t en = frn_bg_stored(0x40128002, 2, 0, &any) & 0x301 & bits;
        frn_bg_put16(0x40128004, (frn_bg_stored(0x40128004, 2, 0, &any) | en) & 0xffff);
        k10d_cpucom_raise_vec(34);
        if (log && (n34++ < 20 || n34 % 500 == 0))
            fprintf(stderr, "[eng] develop start #%ld -> done (status 0x%x), vec34\n", n34, en);
    }
}
static void frn_bg_write(void *opaque, hwaddr addr, uint64_t val, unsigned size)
{
    /*
     * Display-controller write logging (inspectability). FRN_LOG_DISP logs every
     * write into the 0x40000000 peripheral window — in particular the OSDC plane
     * base registers (0x40000000/0x40004000/0x40008000) and palette (~0x40040390)
     * — so we can find where the firmware points the real (planar) framebuffer
     * and recover the CLUT. Values that look like SDRAM pointers are flagged.
     */
    static int on = -1;
    if (on < 0) {
        on = getenv("FRN_LOG_DISP") ? 1 : 0;
    }
    if (on && addr >= 0x40000000 && addr < 0x40100000) {
        const char *tag = "";
        if ((val & 0xff000000u) == 0x80000000u || (val & 0xff000000u) == 0x6a000000u) {
            tag = "  <-- RAM ptr";
        }
        fprintf(stderr, "[disp] wr 0x%08x = 0x%08x (sz%u)%s\n",
                (uint32_t)addr, (uint32_t)val, size, tag);
    }
    /* FRN_LOG_WR=lo-hi : log each distinct write address in range (capped). */
    {
        static long wlo = -2, whi = 0; static uint32_t wseen[512]; static int wns, wnlog;
        if (wlo == -2) { const char *s = getenv("FRN_LOG_WR"); wlo = -1;
            if (s) { char *e; wlo = strtol(s,&e,16); if (*e=='-') whi = strtol(e+1,NULL,16); } }
        if (wlo >= 0 && addr >= (uint64_t)wlo && addr < (uint64_t)whi && wnlog < 4000) {
            int f = 0; for (int i=0;i<wns;i++) if (wseen[i]==(uint32_t)addr){f=1;break;}
            if (!f && wns<512) { wseen[wns++]=(uint32_t)addr;
                fprintf(stderr, "[wr] 0x%08x = 0x%08x (sz%u)\n", (uint32_t)addr, (uint32_t)val, size); wnlog++; }
        }
    }
    frn_log_unmapped("WR", (uint32_t)addr, (uint32_t)val, size);  /* first write per address */
    if (frn_bg_ram_on()) {
        if (!frn_bg_store) frn_bg_store = g_hash_table_new(g_direct_hash, g_direct_equal);
        /* Write-1-to-clear IRQ status registers of the imaging engines (see frn_engine_done). */
        if (size == 2 && frn_engine_on() && (addr == 0x40128004 || addr == 0x400d0006)) {
            int any; val = frn_bg_stored(addr, 2, 0, &any) & ~val;
        }
        for (unsigned i = 0; i < size; i++)
            g_hash_table_insert(frn_bg_store, GUINT_TO_POINTER((uint32_t)addr + i + 1),
                                GUINT_TO_POINTER((uint32_t)((val >> (8 * (size - 1 - i))) & 0xff) + 1));
        frn_engine_done((uint32_t)addr, (uint32_t)val, size);
    }
}
static const MemoryRegionOps frn_bg_ops = {
    .read = frn_bg_read,
    .write = frn_bg_write,
    .endianness = DEVICE_BIG_ENDIAN,
    .valid.min_access_size = 1,
    .valid.max_access_size = 4,
};

/* Key/GPIO port device at 0x40060000 (0x40 bytes). Unlike frn_bg (which DROPS
 * writes), this PERSISTS the firmware's writes - essential because the key driver
 * read-modify-writes a key-state accumulator (0x4006001e) each scan; with dropped
 * writes it never accumulates -> no key CHANGE is ever seen -> the change-triggered
 * key decode never fires. Backing bytes init to 0xff (active-low keys = idle/not
 * pressed). FRN_KEYPULSE drives chosen offsets LOW on read (a press edge) - matched
 * on the ABSOLUTE address (0x40060000+off) to keep the env format consistent. */
static uint8_t frn_keyram[0x40];
static int frn_keyram_init;
static uint64_t frn_key_read(void *opaque, hwaddr off, unsigned size)
{
    if (!frn_keyram_init) { memset(frn_keyram, 0xff, sizeof frn_keyram); frn_keyram_init = 1; }
    uint32_t abs = 0x40060000u + (uint32_t)off;
    /* FRN_KEYPULSE edge injection (same syntax as frn_bg_read, absolute addr). */
    static int kp_init = 0;
    static uint32_t kp_a[8], kp_m[8]; static long kp_after[8], kp_dur[8], kp_cnt[8];
    static int kp_n = 0;
    if (!kp_init) { kp_init = 1; const char *s = getenv("FRN_KEYPULSE");
        while (s && *s && kp_n < 8) { char *e; uint32_t a = (uint32_t)strtoul(s,&e,16);
            if (e==s || *e!=':') break; uint32_t m=(uint32_t)strtoul(e+1,&e,16); if(*e==':')e++;
            long af=strtol(e,&e,0); if(*e==':')e++; long du=strtol(e,&e,0);
            kp_a[kp_n]=a; kp_m[kp_n]=m; kp_after[kp_n]=af; kp_dur[kp_n]=du; kp_cnt[kp_n]=0; kp_n++;
            s=(*e==',')?e+1:e; } }
    uint64_t v = 0;
    for (unsigned i = 0; i < size; i++) {
        uint32_t ba = abs + i; uint8_t byte = frn_keyram[(off + i) & 0x3f];
        for (int k = 0; k < kp_n; k++) if (kp_a[k] == ba) {
            long c = kp_cnt[k]++;
            if (c >= kp_after[k] && c < kp_after[k] + kp_dur[k]) byte = (uint8_t)(0xff & ~kp_m[k]);
        }
        v = (v << 8) | byte;       /* big-endian */
    }
    return v;
}
static void frn_key_write(void *opaque, hwaddr off, uint64_t val, unsigned size)
{
    if (!frn_keyram_init) { memset(frn_keyram, 0xff, sizeof frn_keyram); frn_keyram_init = 1; }
    for (unsigned i = 0; i < size; i++)
        frn_keyram[(off + size - 1 - i) & 0x3f] = (uint8_t)(val >> (8 * i));  /* big-endian */
}
static const MemoryRegionOps frn_key_ops = {
    .read = frn_key_read,
    .write = frn_key_write,
    .endianness = DEVICE_BIG_ENDIAN,
    .valid.min_access_size = 1,
    .valid.max_access_size = 4,
};

/*
 * 0x67000000 = SD card host controller, standard SDHCI register layout (the firmware's
 * accessors: +0x04 block size, +0x08 argument, +0x0C transfer mode, +0x0E command
 * (index<<8 | response flags; 0x0802 CMD8, 0x371a CMD55, 0x2902 ACMD41, 0x333a ACMD51,
 * 0x061a ACMD6, 0x063a CMD6), +0x10..+0x1C response, +0x20 buffer data port, +0x24
 * present state, +0x28 host control (bit 1 = 4-bit bus), +0x30 normal interrupt
 * status (bit 0 command complete, bit 1 transfer complete, bit 5 buffer read ready,
 * bit 15 error interrupt)). Model: a 0x1000 register file, big-endian. Writes store,
 * then force "all operations complete": present state 0x24=0x01F70F00 (bit 16 card
 * inserted), 0x28-0x33 cleared, then the 0x30 read path below synthesises status.
 */
static uint8_t frn_p67[0x1000];
/* Present-state bits 16-23 (+0x25): 16 card inserted, 17 card state stable, 18 card-detect
 * pin, 19 write-enable pin (1 = writable), 20-23 DAT line levels. No card unless an image is
 * given (FRN_SD=path); FRN_SD_PRESENT=1 keeps the old "inserted, write-protected, no data"
 * card. */
static uint8_t frn_sd_present_bits(void)
{
    static int st = -1;
    if (st < 0) st = k10d_sd_present() ? 2 : getenv("FRN_SD_PRESENT") ? 1 : 0;
    return st == 2 ? 0xff : st == 1 ? 0xf7 : 0xf2;
}

/* Interrupt status (+0x30) is synthesised in the read path because the write handler
 * clears 0x28-0x33: command-complete / transfer-complete (bits 0-1) toggle on each
 * poll so sdhc_wait_int_status catches them, buffer-read-ready (bit 5) is always set,
 * error interrupt (bit 15) stays clear (an earlier reading of +0x30 as a video
 * frame-sync register was wrong). */
/* FRN_P67_371A_DG diagnostic flag: set true while a 0x371a command txn is in flight
 * (see the 0x30 read handler + the 0x0e command-write handler). */
int frn_p67_371a_dg = 0;
static uint64_t frn_p67_read(void *opaque, hwaddr off, unsigned size)
{
    /* FRN_P67BTN="off:val,off:val" : override p67 bytes on read (inject button
     * state). Lets us test whether the 0x67000000 chip is the button source and
     * find the MENU/4-way bits, to drive menus in-emulator. */
    static int btn_init = 0; static uint8_t btn_val[0x40]; static uint8_t btn_set[0x40];
    if (!btn_init) { btn_init = 1;
        const char *s = getenv("FRN_P67BTN");
        while (s && *s) { char *e; long o = strtol(s,&e,16); if (e==s||*e!=':') break;
            long v = strtol(e+1,&e,16); if (o>=0&&o<0x40){btn_val[o]=(uint8_t)v;btn_set[o]=1;}
            s = (*e==',')?e+1:e; }
    }
    if (off < 0x40) { for (unsigned i=0;i<size;i++) if (btn_set[(off+i)&0x3f]) {
        /* a byte in this access is overridden: build the value with overrides */
        uint64_t v=0; for (unsigned j=0;j<size;j++){ uint32_t a=(off+j)&0xfff;
            uint8_t b = (a<0x40 && btn_set[a])?btn_val[a]:frn_p67[a]; v=(v<<8)|b; }
        return v; } }
    static int p67log = -1;
    if (p67log < 0) p67log = getenv("FRN_LOG_P67") ? 1 : 0;
    if (p67log && !(off >= 0x24 && off <= 0x33)) {   /* skip the status/handshake block */
        uint64_t rv = 0;
        for (unsigned i = 0; i < size; i++) rv = (rv << 8) | frn_p67[(off + i) & 0xfff];
        fprintf(stderr, "[p67rd] off 0x%03x sz%u = 0x%0*llx\n",
                (unsigned)off, size, size * 2, (unsigned long long)rv);
    }
    if (off <= 0x31 && off + size > 0x30) {
        static uint32_t frame;
        frame++;
        /* bit 15 = SDHCI error interrupt: sdhc_error_interrupt_pending FUN_1044b35e
         * fails every command while it is set. Clear unless FRN_P67_READY forces it. */
        static int ready = -1;
        if (ready < 0) ready = getenv("FRN_P67_READY") ? 0x8000 : 0;
        /* bits 0-1 command/transfer complete (toggled per poll), bit 5 buffer read
         * ready (sdhc_read_buffer waits for it before reading the data port). */
        uint16_t sync = (uint16_t)ready | 0x0020 | ((frame & 1) ? 0x0003 : 0x0000);
        if (k10d_sd_present())           /* image-backed card: real buffer-ready bits */
            sync = (uint16_t)ready | ((frame & 1) ? 0x0003 : 0x0000)
                 | (k10d_sd_read_ready() ? 0x0020 : 0) | (k10d_sd_write_ready() ? 0x0010 : 0);
        /* FRN_P67_371A_DG (diagnostic): raise the error interrupt during CMD55, so the
         * card does not answer APP_CMD and sd_card_init_worker takes the MMC init table. */
        if (frn_p67_371a_dg) sync |= 0x8000;
        frn_p67[0x30] = sync >> 8;
        frn_p67[0x31] = sync & 0xff;
    }
    /* 0x67000020 = SDHCI buffer data port: data-transfer commands are read from it word by
     * word (sdhc_read_buffer FUN_104499ca). The data depends on the command (last write to
     * +0x0E). CMD6 SWITCH_FUNC (0x063a) status: bit 0x20000 set (function supported),
     * bits 24-27 != 0xf. */
    if (off == 0x20 && size == 4) { uint32_t dv; if (k10d_sd_data_read32(&dv)) return dv; }
    if (off == 0x20 && size == 4) {
        uint16_t lastcmd = ((uint16_t)frn_p67[0x0e] << 8) | frn_p67[0x0f];
        if (lastcmd == 0x063a) return 0x00020000u;
        /* ACMD51 SEND_SCR (0x333a, sd_acmd51_read_scr FUN_104485ce): the 8-byte SCR.
         * Byte 1 low nibble = SD_BUS_WIDTHS (bit 0 1-bit, bit 2 4-bit); sd_select_bus_width
         * fails the card if neither is set. byte 1 = 0x01: a 1-bit-only card. */
        if (lastcmd == 0x333a) return 0x00010000u;
    }
    uint64_t v = 0;
    for (unsigned i = 0; i < size; i++) {
        v = (v << 8) | frn_p67[(off + i) & 0xfff];   /* big-endian */
    }
    return v;
}
static void frn_p67_write(void *opaque, hwaddr off, uint64_t val, unsigned size)
{
    { static int wl = -1; if (wl < 0) wl = getenv("FRN_LOG_P67") ? 1 : 0;
      if (wl && off < 0x40) fprintf(stderr, "[p67wr] off 0x%03x sz%u = 0x%0*llx\n",
          (unsigned)off, size, size*2, (unsigned long long)val); }
    if (off == 0x20 && size == 4 && k10d_sd_data_write32((uint32_t)val)) return;   /* card data */
    for (unsigned i = 0; i < size; i++) {
        frn_p67[(off + size - 1 - i) & 0xfff] = (val >> (8 * i)) & 0xff;
    }
    /* SD command response. Writing the command register (+0x0E) issues the command whose
     * argument is at +0x08; the response lands in +0x10..+0x1C (sdhc_latch_response copies
     * it to host+0x3b4..). Per command (index = high byte):
     *  - CMD8  SEND_IF_COND 0x0802: R7 echoes the argument (check pattern 0xAA).
     *  - ACMD41 0x2902: OCR, bit 31 (byte 0 bit 7) = card power-up done.
     *  - CMD1 (MMC) 0x0102: OCR, same busy bit.
     *  - everything else: R1 card status with no error bits (mask 0xfdf90008). */
    if (off <= 0x0e && off + size > 0x0e) {       /* a command was written to 0x0e */
        uint16_t cmd = ((uint16_t)frn_p67[0x0e] << 8) | frn_p67[0x0f];
        /* FRN_P67_371A_DG: mark a 0x371a txn in-flight so the 0x30 read asserts the
         * draw-guard bit15 -> build_hw_txn returns 0 -> worker takes build PATH A. */
        { static int dg = -1; if (dg < 0) dg = getenv("FRN_P67_371A_DG") ? 1 : 0;
          if (dg) frn_p67_371a_dg = (cmd == 0x371a); }
        uint32_t sd_arg = (uint32_t)frn_p67[0x08] << 24 | frn_p67[0x09] << 16 | frn_p67[0x0a] << 8 | frn_p67[0x0b];
        uint32_t sd_bs = ((uint32_t)frn_p67[0x04] << 8 | frn_p67[0x05]) & 0xfff;
        { extern uint32_t k10d_sd_dbg_regs[4];
          k10d_sd_dbg_regs[0] = (uint32_t)frn_p67[0] << 24 | frn_p67[1] << 16 | frn_p67[2] << 8 | frn_p67[3];
          k10d_sd_dbg_regs[1] = (uint32_t)frn_p67[0x0c] << 8 | frn_p67[0x0d];
          k10d_sd_dbg_regs[2] = (uint32_t)frn_p67[0x06] << 8 | frn_p67[0x07]; }
        { static int wpc = -1; static long sarg = -2;
          if (wpc < 0) wpc = getenv("FRN_SD_WIPEPC") ? 1 : 0;
          /* FRN_SD_STACKARG=hex: same stack dump for any data command with this argument
           * (finds the caller chain of a given sector read, e.g. the root-dir re-reads). */
          if (sarg == -2) { const char *s = getenv("FRN_SD_STACKARG"); sarg = s ? (long)strtoul(s, NULL, 16) : -1; }
          int wi = cmd >> 8;   /* CMD24=0x18 single write, CMD25=0x19 multi write */
          if (((wpc && (wi == 24 || wi == 25) && sd_arg < 0x20000) || (sarg >= 0 && sd_arg == (uint32_t)sarg && wi >= 17))
              && current_cpu) {
              CPUFRNState *e = &FRN_CPU(current_cpu)->env;
              fprintf(stderr, "[sdwipe] CMD%d arg 0x%08x (sector %u) PC 0x%08x rp 0x%08x sp 0x%08x\n",
                      wi, sd_arg, sd_arg >> 9, e->pc, e->rp, e->regs[15]);
              fprintf(stderr, "[sdwipe]   stack:");
              for (int k = 0; k < 128; k++) {
                  uint8_t b[4]; address_space_read(&address_space_memory, e->regs[15] + k*4,
                      MEMTXATTRS_UNSPECIFIED, b, 4);
                  uint32_t sv = (uint32_t)b[0]<<24|b[1]<<16|b[2]<<8|b[3];
                  if (sv >= 0x10000000u && sv < 0x11000000u) fprintf(stderr, " 0x%08x", sv);
              }
              fprintf(stderr, "\n"); } }
        if (k10d_sd_command(cmd, sd_arg, &frn_p67[0x10], sd_bs)) {
            /* image-backed card (k10d_sd.c) answered */
        } else
        if (cmd == 0x0802) {                 /* ping: echo the 0x08 data (0xaa marker) */
            frn_p67[0x10] = frn_p67[0x08]; frn_p67[0x11] = frn_p67[0x09];
            frn_p67[0x12] = frn_p67[0x0a]; frn_p67[0x13] = frn_p67[0x0b];
        } else if (cmd == 0x2902) {          /* ACMD41: OCR power-up done */
            frn_p67[0x10] = 0x80; frn_p67[0x11] = 0; frn_p67[0x12] = 0; frn_p67[0x13] = 0;
        } else if (cmd == 0x0102) {
            /* CMD1 (MMC init table): OCR with bit 31 power-up done; bits 30:29 (byte 0
             * bits 6:5) = access mode, selectable via FRN_P67_BODYMODE (0..3, default 0). */
            static int bm = -2; if (bm == -2) { const char *e = getenv("FRN_P67_BODYMODE"); bm = e ? atoi(e) : 0; }
            uint8_t b0 = 0x80 | ((bm & 2) ? 0x40 : 0) | ((bm & 1) ? 0x20 : 0);
            frn_p67[0x10] = b0; frn_p67[0x11] = 0; frn_p67[0x12] = 0; frn_p67[0x13] = 0;
        } else {                             /* status/control query: clean, no error bits */
            frn_p67[0x10] = 0; frn_p67[0x11] = 0; frn_p67[0x12] = 0; frn_p67[0x13] = 0;
        }
        /* The command has now positioned the card (load_block for a read / xfer_addr+wr_active
         * for a write). Run any port DMA that was armed before this command, so it transfers
         * THIS command's data rather than the previous command's stale position (see
         * frn_dma_d60_start). */
        { int ri = cmd >> 8;
          if (current_cpu) {
              CPUFRNState *de = &FRN_CPU(current_cpu)->env;
              if (ri == 17 || ri == 18) { extern void frn_dma_d60_flush_read(CPUFRNState *);  frn_dma_d60_flush_read(de); }
              if (ri == 24 || ri == 25) { extern void frn_dma_d60_flush_write(CPUFRNState *); frn_dma_d60_flush_write(de); }
          } }
    }
    frn_p67[0x24] = 0x01; frn_p67[0x25] = frn_sd_present_bits();
    frn_p67[0x26] = 0x0f; frn_p67[0x27] = 0x00;
    for (int b = 0x28; b < 0x34; b++) {
        frn_p67[b] = 0;
    }
    frn_p67[0x2d] |= 0x02;
}
static const MemoryRegionOps frn_p67_ops = {
    .read = frn_p67_read,
    .write = frn_p67_write,
    .endianness = DEVICE_BIG_ENDIAN,
    .valid.min_access_size = 1,
    .valid.max_access_size = 4,
};

/*
 * Watch-counter / RTC device at 0x40090000. The ISR (FUN_104fae06) reads:
 *   +0x06 bit15 : interrupt pending (acked by writing 0x8000) -> keep asserted
 *   +0x04 bit15 : "is the clock set?"  First boot = UNSET (bit15=0), which is
 *                 what makes the firmware raise the "Date Adjust" screen. Modeled
 *                 explicitly here rather than inheriting the 0xffffffff background
 *                 (which read as clock-SET and drove the wrong, time-running
 *                 branch, posting event 0x80000013 thousands of times).
 */
static uint64_t frn_wc_read(void *opaque, hwaddr off, unsigned size)
{
    uint8_t reg[0x10] = { 0 };
    reg[0x06] = 0x80;              /* +0x06 = 0x8000: IRQ pending */
    /* +0x04 bit15 = "clock set?". Default NOT set (first boot). Env override to
     * compare the clock-set branch (does it drive the rear-UI redraw?). */
    static int clkset = -1;
    if (clkset < 0) clkset = getenv("FRN_CLOCK_SET") ? 1 : 0;
    if (clkset) reg[0x04] = 0x80;  /* +0x04 = 0x8000: clock IS set */
    uint64_t v = 0;
    for (unsigned i = 0; i < size; i++) {
        v = (v << 8) | reg[(off + i) & 0xf];   /* big-endian */
    }
    return v;
}
static void frn_wc_write(void *opaque, hwaddr off, uint64_t val, unsigned size)
{
    /* ack (write 0x8000 to +0x06) is a no-op: the counter re-asserts each tick */
}
static const MemoryRegionOps frn_wc_ops = {
    .read = frn_wc_read,
    .write = frn_wc_write,
    .endianness = DEVICE_BIG_ENDIAN,
    .valid.min_access_size = 1,
    .valid.max_access_size = 4,
};



/* 0x401c0000 SD card door / card detect controller.
 * Status registers (0x106/0x126) always return 0x00 (door closed, no card). */
static uint8_t frn_sdcard_mem[0x200];
static uint64_t frn_sdcard_read(void *opaque, hwaddr off, unsigned size)
{
    /* Status registers always return 0x00 (door closed, no card) */
    if ((off == 0x106 || off == 0x126) && size <= 2) {
        return 0;
    }
    if (size == 1) return frn_sdcard_mem[off];
    if (size == 2) return (frn_sdcard_mem[off] << 8) | frn_sdcard_mem[off+1];
    if (size == 4) return (frn_sdcard_mem[off] << 24) | (frn_sdcard_mem[off+1] << 16) |
                          (frn_sdcard_mem[off+2] << 8) | frn_sdcard_mem[off+3];
    return 0;
}
static void frn_sdcard_write(void *opaque, hwaddr off, uint64_t val, unsigned size)
{
    if (size == 1) frn_sdcard_mem[off] = (uint8_t)val;
    else if (size == 2) { frn_sdcard_mem[off] = (uint8_t)(val >> 8); frn_sdcard_mem[off+1] = (uint8_t)val; }
    else if (size == 4) {
        frn_sdcard_mem[off] = (uint8_t)(val >> 24); frn_sdcard_mem[off+1] = (uint8_t)(val >> 16);
        frn_sdcard_mem[off+2] = (uint8_t)(val >> 8); frn_sdcard_mem[off+3] = (uint8_t)val;
    }
}
static const MemoryRegionOps frn_sdcard_ops = {
    .read = frn_sdcard_read,
    .write = frn_sdcard_write,
    .endianness = DEVICE_BIG_ENDIAN,
    .valid.min_access_size = 1,
    .valid.max_access_size = 4,
};

/* K10D memory map (from fremu.py / RE) */
#define K10D_ROM_BASE   0x10000000
#define K10D_ROM_SIZE   0x01000000      /* 16 MiB window (firmware ~8.4 MiB) */
#define K10D_SDRAM_BASE 0x80000000
#define K10D_SDRAM_SIZE 0x10000000      /* 256 MiB: firmware writes task stacks/TCB
                                         * pointers up to ~0x8fffffff (kernel init
                                         * pc 0x1000e858/e876); 64 MiB dropped them
                                         * -> corrupt kernel structs -> reloop (d308) */
#define K10D_WRAM_BASE  0x6a000000
#define K10D_WRAM_SIZE  0x00100000      /* 1 MiB work RAM */
#define K10D_ENTRY      0x10008000
#define K10D_SP         0x8003F000

/* Framebuffer dump: FRN_FB_DUMP=/tmp/screen.ppm dumps the SDRAM framebuffer
 * region to a PPM file every 5 seconds. The framebuffer is at
 * K10D_SDRAM_BASE + offset, where offset is determined by the OSDC config.
 * For now, we dump the first 640x480 region of SDRAM as RGB24. */
static void frn_fb_dump_timer(void *opaque)
{
    static int dump_count = 0;
    const char *path = getenv("FRN_FB_DUMP");
    if (!path) return;
    
    dump_count++;
    char filename[256];
    snprintf(filename, sizeof(filename), "%s.%d", path, dump_count);
    
    /* Framebuffer params: 640x480 RGB24 (assumed from OSDC config) */
    int width = 640, height = 480;
    size_t fb_size = width * height * 3;
    
    /* Read from SDRAM at the framebuffer location.
     * The OSDC config suggests the framebuffer is in the 0x80008000 range
     * (per prior analysis: dense, structured UI data).
     * Use address_space_read to read from the physical address. */
    uint8_t *fb = g_malloc(fb_size);
    
    /* Framebuffer physical address: 0x80008000 (SDRAM) */
    hwaddr fb_phys = 0x80008000;
    AddressSpace *as = &address_space_memory;
    MemTxResult result = address_space_read(as, fb_phys, MEMTXATTRS_UNSPECIFIED, fb, fb_size);
    if (result == MEMTX_OK) {
        fprintf(stderr, "[frn-fb] read framebuffer from 0x%lx (%zu bytes)\n", 
                (unsigned long)fb_phys, fb_size);
    } else {
        fprintf(stderr, "[frn-fb] ERROR: address_space_read failed at 0x%lx\n", 
                (unsigned long)fb_phys);
        /* Fill with test pattern as fallback */
        for (int y = 0; y < height; y++) {
            for (int x = 0; x < width; x++) {
                fb[(y * width + x) * 3 + 0] = x & 0xff;     /* R */
                fb[(y * width + x) * 3 + 1] = y & 0xff;     /* G */
                fb[(y * width + x) * 3 + 2] = (x ^ y) & 0xff; /* B */
            }
        }
    }
    
    FILE *f = fopen(filename, "wb");
    if (f) {
        fprintf(f, "P6\n%d %d\n255\n", width, height);
        fwrite(fb, 1, fb_size, f);
        fclose(f);
        fprintf(stderr, "[frn-fb] dumped framebuffer to %s (%dx%d)\n", filename, width, height);
    }
    g_free(fb);
}

static void k10d_init(MachineState *machine)
{
    MemoryRegion *sysmem = get_system_memory();
    MemoryRegion *rom = g_new(MemoryRegion, 1);
    MemoryRegion *sdram = g_new(MemoryRegion, 1);
    MemoryRegion *wram = g_new(MemoryRegion, 1);
    FRNCPU *cpu;
    int sz;

    cpu = FRN_CPU(cpu_create(machine->cpu_type));

    /* Background default-MMIO over the whole 32-bit space (low priority). */
    MemoryRegion *bg = g_new(MemoryRegion, 1);
    memory_region_init_io(bg, NULL, &frn_bg_ops, NULL, "frn.mmio-default",
                          0x100000000ULL);
    memory_region_add_subregion_overlap(sysmem, 0, bg, -1);

    /* Low memory [0, 0x01000000): fremu treats this as RAM (control regs like
     * DICR 0x44, timer 0x48-0x4F, ICR table 0x440.. live here and must persist
     * across writes). Timer/DICR hardware side-effects are layered in the
     * interpreter helper. */
    MemoryRegion *lowram = g_new(MemoryRegion, 1);
    memory_region_init_ram(lowram, NULL, "k10d.lowram", 0x01000000, &error_fatal);
    memory_region_add_subregion(sysmem, 0, lowram);

    /* 0x67000000 SD host controller (SDHCI layout): present state from frn_sd_present_bits. */
    frn_p67[0x24] = 0x01; frn_p67[0x25] = frn_sd_present_bits();
    frn_p67[0x26] = 0x0f; frn_p67[0x27] = 0x00;
    frn_p67[0x2d] |= 0x02;
    MemoryRegion *p67 = g_new(MemoryRegion, 1);
    memory_region_init_io(p67, NULL, &frn_p67_ops, NULL, "frn.sdhc", 0x1000);
    memory_region_add_subregion(sysmem, 0x67000000, p67);

    /* Watch-counter / RTC (clock-unset first-boot state) at 0x40090000. */
    MemoryRegion *wc = g_new(MemoryRegion, 1);
    memory_region_init_io(wc, NULL, &frn_wc_ops, NULL, "frn.watchcnt", 0x10);
    memory_region_add_subregion_overlap(sysmem, 0x40090000, wc, 1);

    /* 0x401c0000 peripheral (SD card door / card detect controller).
     * Boot trace: fw writes 0x3 to 0x401c0104/0x401c0124, then reads 0x401c0106/0x401c0126.
     * Status register (0x106/0x126) bits: bit0=card present?, bit1=door open?
     * Return 0x00 (all clear) = door closed, no card = good boot state. */
    MemoryRegion *sdcard = g_new(MemoryRegion, 1);
    memory_region_init_io(sdcard, NULL, &frn_sdcard_ops, NULL, "frn.sdcard", 0x200);
    memory_region_add_subregion_overlap(sysmem, 0x401c0000, sdcard, 1);

    /* ROM (firmware). Writable RAM-backed for bring-up simplicity. */
    memory_region_init_ram(rom, NULL, "k10d.rom", K10D_ROM_SIZE, &error_fatal);
    memory_region_add_subregion(sysmem, K10D_ROM_BASE, rom);

    memory_region_init_ram(sdram, NULL, "k10d.sdram", K10D_SDRAM_SIZE,
                           &error_fatal);
    memory_region_add_subregion(sysmem, K10D_SDRAM_BASE, sdram);

    memory_region_init_ram(wram, NULL, "k10d.wram", K10D_WRAM_SIZE,
                           &error_fatal);
    memory_region_add_subregion(sysmem, K10D_WRAM_BASE, wram);

    /* State/SRAM banks the firmware WRITES during app-main init and the peripheral
     * ISR handlers READ back (d308). Previously unmapped -> writes dropped, reads 0,
     * so every handler status-gate failed and no task ever woke. 0x6b000000 is a 2nd
     * SRAM bank adjacent to WRAM (written @app-main 0x10439558..); 0x5c000000 is a
     * display/peripheral state block (written @0x1043ec6e/0x10440488). Back them as
     * RAM so the firmware's own writes persist and the handlers read real state. */
    MemoryRegion *sram6b = g_new(MemoryRegion, 1);
    memory_region_init_ram(sram6b, NULL, "k10d.sram6b", 0x00100000, &error_fatal);
    memory_region_add_subregion(sysmem, 0x6b000000, sram6b);
    MemoryRegion *blk5c = g_new(MemoryRegion, 1);
    memory_region_init_ram(blk5c, NULL, "k10d.blk5c", 0x00100000, &error_fatal);
    memory_region_add_subregion(sysmem, 0x5c000000, blk5c);
    /* 0x5c002000-0x5c00203f is a bank of four reload timers (firmware timer class,
     * vtable 0x105a05a0), not OSDC status. Their behavior is modeled in
     * target/frn/op_helper.c (frn_tmr_*); here they are plain RAM in blk5c. */
    /* More dark regions the firmware uses (found via FRN_LOG_UNMAPPED, d308):
     * 0x50000000 written first in app-main (0x10439428, 3-channel controller);
     * 0x66000000 / 0x68000000 read by 0x1044b/0x104ab code. Back as RAM. */
    MemoryRegion *blk50 = g_new(MemoryRegion, 1);
    memory_region_init_ram(blk50, NULL, "k10d.blk50", 0x00100000, &error_fatal);
    memory_region_add_subregion(sysmem, 0x50000000, blk50);
    MemoryRegion *blk66 = g_new(MemoryRegion, 1);
    memory_region_init_ram(blk66, NULL, "k10d.blk66", 0x00100000, &error_fatal);
    memory_region_add_subregion(sysmem, 0x66000000, blk66);
    MemoryRegion *blk68 = g_new(MemoryRegion, 1);
    memory_region_init_ram(blk68, NULL, "k10d.blk68", 0x00100000, &error_fatal);
    memory_region_add_subregion(sysmem, 0x68000000, blk68);

    /* OSDC (on-screen display controller) register file at 0x40000000 (d309).
     * Plane-base regs 0x40000000/0x40004000/0x40008000, control+palette ~0x40040000.
     * Previously these READ as 0xffffffff (frn_bg_read fallthrough), so the firmware's
     * display-config read-modify-write operated on garbage. Back the CONFIG sub-range
     * 0x40000000..0x40070000 (plane bases 0x40000000/4000/8000, control+palette
     * ~0x40040000) as RAM so reads return written values. Deliberately stop at
     * 0x40070000: the status register 0x4007000c is POLLED by app-main (pc 0x10439600)
     * and must read "ready" — leaving 0x40070000+ to fall through to the 0xffffffff
     * background keeps that poll passing (readback-0 there regresses app-main into an
     * infinite spin). Priority 0 sits below the 0x40090000 watch-counter overlay. */
    MemoryRegion *osdc = g_new(MemoryRegion, 1);
    /* 0x00060000 (NOT 0x70000): stop before the 0x40060000 key/GPIO port so it is
     * NOT shadowed by this RAM (RAM regions take a direct TLB path that bypasses the
     * keyport overlay). 0x40060000+ then falls to frn_bg_read (all-ones idle + keypulse). */
    memory_region_init_ram(osdc, NULL, "k10d.osdc", 0x00060000, &error_fatal);
    memory_region_add_subregion_overlap(sysmem, 0x40000000, osdc, 0);

    /* Key/GPIO port device at 0x40060000: persists the key driver's RMW accumulator
     * (frn_bg drops writes, which breaks key detection) + honors FRN_KEYPULSE. OSDC
     * above is sized to 0x60000 so it does not overlap this. */
    MemoryRegion *keyport = g_new(MemoryRegion, 1);
    memory_region_init_io(keyport, NULL, &frn_key_ops, NULL, "frn.keyport", 0x40);
    memory_region_add_subregion_overlap(sysmem, 0x40060000, keyport, 1);

    if (!machine->firmware) {
        error_report("k10d: supply the firmware with -bios FWDC162B.BIN");
        exit(1);
    }
    sz = load_image_targphys(machine->firmware, K10D_ROM_BASE, K10D_ROM_SIZE,
                             &error_fatal);
    if (sz < 0) {
        error_report("k10d: could not load firmware '%s'", machine->firmware);
        exit(1);
    }

    /* Rear display window + buttons (-display gtk/sdl/vnc; inert with -display none). */
    k10d_display_init();

    /* Host pointers for the interpreter's fast paths (target/frn/op_helper.c): plain RAM
     * regions with no device overlays inside them. */
    k10d_host_lowram = memory_region_get_ram_ptr(lowram);
    k10d_host_rom = memory_region_get_ram_ptr(rom);
    k10d_host_sdram = memory_region_get_ram_ptr(sdram);
    k10d_host_wram = memory_region_get_ram_ptr(wram);

    cpu->env.pc = K10D_ENTRY;
    cpu->env.regs[15] = K10D_SP;
    
    /* Framebuffer dump timer: FRN_FB_DUMP=/tmp/screen.ppm */
    if (getenv("FRN_FB_DUMP")) {
        QEMUTimer *fb_timer = timer_new_ns(QEMU_CLOCK_REALTIME, frn_fb_dump_timer, NULL);
        timer_mod(fb_timer, qemu_clock_get_ns(QEMU_CLOCK_REALTIME) + 5000000000LL); /* 5 seconds */
    }
}

static void k10d_machine_init(MachineClass *mc)
{
    mc->desc = "Pentax K10D (Fujitsu MB91683 / FR60Lite)";
    mc->init = k10d_init;
    mc->default_cpu_type = TYPE_FRN_CPU;
    mc->default_ram_size = K10D_SDRAM_SIZE;
    mc->no_parallel = 1;
    mc->no_floppy = 1;
    mc->no_cdrom = 1;
}

DEFINE_MACHINE("k10d", k10d_machine_init)
