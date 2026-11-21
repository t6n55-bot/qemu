/*
 * K10D rear display + rear buttons for interactive use.
 *
 * Display: the display controller at 0x40040000 scans out two 640x480 layers, each a
 * planar YCbCr 4:2:0 frame (Y at base, Cb at base + 0x4b000, Cr at base + 0x5dc00).
 * Layer A (background) base register +0x308, layer B (text overlay) +0x328; registers
 * hold address & 0x3ffffff0 and the frames live in SDRAM at 0x80000000 | base. The
 * firmware double-buffers by rewriting these registers, so they are read every refresh.
 * Layer A is opaque; layer B carries a 4-bit alpha plane (two pixels per byte, high nibble
 * first) at the address in +0x334 (base + 0x70800), and is blended over A (see k10d-re
 * harness2/render_layers.py, which this mirrors). Before each redraw the firmware clears the
 * back buffer with image-processor fills (k10d_imgproc.c engine A, mode 0x700).
 *
 * Buttons: the companion CPU reports them in its 'A' status record, active-low; byte 3
 * (0x01 right, 0x02 left, 0x04 down, 0x08 up, 0x10 OK, 0x80 MENU; up/left confirmed by
 * Andrew on the live window). Keys: arrows, Enter = OK,
 * M = MENU, I = INFO (byte 2 0x10), F = Fn (byte 5 0x08), V = playback guess (byte 2 0x20);
 * P = power off (an all-zero 'A' record, which drives the firmware into its
 * power-off path, where it saves settings to flash; see k10d_flash.c / FRN_FLASH_SAVE).
 * Each change of button state is handed to the companion-CPU model, which queues the
 * message and raises the request interrupt on the CPU thread.
 */
#include "qemu/osdep.h"
#include "ui/console.h"
#include "ui/input.h"
#include "system/address-spaces.h"
#include "system/memory.h"
#include "qemu/timer.h"
#include "k10d_display.h"

void k10d_cpucom_post_key_record(const uint8_t *payload9);   /* target/frn/k10d_cpucom.c */
void k10d_cpucom_post_msg(char c, const uint8_t *payload, int n);   /* FRN_MSG_FILE */
void k10d_cpucom_raise_vec(int v);
void k10d_cpucom_hold_lines(uint32_t set, uint32_t clr);

#define W 640
#define H 480
#define CB_OFF 0x4b000
#define CR_OFF 0x5dc00
#define FRAME  0x70800

static QemuConsole *con;
static uint8_t frame_a[FRAME], frame_b[FRAME], alpha_b[(W / 2) * H];
static uint8_t byte3 = 0xff;

static uint32_t rd32(hwaddr a)
{
    uint8_t b[4];
    address_space_read(&address_space_memory, a, MEMTXATTRS_UNSPECIFIED, b, 4);
    return ((uint32_t)b[0] << 24) | (b[1] << 16) | (b[2] << 8) | b[3];
}

static inline uint32_t yuv2rgb(int y, int u, int v)
{
    u -= 128; v -= 128;
    int r = y + (1402 * v) / 1000, g = y - (344 * u + 714 * v) / 1000, b = y + (1772 * u) / 1000;
    r = r < 0 ? 0 : r > 255 ? 255 : r;
    g = g < 0 ? 0 : g > 255 ? 255 : g;
    b = b < 0 ? 0 : b > 255 ? 255 : b;
    return (r << 16) | (g << 8) | b;
}

static bool k10d_display_update(void *opaque)
{
    DisplaySurface *s = qemu_console_surface(con);
    uint32_t base_a = rd32(0x40040308) & 0x3ffffff0, base_b = rd32(0x40040328) & 0x3ffffff0;
    if (base_a) address_space_read(&address_space_memory, 0x80000000u | base_a, MEMTXATTRS_UNSPECIFIED, frame_a, FRAME);
    if (base_b) address_space_read(&address_space_memory, 0x80000000u | base_b, MEMTXATTRS_UNSPECIFIED, frame_b, FRAME);
    uint32_t base_al = rd32(0x40040334) & 0x3ffffff0;
    if (base_b && base_al)
        address_space_read(&address_space_memory, 0x80000000u | base_al, MEMTXATTRS_UNSPECIFIED, alpha_b, sizeof alpha_b);
    else memset(alpha_b, base_b ? 0xff : 0, sizeof alpha_b);
    uint8_t *dst = surface_data(s);
    int stride = surface_stride(s);
    for (int y = 0; y < H; y++) {
        uint32_t *row = (uint32_t *)(dst + y * stride);
        for (int x = 0; x < W; x++) {
            int c = (y / 2) * (W / 2) + x / 2;
            uint32_t pa = base_a ? yuv2rgb(frame_a[y * W + x], frame_a[CB_OFF + c], frame_a[CR_OFF + c]) : 0;
            uint8_t ab = alpha_b[y * (W / 2) + x / 2];
            int al = (x & 1) ? (ab & 0x0f) : (ab >> 4);           /* 4-bit alpha, two pixels per byte */
            uint32_t px = pa;
            if (base_b && al) {
                uint32_t pb = yuv2rgb(frame_b[y * W + x], frame_b[CB_OFF + c], frame_b[CR_OFF + c]);
                px = 0;
                for (int sh = 0; sh < 24; sh += 8) {
                    int ca = (pa >> sh) & 0xff, cbv = (pb >> sh) & 0xff;
                    px |= (uint32_t)((ca * (15 - al) + cbv * al) / 15) << sh;
                }
            }
            row[x] = px;
        }
    }
    qemu_console_update_full(con);
    return true;
}

static const GraphicHwOps k10d_display_ops = {
    .gfx_update = k10d_display_update,
};

static uint8_t rec[9] = { 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff };

static void k10d_key_event(DeviceState *dev, QemuConsole *src, QemuInputEvent *evt)
{
    int q = qemu_input_linux_to_qcode(evt->key.key);
    bool down = evt->key.down;
    int byte; uint8_t bit;
    switch (q) {
    case Q_KEY_CODE_RIGHT: byte = 3; bit = 0x01; break;
    case Q_KEY_CODE_LEFT:  byte = 3; bit = 0x02; break;
    case Q_KEY_CODE_DOWN:  byte = 3; bit = 0x04; break;
    case Q_KEY_CODE_UP:    byte = 3; bit = 0x08; break;
    case Q_KEY_CODE_RET: case Q_KEY_CODE_KP_ENTER: byte = 3; bit = 0x10; break;
    case Q_KEY_CODE_M: case Q_KEY_CODE_ESC: byte = 3; bit = 0x80; break;   /* MENU / back (Esc) */
    /* Found with the firmware's own SWITCH TEST screen (debug menu, MODSET.TXT [OPEN_DEBUG_MENU]) by
     * clearing each record bit in turn and reading which label lit up. Active-low like the rest. */
    case Q_KEY_CODE_S:     byte = 0; bit = 0x01; break;   /* SWS: shutter half-press */
    case Q_KEY_CODE_A:     byte = 0; bit = 0x08; break;   /* AFSTART (AF button) */
    case Q_KEY_CODE_E:     byte = 2; bit = 0x01; break;   /* AEL */
    case Q_KEY_CODE_G:     byte = 2; bit = 0x02; break;   /* GREEN */
    case Q_KEY_CODE_W:     byte = 2; bit = 0x04; break;   /* PRV (preview) */
    case Q_KEY_CODE_D:     byte = 2; bit = 0x20; break;   /* DISP (same bit as V) */
    case Q_KEY_CODE_Z:     byte = 2; bit = 0x80; break;   /* XV / AVSET (one of the two) */
    case Q_KEY_CODE_R:     byte = 5; bit = 0x01; break;   /* RAW */
    case Q_KEY_CODE_X:     byte = 5; bit = 0x04; break;   /* SR (shake reduction) */
    case Q_KEY_CODE_BACKSPACE: case Q_KEY_CODE_DELETE:
                           byte = 5; bit = 0x40; break;   /* ERASE */
    case Q_KEY_CODE_U:     byte = 4; bit = 0x01; break;   /* FLPOP: flash pop-up */
    case Q_KEY_CODE_C:     byte = 2; bit = 0x08; break;   /* DOOR: card door */
    case Q_KEY_CODE_I:     byte = 2; bit = 0x10; break;   /* INFO (opens the shooting-info screen from idle) */
    case Q_KEY_CODE_V:     byte = 2; bit = 0x20; break;   /* playback: item 0xe, the shooting-mode handler's mode switch (unconfirmed) */
    case Q_KEY_CODE_F:     byte = 5; bit = 0x08; break;   /* Fn (opens the Fn menu from idle) */
    case Q_KEY_CODE_P:
        if (down) {
            static const uint8_t off[9] = { 0 };
            fprintf(stderr, "[k10d] power off\n");
            k10d_cpucom_post_key_record(off);
        }
        return;
    default: return;
    }
    uint8_t nb = down ? (rec[byte] & ~bit) : (rec[byte] | bit);
    if (nb == rec[byte]) return;                  /* key repeat */
    rec[byte] = nb;
    k10d_cpucom_post_key_record(rec);
}

static const QemuInputHandler k10d_key_handler = {
    .name = "K10D rear buttons",
    .mask = INPUT_EVENT_MASK_KEY,
    .event = k10d_key_event,
};

/* FRN_REC_FILE=<path>: debug aid. Every 100 ms the file is read; it holds the 9 payload bytes of
 * the 'A' button record as hex ("ffffffffffffffffff", active-low). A change is posted to the
 * companion-CPU model exactly like a key event. Used to find which bit drives which switch
 * on the firmware's SWITCH TEST screen. */
static QEMUTimer *rec_timer;
static uint8_t rec_prev[9] = { 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff };
static void k10d_rec_file_poll(void *opaque)
{
    const char *path = getenv("FRN_REC_FILE");
    FILE *f = path ? fopen(path, "r") : NULL;
    if (f) {
        char line[64] = "";
        if (fgets(line, sizeof line, f) && strlen(line) >= 18) {
            uint8_t nr[9]; bool ok = true;
            for (int i = 0; i < 9 && ok; i++) {
                unsigned v;
                ok = sscanf(line + 2 * i, "%2x", &v) == 1;
                nr[i] = v;
            }
            if (ok && memcmp(nr, rec_prev, 9)) {
                memcpy(rec_prev, nr, 9);
                memcpy(rec, nr, 9);
                fprintf(stderr, "[k10d] rec-file -> %02x%02x%02x%02x%02x%02x%02x%02x%02x\n", rec[0],rec[1],rec[2],rec[3],rec[4],rec[5],rec[6],rec[7],rec[8]);
                k10d_cpucom_post_key_record(rec);
            }
        }
        fclose(f);
    }
    /* FRN_MSG_FILE=<path>: when its contents change, each line "<letter> [hex payload]" is queued
     * as a companion-CPU status message (unset payload bytes stay 0xff). Debug aid. */
    const char *mp = getenv("FRN_MSG_FILE");
    FILE *mf = mp ? fopen(mp, "r") : NULL;
    if (mf) {
        static char prev[2048]; char buf[2048] = "";
        size_t n = fread(buf, 1, sizeof buf - 1, mf); buf[n] = 0; fclose(mf);
        if (strcmp(buf, prev)) {
            memcpy(prev, buf, sizeof prev);
            for (char *ln = strtok(buf, "\n"); ln; ln = strtok(NULL, "\n")) {
                if (!ln[0] || ln[0] == '#') continue;
                if (ln[0] == '!') {     /* "!<vec>": raise that interrupt vector once */
                    int v = atoi(ln + 1);
                    fprintf(stderr, "[k10d] msg-file -> raise vector %d\n", v);
                    k10d_cpucom_raise_vec(v);
                    continue;
                }
                if (ln[0] == '+' || ln[0] == '-') {   /* "+01" / "-01": hold / release 0x50000106 input bits */
                    uint32_t m = strtoul(ln + 1, NULL, 16);
                    fprintf(stderr, "[k10d] msg-file -> %s lines 0x%02x on 0x50000106\n", ln[0] == '+' ? "hold" : "release", m);
                    k10d_cpucom_hold_lines(ln[0] == '+' ? m : 0, ln[0] == '-' ? m : 0);
                    continue;
                }
                uint8_t pl[80]; int k = 0; char *s = ln + 1;
                while (*s && k < 80) {
                    while (*s == ' ' || *s == ',') s++;
                    unsigned v; if (sscanf(s, "%2x", &v) != 1) break;
                    pl[k++] = v; s += 2;
                }
                fprintf(stderr, "[k10d] msg-file -> '%c' (%d payload bytes)\n", ln[0], k);
                k10d_cpucom_post_msg(ln[0], pl, k);
            }
        }
    }
    timer_mod(rec_timer, qemu_clock_get_ms(QEMU_CLOCK_REALTIME) + 100);
}

void k10d_display_init(void)
{
    if (getenv("FRN_REC_FILE") || getenv("FRN_MSG_FILE")) {
        rec_timer = timer_new_ms(QEMU_CLOCK_REALTIME, k10d_rec_file_poll, NULL);
        timer_mod(rec_timer, qemu_clock_get_ms(QEMU_CLOCK_REALTIME) + 100);
    }
    con = qemu_graphic_console_create(NULL, 0, &k10d_display_ops, NULL);
    qemu_console_resize(con, W, H);
    QemuInputHandlerState *hs = qemu_input_handler_register(NULL, &k10d_key_handler);
    qemu_input_handler_activate(hs);
}
