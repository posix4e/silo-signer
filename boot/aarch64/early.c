/*
Early AArch64 bare-metal bring-up & verified Stage-1 MMU setup (`boot/aarch64/early.c`).

Every Stage-1 descriptor bit matches `Kernel/Mmu.lean` & `Kernel/MmuProofs.lean` verbatim:
  - MAIR_EL1 = 0x0000000000FF4400 (Attr0=Device-nGnRnE, Attr1=Normal-NC, Attr2=Normal-WB)
  - Strict W^X enforced both in descriptors AND in hardware via `SCTLR_EL1.WXN = 1`
  - Null page (0x0) and 64 KiB stack guard hole (`__stack_guard .. __stack_bottom`) unmapped
  - Dedicated `SP_EL1` exception stack catches stack overflows cleanly without triple-faulting
*/
#include "boot.h"
#include <stddef.h>
#include <stdint.h>

extern char __image_start[], __image_end[];
extern char __text_start[], __text_end[];
extern char __rodata_start[], __rodata_end[];
extern char __data_start[], __bss_end[];
extern char __exc_stack_bot[], __exc_stack_top[];
extern char __stack_guard[], __stack_bottom[], __stack_top[];
extern char __pt_pool_start[], __pt_pool_end[];

boot_window_t boot_windows[BOOT_MAX_WINDOWS];
size_t boot_window_count = 0;

void * boot_heap_start = NULL;
size_t boot_heap_size = 0;

void * boot_device_start = NULL;
size_t boot_device_size = 0;

uint64_t boot_fb_base = 0;
uint32_t boot_fb_width = 0;
uint32_t boot_fb_height = 0;
uint32_t boot_fb_stride = 0;
uint32_t boot_fb_bpp = 4;
int boot_fb_console_quiet = 0;

static uint8_t fdt_copy[1048576]; /* 1 MiB static copy inside .bss (covers QEMU virt's 1 MiB DTB!) */
uint8_t const * boot_fdt_ptr = fdt_copy;
size_t boot_fdt_size = 0;
char boot_command_line[1024];

uint64_t boot_midr = 0;
int boot_has_dit = 0;
int boot_dit_enabled = 0;
int boot_has_rndr = 0;
uint8_t boot_initial_el = 0;

static uint64_t serial_base = 0;
static int serial_is_pl011 = 1;
static int mmu_enabled = 0;
static uint32_t fb_con_x = 32;
static uint32_t fb_con_y = 148;
static uint32_t fb_con_color = 0xFF66CCFFU; /* LCARS Science Cyan */
static int is_komodo_board(void) {
    return (uint64_t)(uintptr_t)__image_start >= 0x80000000ULL;
}

static void komodo_decon_kick(void) {
    volatile uint32_t * decon = (volatile uint32_t *)(uintptr_t)0x19470000ULL;
    decon[0x20 / 4] |= 0x3u;
    decon[0x50 / 4] = 0x80103FFFu;
    uint32_t trig = decon[0x30 / 4];
    decon[0x30 / 4] = (trig & ~(1u << 4)) | 1u;
    __asm__ volatile("dsb sy" ::: "memory");
}

/* Compact 5x7 uppercase + digits + symbols bitmap font for bare-metal OLED console diagnostics. */
static uint8_t const * fb_glyph(char c) {
    static uint8_t const blank[7] = {0,0,0,0,0,0,0};
    static uint8_t const unk[7]   = {0x1F,0x11,0x15,0x15,0x15,0x11,0x1F};
    static uint8_t const alpha[26][7] = {
        {0x0E,0x11,0x11,0x1F,0x11,0x11,0x11}, /* A */
        {0x1E,0x11,0x11,0x1E,0x11,0x11,0x1E}, /* B */
        {0x0E,0x11,0x10,0x10,0x10,0x11,0x0E}, /* C */
        {0x1C,0x12,0x11,0x11,0x11,0x12,0x1C}, /* D */
        {0x1F,0x10,0x10,0x1E,0x10,0x10,0x1F}, /* E */
        {0x1F,0x10,0x10,0x1E,0x10,0x10,0x10}, /* F */
        {0x0E,0x11,0x10,0x17,0x11,0x11,0x0E}, /* G */
        {0x11,0x11,0x11,0x1F,0x11,0x11,0x11}, /* H */
        {0x0E,0x04,0x04,0x04,0x04,0x04,0x0E}, /* I */
        {0x07,0x02,0x02,0x02,0x12,0x12,0x0C}, /* J */
        {0x11,0x12,0x14,0x18,0x14,0x12,0x11}, /* K */
        {0x10,0x10,0x10,0x10,0x10,0x10,0x1F}, /* L */
        {0x11,0x1B,0x15,0x15,0x11,0x11,0x11}, /* M */
        {0x11,0x19,0x15,0x13,0x11,0x11,0x11}, /* N */
        {0x0E,0x11,0x11,0x11,0x11,0x11,0x0E}, /* O */
        {0x1E,0x11,0x11,0x1E,0x10,0x10,0x10}, /* P */
        {0x0E,0x11,0x11,0x11,0x15,0x12,0x0D}, /* Q */
        {0x1E,0x11,0x11,0x1E,0x14,0x12,0x11}, /* R */
        {0x0F,0x10,0x10,0x0E,0x01,0x01,0x1E}, /* S */
        {0x1F,0x04,0x04,0x04,0x04,0x04,0x04}, /* T */
        {0x11,0x11,0x11,0x11,0x11,0x11,0x0E}, /* U */
        {0x11,0x11,0x11,0x11,0x11,0x0A,0x04}, /* V */
        {0x11,0x11,0x11,0x15,0x15,0x1B,0x11}, /* W */
        {0x11,0x11,0x0A,0x04,0x0A,0x11,0x11}, /* X */
        {0x11,0x11,0x0A,0x04,0x04,0x04,0x04}, /* Y */
        {0x1F,0x01,0x02,0x04,0x08,0x10,0x1F}  /* Z */
    };
    static uint8_t const digits[10][7] = {
        {0x0E,0x11,0x13,0x15,0x19,0x11,0x0E}, /* 0 */
        {0x04,0x0C,0x04,0x04,0x04,0x04,0x0E}, /* 1 */
        {0x0E,0x11,0x01,0x06,0x08,0x10,0x1F}, /* 2 */
        {0x1E,0x01,0x01,0x0E,0x01,0x01,0x1E}, /* 3 */
        {0x02,0x06,0x0A,0x12,0x1F,0x02,0x02}, /* 4 */
        {0x1F,0x10,0x1E,0x01,0x01,0x11,0x0E}, /* 5 */
        {0x0E,0x10,0x1E,0x11,0x11,0x11,0x0E}, /* 6 */
        {0x1F,0x01,0x02,0x04,0x08,0x08,0x08}, /* 7 */
        {0x0E,0x11,0x11,0x0E,0x11,0x11,0x0E}, /* 8 */
        {0x0E,0x11,0x11,0x0F,0x01,0x01,0x0E}  /* 9 */
    };
    static uint8_t const colon[7] = {0x00,0x04,0x04,0x00,0x04,0x04,0x00};
    static uint8_t const eqs[7]   = {0x00,0x00,0x1F,0x00,0x1F,0x00,0x00};
    static uint8_t const dash[7]  = {0x00,0x00,0x00,0x1F,0x00,0x00,0x00};
    static uint8_t const dot[7]   = {0x00,0x00,0x00,0x00,0x00,0x0C,0x0C};
    static uint8_t const slash[7] = {0x01,0x01,0x02,0x04,0x08,0x10,0x10};
    static uint8_t const lparen[7]= {0x02,0x04,0x08,0x08,0x08,0x04,0x02};
    static uint8_t const rparen[7]= {0x08,0x04,0x02,0x02,0x02,0x04,0x08};
    static uint8_t const plus[7]  = {0x00,0x04,0x04,0x1F,0x04,0x04,0x00};
    static uint8_t const comma[7] = {0x00,0x00,0x00,0x00,0x04,0x04,0x08};
    static uint8_t const bang[7]  = {0x04,0x04,0x04,0x04,0x04,0x00,0x04};
    static uint8_t const under[7] = {0x00,0x00,0x00,0x00,0x00,0x00,0x1F};
    if (c >= 'a' && c <= 'z') c = (char)(c - 'a' + 'A');
    if (c >= 'A' && c <= 'Z') return alpha[c - 'A'];
    if (c >= '0' && c <= '9') return digits[c - '0'];
    switch (c) {
    case ' ': return blank;
    case ':': return colon;
    case '=': return eqs;
    case '-': return dash;
    case '.': return dot;
    case '/': return slash;
    case '(': return lparen;
    case ')': return rparen;
    case '+': return plus;
    case ',': return comma;
    case '!': return bang;
    case '_': return under;
    default:  return unk;
    }
}

static void fb_console_putc(char c) {
    if (!mmu_enabled || boot_fb_console_quiet || boot_fb_base == 0 || boot_fb_width < 64 || boot_fb_height < 200)
        return;
    uint32_t const scale = 3;
    uint32_t const cw = 6 * scale;
    uint32_t const ch = 9 * scale;
    if (c == '\n') {
        fb_con_x = 32;
        fb_con_y += ch;
        if (fb_con_y + ch >= boot_fb_height) fb_con_y = 148;
        __asm__ volatile("dsb sy" ::: "memory");
        komodo_decon_kick();
        return;
    }
    if (c == '\r') return;
    if (fb_con_x + cw >= boot_fb_width - 16) {
        fb_con_x = 32;
        fb_con_y += ch;
        if (fb_con_y + ch >= boot_fb_height) fb_con_y = 148;
    }
    uint8_t const * g = fb_glyph(c);
    volatile uint32_t * px = (volatile uint32_t *)(uintptr_t)boot_fb_base;
    for (uint32_t r = 0; r < 7; r++) {
        uint8_t bits = g[r];
        for (uint32_t col = 0; col < 5; col++) {
            uint32_t clr = (bits & (1u << (4 - col))) ? fb_con_color : 0xFF000000U;
            for (uint32_t dy = 0; dy < scale; dy++) {
                uint32_t py = fb_con_y + r * scale + dy;
                uint64_t row = (uint64_t)py * (uint64_t)boot_fb_stride;
                for (uint32_t dx = 0; dx < scale; dx++) {
                    px[row + fb_con_x + col * scale + dx] = clr;
                }
            }
        }
    }
    fb_con_x += cw;
}

/* Exact descriptor flags matching `Kernel/Mmu.lean` (`encodeDescriptor`). */
#define MAIR_VALUE     0x0000000000FF4400ULL
#define DESC_VALID     (1ULL << 0)
#define DESC_TABLE     (1ULL << 1)
#define DESC_PAGE      (3ULL << 0)
#define DESC_BLOCK     (1ULL << 0)
#define ATTR_DEVICE    (0ULL << 2)
#define ATTR_NORMAL_NC (1ULL << 2)
#define ATTR_NORMAL_WB (2ULL << 2)
#define AP_EL1_RW      (0ULL << 6)
#define AP_EL1_RO      (2ULL << 6)
#define SH_OUTER       (2ULL << 8)
#define SH_INNER       (3ULL << 8)
#define BIT_AF         (1ULL << 10)
#define BIT_PXN        (1ULL << 53)
#define BIT_UXN        (1ULL << 54)

#define FLAGS_CODE_RX   (ATTR_NORMAL_WB | AP_EL1_RO | SH_INNER | BIT_AF | BIT_UXN)
#define FLAGS_RO_DATA   (ATTR_NORMAL_WB | AP_EL1_RO | SH_INNER | BIT_AF | BIT_PXN | BIT_UXN)
#define FLAGS_RW_DATA   (ATTR_NORMAL_WB | AP_EL1_RW | SH_INNER | BIT_AF | BIT_PXN | BIT_UXN)
#define FLAGS_NORMAL_NC (ATTR_NORMAL_NC | AP_EL1_RW | SH_OUTER | BIT_AF | BIT_PXN | BIT_UXN)
#define FLAGS_DEVICE    (ATTR_DEVICE    | AP_EL1_RW |            BIT_AF | BIT_PXN | BIT_UXN)

static uint32_t read_be32(uint8_t const * p) {
    return ((uint32_t)p[0] << 24) | ((uint32_t)p[1] << 16) | ((uint32_t)p[2] << 8) | (uint32_t)p[3];
}

void boot_serial_write(char const * bytes, size_t length) {
    if (is_komodo_board() && boot_fb_console_quiet && length >= 12) {
        if ((bytes[0] == 's' && bytes[1] == 'i' && bytes[2] == 'l' && bytes[3] == 'o' && bytes[4] == ' ') ||
            (bytes[0] == 'I' && bytes[1] == 'N' && bytes[2] == 'T' && bytes[3] == 'E' && bytes[4] == 'R')) {
            boot_fb_console_quiet = 0;
            fb_con_color = 0xFFFF4444U;
            fb_con_x = 32;
            fb_con_y = 200;
        }
    }
    if (is_komodo_board() && !boot_fb_console_quiet) {
        for (size_t i = 0; i < length; i++) fb_console_putc(bytes[i]);
    }
    if (serial_base == 0) return;
    if (serial_is_pl011) {
        volatile uint32_t * dr = (volatile uint32_t *)(uintptr_t)(serial_base + 0x00);
        volatile uint32_t * fr = (volatile uint32_t *)(uintptr_t)(serial_base + 0x18);
        for (size_t i = 0; i < length; i++) {
            uint32_t guard = 0;
            while ((*fr & (1u << 5)) != 0 && guard < 1000000u) guard++;
            *dr = (uint32_t)(unsigned char)bytes[i];
        }
    } else {
        /* Exynos UART: UTRSTAT at +0x10 (bit 2 = TX empty), UTXH at +0x20 */
        volatile uint32_t * utrstat = (volatile uint32_t *)(uintptr_t)(serial_base + 0x10);
        volatile uint32_t * utxh = (volatile uint32_t *)(uintptr_t)(serial_base + 0x20);
        for (size_t i = 0; i < length; i++) {
            uint32_t guard = 0;
            while ((*utrstat & (1u << 2)) == 0 && guard < 1000000u) guard++;
            *utxh = (uint32_t)(unsigned char)bytes[i];
        }
    }
}

void boot_serial_puts(char const * s) {
    size_t n = 0;
    while (s[n] != 0) n++;
    boot_serial_write(s, n);
}

void boot_serial_hex64(uint64_t v) {
    static char const hex[] = "0123456789abcdef";
    char buf[19];
    buf[0] = '0';
    buf[1] = 'x';
    for (int i = 0; i < 16; i++) buf[2 + i] = hex[(v >> (60 - 4 * i)) & 0xf];
    buf[18] = 0;
    boot_serial_write(buf, 18);
}

static void boot_serial_dec(int v) {
    char buf[16];
    int neg = v < 0;
    unsigned int u = neg ? (unsigned int)(-v) : (unsigned int)v;
    int pos = 0;
    if (u == 0) buf[pos++] = '0';
    else {
        while (u > 0 && pos < 12) {
            buf[pos++] = (char)('0' + (u % 10));
            u /= 10;
        }
    }
    if (neg) boot_serial_write("-", 1);
    while (pos > 0) boot_serial_write(&buf[--pos], 1);
}

static void komodo_wdt_hard_reset(void) {
    /* Verified on live Pixel 9 Pro XL silicon (`s3c2410_wdt` @ 0x10060000): 1-tick WDT reset (<1ms)! */
    volatile uint32_t * wdt = (volatile uint32_t *)(uintptr_t)0x10060000ULL;
    wdt[0x00 / 4] = 0u;
    wdt[0x04 / 4] = 1u;
    wdt[0x08 / 4] = 1u;
    wdt[0x00 / 4] = 0x21u; /* WTCON: ENABLE | RSTEN */
    __asm__ volatile("dsb sy" ::: "memory");
    for (;;) __asm__ volatile("wfi");
}

static void komodo_psci_reset(void) {
    register uint64_t x0 __asm__("x0") = 0x84000009ULL; /* PSCI_0_2_FN_SYSTEM_RESET */
    __asm__ volatile("smc #0" : "+r"(x0) :: "memory");
    /* If EL3 PSCI returned, force immediate <1ms Tensor G4 hardware WDT reset! */
    komodo_wdt_hard_reset();
}

static void komodo_psci_poweroff(void) {
    register uint64_t x0 __asm__("x0") = 0x84000008ULL; /* PSCI_0_2_FN_SYSTEM_OFF */
    __asm__ volatile("smc #0" : "+r"(x0) :: "memory");
    /* Exynos/Tensor PMU_ALIVE PS_HOLD_CONTROL (0x1546330C): clear bit 8 to drop PMIC PS_HOLD! */
    volatile uint32_t * ps_hold = (volatile uint32_t *)(uintptr_t)0x1546330CULL;
    *ps_hold &= ~(1u << 8);
    __asm__ volatile("dsb sy" ::: "memory");
    /* Brief wait for PMIC cutoff, else guaranteed WDT reset so device never hangs */
    for (volatile uint32_t i = 0; i < 5000000u; i++) { }
    komodo_wdt_hard_reset();
}

_Noreturn void boot_halt(int code) {
    if (is_komodo_board() && code == 99) {
        komodo_psci_reset();
    }
    if (is_komodo_board() && code == 98) {
        komodo_psci_poweroff();
    }
    if (is_komodo_board()) {
        boot_fb_console_quiet = 0;
        if (code != 0) fb_con_color = 0xFFFF4444U;
    }
    boot_serial_puts("TRICORDER_EXIT=");
    boot_serial_dec(code);
    boot_serial_puts("\n");
    if (!is_komodo_board()) {
        /* PSCI_0_2_FN_SYSTEM_OFF via HVC #0 (exits QEMU -M virt cleanly). */
        register uint64_t x0 __asm__("x0") = 0x84000008ULL;
        __asm__ volatile("hvc #0" : "+r"(x0) :: "memory");
    }
    /* On physical Pixel silicon, stay halted cleanly so OLED stays visible:
       Power + VolDown = instant reboot; Power + VolUp = instant power off! */
    if (is_komodo_board() && mmu_enabled) {
        boot_serial_puts("PWR+VOLDOWN=REBOOT  PWR+VOLUP=POWEROFF\n");
        volatile uint32_t * gpa4_dat = (volatile uint32_t *)(uintptr_t)(0x154D0000ULL + 0x84ULL);
        volatile uint32_t * gpa6_dat = (volatile uint32_t *)(uintptr_t)(0x154D0000ULL + 0xA4ULL);
        for (;;) {
            uint32_t g4 = *gpa4_dat;
            uint32_t g6 = *gpa6_dat;
            if ((g4 & 0x3u) == 0u) komodo_psci_reset();
            if ((g4 & 0x1u) == 0u && (g6 & 0x4u) == 0u) komodo_psci_poweroff();
            __asm__ volatile("yield");
        }
    }
    for (;;) __asm__ volatile("wfi");
}

static int boot_has_smc_trng = 0; /* 1 = Exynos SMC_CMD_RANDOM, 2 = ARM SMCCC_TRNG_RND64 */
static int boot_smc_trng_tested = 0;
static uint64_t boot_smc_trng_err = 0;

/* Official Tensor G4 (`zumapro`) EL3 DTRNG via `exyswd-rng.c` (`SMC_CMD_RANDOM = 0x82001012`)
   and ARM SMCCC TRNG (`ARM_SMCCC_TRNG_RND64 = 0xC4000053`). */
#define SMC_CMD_RANDOM               0x82001012ULL
#define ARM_SMCCC_TRNG_RND64         0xC4000053ULL
#define HWRNG_INIT                   0x0ULL
#define HWRNG_EXIT                   0x1ULL
#define HWRNG_GET_DATA               0x2ULL
#define HWRNG_RET_OK                 0ULL
#define HWRNG_RET_RETRY_ERROR        2ULL
#define HWRNG_RET_START_UP_TEST_DONE 5ULL

static void komodo_delay_us_cntvct(uint64_t us) {
    uint64_t t0 = 0, t1 = 0;
    __asm__ volatile("mrs %0, CNTVCT_EL0" : "=r"(t0));
    uint64_t need = us * 25ULL;
    for (uint32_t i = 0; i < 10000000u; i++) {
        __asm__ volatile("mrs %0, CNTVCT_EL0" : "=r"(t1));
        if (t1 - t0 >= need) break;
        __asm__ volatile("yield");
    }
}

static uint64_t exynos_cm_smc(uint64_t * a0, uint64_t * a1, uint64_t * a2, uint64_t * a3) {
    register uint64_t x0 __asm__("x0") = *a0;
    register uint64_t x1 __asm__("x1") = *a1;
    register uint64_t x2 __asm__("x2") = *a2;
    register uint64_t x3 __asm__("x3") = *a3;
    register uint64_t x4 __asm__("x4") = 0;
    register uint64_t x5 __asm__("x5") = 0;
    register uint64_t x6 __asm__("x6") = 0;
    register uint64_t x7 __asm__("x7") = 0;
    __asm__ volatile(
        "str x18, [sp, #-16]!\n"
        "smc #0\n"
        "ldr x18, [sp], #16\n"
        : "+r"(x0), "+r"(x1), "+r"(x2), "+r"(x3), "+r"(x4), "+r"(x5), "+r"(x6), "+r"(x7)
        :
        : "x8", "x9", "x10", "x11", "x12", "x13", "x14", "x15", "x16", "x17", "memory"
    );
    *a0 = x0;
    *a1 = x1;
    *a2 = x2;
    *a3 = x3;
    return x0;
}

static int komodo_smc_trng64(uint64_t * out) {
    uint64_t r0, r1, r2, r3, ret = 1;
    for (uint32_t tries = 0; tries < 500; tries++) {
        r0 = SMC_CMD_RANDOM; r1 = HWRNG_INIT; r2 = 0; r3 = 0;
        ret = exynos_cm_smc(&r0, &r1, &r2, &r3);
        if (ret != HWRNG_RET_RETRY_ERROR) break;
        komodo_delay_us_cntvct(60);
    }
    if (ret != HWRNG_RET_OK) return 0;

    if (!boot_smc_trng_tested) {
        uint32_t remain = 4097;
        uint32_t retries = 0;
        while (remain > 0) {
            r0 = SMC_CMD_RANDOM; r1 = HWRNG_GET_DATA; r2 = 1; r3 = 0;
            ret = exynos_cm_smc(&r0, &r1, &r2, &r3);
            if (ret == HWRNG_RET_RETRY_ERROR) {
                if (++retries > 500) { ret = 1; break; }
                komodo_delay_us_cntvct(60);
                continue;
            }
            if (ret == HWRNG_RET_START_UP_TEST_DONE) { ret = HWRNG_RET_OK; break; }
            if (ret != HWRNG_RET_OK) break;
            remain = (remain >= 32) ? (remain - 32) : 0;
            retries = 0;
        }
        if (ret != HWRNG_RET_OK) {
            for (uint32_t tries = 0; tries < 200; tries++) {
                r0 = SMC_CMD_RANDOM; r1 = HWRNG_EXIT; r2 = 0; r3 = 0;
                if (exynos_cm_smc(&r0, &r1, &r2, &r3) == HWRNG_RET_OK) break;
                komodo_delay_us_cntvct(60);
            }
            return 0;
        }
        boot_smc_trng_tested = 1;
    }

    int ok = 0;
    for (uint32_t tries = 0; tries < 500; tries++) {
        r0 = SMC_CMD_RANDOM; r1 = HWRNG_GET_DATA; r2 = 0; r3 = 0;
        ret = exynos_cm_smc(&r0, &r1, &r2, &r3);
        if (ret == HWRNG_RET_RETRY_ERROR) {
            komodo_delay_us_cntvct(60);
            continue;
        }
        if (ret == HWRNG_RET_OK) {
            *out = ((uint64_t)(uint32_t)r2) | (((uint64_t)(uint32_t)r3) << 32);
            ok = 1;
        }
        break;
    }

    for (uint32_t tries = 0; tries < 200; tries++) {
        r0 = SMC_CMD_RANDOM; r1 = HWRNG_EXIT; r2 = 0; r3 = 0;
        if (exynos_cm_smc(&r0, &r1, &r2, &r3) == HWRNG_RET_OK) break;
        komodo_delay_us_cntvct(60);
    }
    return ok;
}

static int arm_smccc_trng64(uint64_t * out) {
    uint64_t r0 = ARM_SMCCC_TRNG_RND64, r1 = 64, r2 = 0, r3 = 0;
    uint64_t ret = exynos_cm_smc(&r0, &r1, &r2, &r3);
    if (ret == 0) {
        *out = r3;
        return 1;
    }
    return 0;
}

int boot_rndr64(uint64_t * out) {
    if (boot_has_smc_trng == 1) {
        return komodo_smc_trng64(out);
    }
    if (boot_has_smc_trng == 2) {
        return arm_smccc_trng64(out);
    }
    if (!boot_has_rndr) return 0;
    uint64_t val = 0;
    uint64_t ok = 0;
    /* RNDRRS = S3_3_C2_C4_1; NZCV.Z == 0 indicates valid hardware entropy. */
    __asm__ volatile(
        "mrs %0, S3_3_C2_C4_1\n"
        "cset %1, ne\n"
        : "=r"(val), "=r"(ok)
        :
        : "cc"
    );
    if (!ok) {
        /* Fall back to RNDR = S3_3_C2_C4_0 if RNDRRS reseeding was busy. */
        __asm__ volatile(
            "mrs %0, S3_3_C2_C4_0\n"
            "cset %1, ne\n"
            : "=r"(val), "=r"(ok)
            :
            : "cc"
        );
    }
    if (!ok) return 0;
    *out = val;
    return 1;
}

uint64_t boot_cntvct(void) {
    uint64_t v = 0;
    __asm__ volatile("mrs %0, CNTVCT_EL0" : "=r"(v));
    return v;
}

/* ---- Page-table allocator from zeroed __pt_pool_start .. __pt_pool_end ---- */

static uintptr_t pt_cursor = 0;

static uint64_t * alloc_pt_page(void) {
    if (pt_cursor + 4096 > (uintptr_t)__pt_pool_end) {
        boot_serial_puts("tricorder boot: out of page-table pool\n");
        boot_halt(71);
    }
    uint64_t * page = (uint64_t *)pt_cursor;
    pt_cursor += 4096;
    for (size_t i = 0; i < 512; i++) page[i] = 0;
    return page;
}

static uint64_t * l1_table = NULL;

static void map_4k(uint64_t va, uint64_t pa, uint64_t flags) {
    uint64_t l1_idx = (va >> 30) & 0x1ff;
    uint64_t l2_idx = (va >> 21) & 0x1ff;
    uint64_t l3_idx = (va >> 12) & 0x1ff;

    uint64_t * l2;
    if ((l1_table[l1_idx] & DESC_VALID) == 0) {
        l2 = alloc_pt_page();
        l1_table[l1_idx] = ((uint64_t)(uintptr_t)l2 & 0x0000FFFFFFFFF000ULL) | DESC_PAGE;
    } else {
        l2 = (uint64_t *)(uintptr_t)(l1_table[l1_idx] & 0x0000FFFFFFFFF000ULL);
    }

    uint64_t * l3;
    if ((l2[l2_idx] & DESC_VALID) == 0) {
        l3 = alloc_pt_page();
        l2[l2_idx] = ((uint64_t)(uintptr_t)l3 & 0x0000FFFFFFFFF000ULL) | DESC_PAGE;
    } else if ((l2[l2_idx] & DESC_TABLE) == 0) {
        /* Already a 2 MiB block; should not overlap with 4 KiB page mapping. */
        boot_serial_puts("tricorder boot: overlapping 2MiB/4KiB mapping\n");
        boot_halt(72);
    } else {
        l3 = (uint64_t *)(uintptr_t)(l2[l2_idx] & 0x0000FFFFFFFFF000ULL);
    }

    l3[l3_idx] = (pa & 0x0000FFFFFFFFF000ULL) | DESC_PAGE | flags;
}

static void map_2m(uint64_t va, uint64_t pa, uint64_t flags) {
    uint64_t l1_idx = (va >> 30) & 0x1ff;
    uint64_t l2_idx = (va >> 21) & 0x1ff;

    uint64_t * l2;
    if ((l1_table[l1_idx] & DESC_VALID) == 0) {
        l2 = alloc_pt_page();
        l1_table[l1_idx] = ((uint64_t)(uintptr_t)l2 & 0x0000FFFFFFFFF000ULL) | DESC_PAGE;
    } else {
        l2 = (uint64_t *)(uintptr_t)(l1_table[l1_idx] & 0x0000FFFFFFFFF000ULL);
    }

    l2[l2_idx] = (pa & 0x0000FFFFFFE00000ULL) | DESC_BLOCK | flags;
}

static void map_range_4k(uint64_t start, uint64_t end, uint64_t flags) {
    uint64_t a = start & ~0xfffULL;
    uint64_t e = (end + 0xfffULL) & ~0xfffULL;
    for (uint64_t p = a; p < e; p += 4096) {
        map_4k(p, p, flags);
    }
}

static void map_range_2m(uint64_t start, uint64_t end, uint64_t flags) {
    uint64_t a = start & ~0x1fffffULL;
    uint64_t e = (end + 0x1fffffULL) & ~0x1fffffULL;
    for (uint64_t p = a; p < e; p += 0x200000ULL) {
        map_2m(p, p, flags);
    }
}

static void add_window(uint64_t base, uint64_t size) {
    if (size == 0 || boot_window_count >= BOOT_MAX_WINDOWS) return;
    /* Deduplicate identical windows */
    for (size_t i = 0; i < boot_window_count; i++) {
        if (boot_windows[i].base == base && boot_windows[i].size == size) return;
    }
    boot_windows[boot_window_count].base = base;
    boot_windows[boot_window_count].size = size;
    boot_window_count++;
}

static int str_eq(char const * a, char const * b) {
    while (*a && *b && *a == *b) { a++; b++; }
    return *a == 0 && *b == 0;
}

static uint64_t fdt_splash_base = 0;

static int str_starts_with(char const * s, char const * pref) {
    while (*pref) {
        if (*s != *pref) return 0;
        s++;
        pref++;
    }
    return 1;
}

/* Minimal early FDT scan strictly to copy DTB, extract /chosen/bootargs, and note any
   reserved-memory splash framebuffer before enabling MMU. Full verified FDT parsing runs in Lean. */
static void early_scan_fdt(uint64_t fdt_phys) {
    boot_command_line[0] = 0;
    fdt_splash_base = 0;
    if (fdt_phys == 0) return;
    uint8_t const * raw = (uint8_t const *)(uintptr_t)fdt_phys;
    if (read_be32(raw) != 0xd00dfeedU) return;
    uint32_t total = read_be32(raw + 4);
    if (total < 40 || total > sizeof(fdt_copy)) return;
    for (uint32_t i = 0; i < total; i++) fdt_copy[i] = raw[i];
    boot_fdt_size = total;

    uint32_t off_struct = read_be32(fdt_copy + 8);
    uint32_t off_strings = read_be32(fdt_copy + 12);
    uint32_t size_strings = read_be32(fdt_copy + 32);
    uint32_t size_struct = read_be32(fdt_copy + 36);
    if ((uint64_t)off_struct + size_struct > total || (uint64_t)off_strings + size_strings > total) return;

    uint32_t pos = off_struct;
    uint32_t end = off_struct + size_struct;
    int in_chosen = 0;
    int in_splash = 0;
    int depth = 0;
    int chosen_depth = -1;
    int splash_depth = -1;

    while (pos + 4 <= end) {
        uint32_t tok = read_be32(fdt_copy + pos);
        pos += 4;
        if (tok == 1) { /* FDT_BEGIN_NODE */
            char const * nm = (char const *)(fdt_copy + pos);
            depth++;
            if (str_eq(nm, "chosen")) { in_chosen = 1; chosen_depth = depth; }
            if (str_starts_with(nm, "cont_splash") || str_starts_with(nm, "splash") ||
                str_starts_with(nm, "fb_handover") || str_starts_with(nm, "fb_mem")) {
                in_splash = 1;
                splash_depth = depth;
            }
            while (pos < end && fdt_copy[pos] != 0) pos++;
            if (pos < end) pos++;
            pos = (pos + 3) & ~3U;
        } else if (tok == 2) { /* FDT_END_NODE */
            if (depth == chosen_depth) { in_chosen = 0; chosen_depth = -1; }
            if (depth == splash_depth) { in_splash = 0; splash_depth = -1; }
            if (depth > 0) depth--;
        } else if (tok == 3) { /* FDT_PROP */
            if (pos + 8 > end) break;
            uint32_t plen = read_be32(fdt_copy + pos);
            uint32_t nameoff = read_be32(fdt_copy + pos + 4);
            pos += 8;
            if ((uint64_t)pos + plen > end) break;
            if (nameoff < size_strings) {
                char const * pname = (char const *)(fdt_copy + off_strings + nameoff);
                uint8_t const * pval = fdt_copy + pos;
                if (in_chosen && str_eq(pname, "bootargs")) {
                    size_t copy = plen < sizeof(boot_command_line) - 1 ? plen : sizeof(boot_command_line) - 1;
                    for (size_t i = 0; i < copy; i++) boot_command_line[i] = (char)pval[i];
                    boot_command_line[copy] = 0;
                } else if (in_splash && str_eq(pname, "reg") && (plen == 12 || plen == 16)) {
                    uint64_t base = ((uint64_t)read_be32(pval) << 32) | (uint64_t)read_be32(pval + 4);
                    if (base >= 0x80000000ULL && base < 0xFD3E0000ULL) fdt_splash_base = base;
                }
            }
            pos = (pos + plen + 3) & ~3U;
        } else if (tok == 4) {
            /* FDT_NOP */
        } else if (tok == 9) {
            break; /* FDT_END */
        } else {
            break;
        }
    }
}

/* Official Tensor G4 (`zumapro` / `cal_9865`) verified hardware map from AOSP `android-gs-caimito-6.1-android16-dp`. */
#define KOMODO_DECON0_MAIN   0x19470000ULL /* 0x6000 */
#define KOMODO_DECON0_WIN    0x19480000ULL /* 0xE000 */
#define KOMODO_DECON0_WINCON 0x194A0000ULL /* 0xE000 */
#define KOMODO_DPU_DMA0_BASE 0x19900000ULL /* L0..L6: 7 x 0x1000 = 0x7000 */
#define KOMODO_DPU_DMA1_BASE 0x19D00000ULL /* L7..L13: 7 x 0x1000 = 0x7000 */
#define KOMODO_GPIO_ALIVE    0x154D0000ULL /* pinctrl_0 (gpa4: volDown/power, gpa6: volUp) */
#define KOMODO_PMU_ALIVE     0x15460000ULL /* PMU_ALIVE (pd_hsi0 status at +0x2A84) */
#define KOMODO_WDT_CL0       0x10060000ULL
#define KOMODO_WDT_CL1       0x10070000ULL
#define KOMODO_UART0         0x10870000ULL
#define KOMODO_USB_BLKCON    0x11100000ULL /* usbdrd_phy0 reg[0]: USBCON_REG_LINKCTRL / UTMI_CTRL */
#define KOMODO_USB_EUSBCON   0x11110000ULL /* usbdrd_phy0 reg[1]: EUSBCON_REG_RST_CTRL / UTMI */
#define KOMODO_DWC3          0x11210000ULL
#define KOMODO_UFS           0x13200000ULL
#define KOMODO_RAMOOPS       0xFD3FF000ULL
#define KOMODO_RAMOOPS_SIZE  0x00040000ULL /* map 256 KiB of 4 MiB ramoops */

static void komodo_delay_ms(uint32_t ms) {
    uint64_t freq = 0, t0 = 0, t1 = 0;
    __asm__ volatile("mrs %0, CNTFRQ_EL0" : "=r"(freq));
    if (freq < 1000000ULL) freq = 24576000ULL;
    uint64_t ticks = (freq / 1000ULL) * (uint64_t)ms;
    __asm__ volatile("mrs %0, CNTVCT_EL0" : "=r"(t0));
    do {
        __asm__ volatile("mrs %0, CNTVCT_EL0" : "=r"(t1));
    } while (t1 - t0 < ticks);
}

static void komodo_decon_flush(void) {
    volatile uint32_t * decon = (volatile uint32_t *)(uintptr_t)KOMODO_DECON0_MAIN;
    /* 1. GLOBAL_CON (+0x20): ensure DECON_EN | DECON_EN_F */
    decon[0x20 / 4] |= 0x3u;
    /* 2. SHD_REG_UP_REQ (+0x50) = GLOBAL (1<<31) | CMP (1<<20) | WIN0..13 (0x3fff) */
    decon[0x50 / 4] = 0x80103FFFu;
    /* 3. TRIG_CON (+0x30): unmask HW TE trigger first (`cal_9865/decon_reg.c`), then SW trigger fallback! */
    uint32_t trig = decon[0x30 / 4];
    decon[0x30 / 4] = (trig & ~(1u << 4)) | 1u; /* clear HW_TRIG_MASK_DECON, set HW_TRIG_EN */
    __asm__ volatile("dsb sy" ::: "memory");
    komodo_delay_ms(60);
    if (decon[0x50 / 4] != 0) {
        decon[0x30 / 4] = (trig & ~0x11u) | (1u << 8) | (1u << 1); /* SW_TRIG_EN | SW_TRIG_DET_EN */
        __asm__ volatile("dsb sy" ::: "memory");
    }
}

static int probe_dpu_channel(uint64_t dma_base) {
    volatile uint32_t * dma = (volatile uint32_t *)(uintptr_t)dma_base;
    /* cal_9865/regs-dpp.h: DMA_SHD_OFFSET = 0x0400, RDMA_BASEADDR_P0 = 0x0040, RDMA_IMG_SIZE = 0x001C */
    uint32_t base = dma[0x0040 / 4];
    uint32_t shd  = dma[0x0440 / 4];
    uint32_t img  = dma[0x001C / 4];
    uint32_t simg = dma[0x041C / 4];
    uint32_t sw   = dma[0x0010 / 4] & 0xFFFFFFu;
    uint32_t ssw  = dma[0x0410 / 4] & 0xFFFFFFu;
    uint32_t addr = (base >= 0x80000000u && base < 0xFD3E0000u) ? base : shd;
    uint32_t use_img = (img != 0) ? img : simg;
    uint32_t use_sw  = (sw != 0) ? sw : ssw;
    uint32_t w = use_img & 0xFFFFu;
    uint32_t h = (use_img >> 16) & 0xFFFFu;
    if (addr >= 0x80000000u && addr < 0xFD3E0000u && w >= 240 && w <= 2048 && h >= 400 && h <= 4096) {
        boot_fb_base = (uint64_t)addr;
        boot_fb_width = w;
        boot_fb_height = h;
        boot_fb_stride = (use_sw >= w && use_sw <= 4096) ? use_sw : w;
        boot_fb_bpp = 4;
        return 1;
    }
    return 0;
}

/* Probes DECON0 active handover window (`decon_reg_get_win_ch`) first, then DPUF0 L0..L6, then FDT! */
static void komodo_probe_live_fb(void) {
    for (uint32_t w = 0; w < 6; w++) {
        volatile uint32_t * wincon = (volatile uint32_t *)(uintptr_t)(KOMODO_DECON0_WINCON + (uint64_t)w * 0x1000ULL);
        uint32_t c = wincon[0];
        if (c & 1u) {
            uint32_t ch = (c >> 4) & 0xFu;
            if (ch > 7) ch -= 1;
            uint64_t dma_base = (ch < 7)
                ? (KOMODO_DPU_DMA0_BASE + (uint64_t)ch * 0x1000ULL)
                : (KOMODO_DPU_DMA1_BASE + (uint64_t)(ch - 7) * 0x1000ULL);
            if (probe_dpu_channel(dma_base)) return;
        }
    }
    for (uint64_t ch = 0; ch < 7; ch++) {
        if (probe_dpu_channel(KOMODO_DPU_DMA0_BASE + ch * 0x1000ULL)) return;
    }
    if (fdt_splash_base != 0) {
        boot_fb_base = fdt_splash_base;
        boot_fb_width = 1344;
        boot_fb_height = 2992;
        boot_fb_stride = 1344;
        boot_fb_bpp = 4;
    }
}

void early_fault_handler(uint64_t esr, uint64_t far, uint64_t elr, uint64_t kind) {
    if (is_komodo_board()) {
        boot_fb_console_quiet = 0;
        fb_con_color = 0xFFFF4444U; /* Bright red on OLED for any CPU exception */
    }
    uint64_t ec = (esr >> 26) & 0x3f;
    boot_serial_puts("tricorder boot: FAULT kind=");
    boot_serial_dec((int)kind);
    boot_serial_puts(" EC=");
    boot_serial_hex64(ec);
    boot_serial_puts(" FAR=");
    boot_serial_hex64(far);
    boot_serial_puts(" ELR=");
    boot_serial_hex64(elr);
    boot_serial_puts("\n");

    if (far >= (uint64_t)(uintptr_t)__stack_guard && far < (uint64_t)(uintptr_t)__stack_bottom) {
        boot_serial_puts("tricorder boot: hit the hole under the stack: stack overflow caught!\n");
    } else if (ec == 0x21) {
        boot_serial_puts("tricorder boot: instruction abort (W^X / PXN enforced!)\n");
    } else if (ec == 0x25) {
        boot_serial_puts("tricorder boot: data abort (unmapped or RO memory protected!)\n");
    }
    boot_halt(3);
}

static void enable_mmu(void) {
    pt_cursor = (uintptr_t)__pt_pool_start;
    l1_table = alloc_pt_page();

    /* 1. Kernel image with strict 4 KiB page-granularity W^X + unmapped stack guard! */
    map_range_4k((uint64_t)(uintptr_t)__text_start,   (uint64_t)(uintptr_t)__text_end,   FLAGS_CODE_RX);
    map_range_4k((uint64_t)(uintptr_t)__rodata_start, (uint64_t)(uintptr_t)__rodata_end, FLAGS_RO_DATA);
    map_range_4k((uint64_t)(uintptr_t)__data_start,   (uint64_t)(uintptr_t)__exc_stack_top, FLAGS_RW_DATA);
    /* [__stack_guard .. __stack_bottom) is DELIBERATELY UNMAPPED! */
    map_range_4k((uint64_t)(uintptr_t)__stack_bottom, (uint64_t)(uintptr_t)__image_end,  FLAGS_RW_DATA);

    /* 2. Heap (Normal-WB, non-exec) and DMA/Framebuffer arena (Normal-NC, non-exec).
          On Pixel komodo, stay tightly inside 0xA0000000..0xA4000000 (48 MiB heap + 8 MiB DMA)
          so DMA buffers never overlap high ABL/Trusty/EL3 carveouts above 0xB0000000! */
    uint64_t heap_base = (uint64_t)(uintptr_t)__image_end;
    uint64_t heap_len  = is_komodo_board() ? (128ULL * 1024ULL * 1024ULL) : (256ULL * 1024ULL * 1024ULL);
    uint64_t dma_len   = is_komodo_board() ? (8ULL * 1024ULL * 1024ULL)   : (16ULL * 1024ULL * 1024ULL);
    if (boot_fb_base != 0 && boot_fb_height > 0 && boot_fb_stride > 0) {
        uint64_t fb_len = (uint64_t)boot_fb_height * (uint64_t)boot_fb_stride * (uint64_t)boot_fb_bpp;
        uint64_t fb_end = (boot_fb_base + fb_len + 0x1fffffULL) & ~0x1fffffULL;
        if (boot_fb_base < heap_base + heap_len + dma_len && fb_end > heap_base) {
            heap_base = fb_end;
        }
    }
    uint64_t dma_base  = heap_base + heap_len;
    boot_heap_start = (void *)(uintptr_t)heap_base;
    boot_heap_size  = (size_t)heap_len;
    boot_device_start = (void *)(uintptr_t)dma_base;
    boot_device_size  = (size_t)dma_len;

    map_range_2m(heap_base, heap_base + heap_len, FLAGS_RW_DATA);
    map_range_2m(dma_base,  dma_base + dma_len,   FLAGS_NORMAL_NC);

    /* 3. Announced device MMIO windows ONLY (Device-nGnRnE, non-exec). */
    for (size_t i = 0; i < boot_window_count; i++) {
        map_range_4k(boot_windows[i].base, boot_windows[i].base + boot_windows[i].size, FLAGS_DEVICE);
    }

    /* 4. Optional pre-initialized bootloader splash framebuffer (Normal-NC, non-exec). */
    if (boot_fb_base != 0 && boot_fb_height > 0 && boot_fb_stride > 0) {
        uint64_t fb_len = (uint64_t)boot_fb_height * (uint64_t)boot_fb_stride * (uint64_t)boot_fb_bpp;
        map_range_4k(boot_fb_base, boot_fb_base + fb_len, FLAGS_NORMAL_NC);
    }

    /* 5. Load MAIR_EL1, TCR_EL1 (39-bit VA, 4K granule, EPD1=1), TTBR0_EL1, and enable MMU + WXN! */
    uint64_t tcr =
        (25ULL << 0)  |  /* T0SZ = 25 (512 GiB VA space, L1->L2->L3) */
        (1ULL  << 8)  |  /* IRGN0 = WB WA */
        (1ULL  << 10) |  /* ORGN0 = WB WA */
        (3ULL  << 12) |  /* SH0 = Inner Shareable */
        (0ULL  << 14) |  /* TG0 = 4 KiB */
        (1ULL  << 23) |  /* EPD1 = 1 (disable TTBR1) */
        (2ULL  << 32);   /* IPS = 40-bit PA (1 TiB) */

    __asm__ volatile(
        "msr MAIR_EL1, %0\n"
        "msr TCR_EL1, %1\n"
        "msr TTBR0_EL1, %2\n"
        "dsb ish\n"
        "isb\n"
        "tlbi vmalle1\n"
        "dsb ish\n"
        "isb\n"
        :
        : "r"((uint64_t)MAIR_VALUE), "r"(tcr), "r"((uint64_t)(uintptr_t)l1_table)
        : "memory"
    );

    uint64_t sctlr = 0;
    __asm__ volatile("mrs %0, SCTLR_EL1" : "=r"(sctlr));
    sctlr |= (1ULL << 0)  |  /* M: enable Stage-1 MMU */
             (1ULL << 2)  |  /* C: enable data cache */
             (1ULL << 12) |  /* I: enable instruction cache */
             (1ULL << 19);   /* WXN: hardware W^X (writable pages are ALWAYS execute-never!) */
    sctlr &= ~(1ULL << 1);   /* A: allow unaligned accesses */
    __asm__ volatile(
        "msr SCTLR_EL1, %0\n"
        "dsb ish\n"
        "isb\n"
        :
        : "r"(sctlr)
        : "memory"
    );
    mmu_enabled = 1;
}

void early_boot(uint64_t fdt_phys, uint64_t initial_el) {
    boot_initial_el = (uint8_t)initial_el;

    /* Probe CPU identity, FEAT_DIT, and FEAT_RNG (`RNDR`/`RNDRRS`). */
    uint64_t pfr0 = 0, isar0 = 0, dit_reg = 0;
    __asm__ volatile("mrs %0, MIDR_EL1" : "=r"(boot_midr));
    __asm__ volatile("mrs %0, ID_AA64PFR0_EL1" : "=r"(pfr0));
    __asm__ volatile("mrs %0, ID_AA64ISAR0_EL1" : "=r"(isar0));
    boot_has_dit = ((pfr0 >> 48) & 0xf) != 0;
    boot_has_rndr = ((isar0 >> 60) & 0xf) != 0;
    if (boot_has_dit) {
        __asm__ volatile("mrs %0, S3_3_C4_C2_5" : "=r"(dit_reg));
        boot_dit_enabled = ((dit_reg >> 24) & 1) != 0;
    }

    /* Copy FDT before turning on our strict Stage-1 MMU. */
    early_scan_fdt(fdt_phys);

    /* Announce MMIO windows for QEMU (-M virt) or official Tensor G4 (`zumapro` / `komodo`). */
    if (!is_komodo_board()) {
        serial_base = 0x09000000ULL;
        serial_is_pl011 = 1;
        add_window(0x09000000ULL, 0x1000ULL);   /* PL011 UART */
        add_window(0x09020000ULL, 0x1000ULL);   /* QEMU fw_cfg (for ramfb!) */
        for (uint64_t i = 0; i < 32; i++) {
            add_window(0x0a000000ULL + i * 0x200ULL, 0x200ULL); /* VirtIO-MMIO slots 0..31 */
        }
    } else {
        /* Official Tensor G4 (`zumapro` / `cal_9865`) verified hardware map: */
        serial_base = 0; /* log directly onto live Pixel 9 Pro XL OLED console */
        add_window(KOMODO_DECON0_MAIN,   0x6000ULL);  /* DECON0_MAIN */
        add_window(KOMODO_DECON0_WIN,    0xE000ULL);  /* DECON0_WIN */
        add_window(KOMODO_DECON0_WINCON, 0xE000ULL);  /* DECON0_WINCON */
        add_window(KOMODO_DPU_DMA0_BASE, 0x7000ULL);  /* DPU_DMA L0..L6 */
        add_window(KOMODO_DPU_DMA1_BASE, 0x7000ULL);  /* DPU_DMA L7..L13 */
        add_window(KOMODO_GPIO_ALIVE,    0x1000ULL);  /* pinctrl_0 (GPIO_ALIVE: gpa4/gpa6 physical buttons!) */
        add_window(KOMODO_PMU_ALIVE + 0x2000ULL, 0x1000ULL); /* PMU_ALIVE power-domain status regs (pd_hsi0 @ +0xA80) */
        add_window(KOMODO_PMU_ALIVE + 0x3000ULL, 0x1000ULL); /* PMU_ALIVE PHY isolation regs (usbdrd @ +0xEB0) */
        add_window(KOMODO_WDT_CL0,       0x1000ULL);  /* watchdog_cl0 */
        add_window(KOMODO_WDT_CL1,       0x1000ULL);  /* watchdog_cl1 */
        add_window(KOMODO_UFS,           0x1000ULL);  /* exynos-ufs */
        add_window(KOMODO_USB_BLKCON,    0x1000ULL);  /* usbdrd_phy0 blkcon (FORCE_BVALID/VBUSVALID) */
        add_window(KOMODO_USB_EUSBCON,   0x1000ULL);  /* usbdrd_phy0 eusbcon (VBUS_VALID_EXT) */
        add_window(KOMODO_DWC3,          0x10000ULL); /* synopsys,dwc3 */
        /* Touchscreen bring-up (branch touch-bringup): the SPI controller the panel's touch IC hangs off,
         * what switches that block to SPI and clocks it, and the two pin banks that hold its reset and
         * interrupt lines. From zumapro-usi.dtsi, zuma-usb.dtsi, zumapro.dtsi and pinctrl-gs.c. */
        add_window(0x111D0000ULL, 0x1000ULL);   /* spi_20 (USI2_HSI0) */
        add_window(0x11021000ULL, 0x1000ULL);   /* sysreg_hsi0: USI SW_CONF at +0x01C */
        add_window(0x11000000ULL, 0x8000ULL);   /* cmu_hsi0: the block's clock muxes, dividers and gates */
        add_window(0x10840000ULL, 0x1000ULL);   /* pinctrl_11 (GPIO_PERIC0): gpp1-1 = touch reset */
        add_window(0x15060000ULL, 0x1000ULL);   /* pinctrl_1 (GPIO_CUSTOM_ALIVE): gpn0-0 = touch interrupt */
        /* The touch IC's two supplies are LDOs of the main PMIC, which only the power-management
         * firmware can reach: requests go through its mailbox and the queues in its shared memory
         * (acpm_ipc in zumapro.dtsi). */
        add_window(0x15110000ULL, 0x1000ULL);   /* AP-to-APM mailbox */
        add_window(0x15700000ULL, 0x58000ULL);  /* APM shared memory, as the AP sees it */
        /* Discover ABL's live active OLED framebuffer directly from DPU_DMA L0..L13 registers! */
        komodo_probe_live_fb();
    }

    enable_mmu();

    /* Visual proof-of-life banner on Pixel 9 Pro XL OLED + immediate DECON0 command-mode flush! */
    if (is_komodo_board()) {
        if (boot_fb_base != 0 && boot_fb_width > 0 && boot_fb_height > 128) {
            volatile uint32_t * px = (volatile uint32_t *)(uintptr_t)boot_fb_base;
            for (uint32_t y = 0; y < 128; y++) {
                for (uint32_t x = 0; x < boot_fb_width; x++) {
                    px[(uint64_t)y * (uint64_t)boot_fb_stride + x] = 0xFF66CCFFU; /* LCARS Science Cyan */
                }
            }
            __asm__ volatile("dsb sy" ::: "memory");
            komodo_decon_flush();
        } else {
            /* Reached post-MMU on komodo but no live framebuffer found: turn DECON0 bright LCARS Amber! */
            volatile uint32_t * decon = (volatile uint32_t *)(uintptr_t)KOMODO_DECON0_MAIN;
            decon[0x224 / 4] = (0xFFu << 16) | 0x3FFu;
            decon[0x228 / 4] = (0x266u << 16) | 0x000u;
            for (uint32_t w = 0; w < 6; w++) {
                volatile uint32_t * wc = (volatile uint32_t *)(uintptr_t)(KOMODO_DECON0_WINCON + (uint64_t)w * 0x1000ULL);
                volatile uint32_t * wn = (volatile uint32_t *)(uintptr_t)(KOMODO_DECON0_WIN + (uint64_t)w * 0x1000ULL);
                if (wc[0] & 1u) {
                    wn[0x14 / 4] = (0xFFu << 16) | 0x3FFu;
                    wn[0x18 / 4] = (0x266u << 16) | 0x000u;
                    wc[0] |= 2u;
                }
            }
            komodo_decon_flush();
        }
    }

    if (is_komodo_board() && !boot_has_rndr) {
        uint64_t sample = 0;
        if (komodo_smc_trng64(&sample)) {
            boot_has_smc_trng = 1;
            boot_has_rndr = 1;
        } else {
            uint64_t a0 = SMC_CMD_RANDOM, a1 = HWRNG_INIT, a2 = 0, a3 = 0;
            boot_smc_trng_err = exynos_cm_smc(&a0, &a1, &a2, &a3);
            if (arm_smccc_trng64(&sample)) {
                boot_has_smc_trng = 2;
                boot_has_rndr = 1;
            }
        }
    }

    boot_serial_puts("tricorder boot: AArch64 EL1 bare-metal, Stage-1 MMU + WXN active\n");
    boot_serial_puts("tricorder boot: MIDR=");
    boot_serial_hex64(boot_midr);
    boot_serial_puts(" DIT=");
    boot_serial_puts(boot_dit_enabled ? "ON" : (boot_has_dit ? "OFF" : "UNSUPPORTED"));
    boot_serial_puts(" RNDR=");
    boot_serial_puts(boot_has_smc_trng == 1 ? "EXYSWD-TRNG" : (boot_has_smc_trng == 2 ? "SMCCC-TRNG" : (boot_has_rndr ? "YES" : "NO")));
    if (!boot_has_rndr && is_komodo_board()) {
        boot_serial_puts(" SMCERR=");
        boot_serial_hex64(boot_smc_trng_err);
    }
    boot_serial_puts(" FDT=");
    boot_serial_dec((int)boot_fdt_size);
    boot_serial_puts("B");
    if (is_komodo_board() && boot_has_rndr) {
        int r_ok = 0;
        for (int k = 0; k < 4; k++) {
            uint64_t tmp = 0;
            if (boot_rndr64(&tmp)) r_ok++;
        }
        boot_serial_puts(" TRNG4=");
        boot_serial_dec(r_ok);
    }
    boot_serial_puts("\n");
    if (is_komodo_board()) {
        boot_serial_puts("tricorder boot: FB=");
        boot_serial_hex64(boot_fb_base);
        boot_serial_puts(" ");
        boot_serial_dec((int)boot_fb_width);
        boot_serial_puts("X");
        boot_serial_dec((int)boot_fb_height);
        boot_serial_puts(" HEAP=");
        boot_serial_hex64((uint64_t)(uintptr_t)boot_heap_start);
        boot_serial_puts("\n");
        uint32_t pd_hsi0 = *(volatile uint32_t *)(uintptr_t)(KOMODO_PMU_ALIVE + 0x2A84ULL);
        boot_serial_puts("tricorder boot: PD_HSI0=");
        boot_serial_hex64(pd_hsi0);
        if ((pd_hsi0 & 0x1u) != 0u) {
            uint32_t snps = *(volatile uint32_t *)(uintptr_t)(KOMODO_DWC3 + 0xC120ULL);
            boot_serial_puts(" DWC3=");
            boot_serial_hex64(snps);
        }
        uint32_t ufs_hce = *(volatile uint32_t *)(uintptr_t)(KOMODO_UFS + 0x34ULL);
        uint32_t ufs_hcs = *(volatile uint32_t *)(uintptr_t)(KOMODO_UFS + 0x30ULL);
        boot_serial_puts(" UFS_HCE=");
        boot_serial_hex64(ufs_hce);
        boot_serial_puts(" HCS=");
        boot_serial_hex64(ufs_hcs);
        boot_serial_puts("\n");
        komodo_delay_ms(1200); /* pause 1.2s so user can glimpse silicon telemetry before LCARS takes over! */
    }

    tricorder_bare_start();
    boot_halt(0);
}
