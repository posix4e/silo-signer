/* Shared contract between boot/aarch64/ and rt/bare/. */
#pragma once
#include <stddef.h>
#include <stdint.h>

typedef struct {
    uint64_t base;
    uint64_t size;
} boot_window_t;

#define BOOT_MAX_WINDOWS 64

extern boot_window_t boot_windows[BOOT_MAX_WINDOWS];
extern size_t boot_window_count;

extern void * boot_heap_start;
extern size_t boot_heap_size;

extern void * boot_device_start;
extern size_t boot_device_size;

extern uint64_t boot_fb_base;
extern uint32_t boot_fb_width;
extern uint32_t boot_fb_height;
extern uint32_t boot_fb_stride;
extern uint32_t boot_fb_bpp;
extern int boot_fb_console_quiet;

extern uint8_t const * boot_fdt_ptr;
extern size_t boot_fdt_size;
extern char boot_command_line[1024];

extern uint64_t boot_midr;
extern int boot_has_dit;
extern int boot_dit_enabled;
extern int boot_has_rndr;
extern uint8_t boot_initial_el;

void boot_serial_write(char const * bytes, size_t length);
void boot_serial_puts(char const * s);
void boot_serial_hex64(uint64_t v);
int boot_rndr64(uint64_t * out);
uint64_t boot_cntvct(void);
_Noreturn void boot_halt(int code);
int boot_check(void);

/* Entry point implemented by rt/bare/platform.c calling Lean bare_main(). */
void tricorder_bare_start(void);
