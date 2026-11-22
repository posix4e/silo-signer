/*
AArch64 MMU protection self-checks (`boot/aarch64/checks.c`), modeled directly on `silo-os/boot/checks.c`.

Reads `check=<name>` from `boot_command_line` and attempts that exact forbidden operation:
  - `check=none`           : ordinary data/heap/stack use succeeds -> returns 0
  - `check=write-code`     : store into `.text` -> Data Abort (RO enforced) -> exit 3
  - `check=write-constant` : store into `.rodata` -> Data Abort (RO enforced) -> exit 3
  - `check=run-data`       : execute AArch64 `ret` in `.data` -> Instruction Abort (PXN+WXN) -> exit 3
  - `check=run-heap`       : execute AArch64 `ret` in heap -> Instruction Abort (PXN+WXN) -> exit 3
  - `check=run-stack`      : execute AArch64 `ret` on stack -> Instruction Abort (PXN+WXN) -> exit 3
  - `check=read-zero`      : load from address 0x10 -> Data Abort (null page unmapped) -> exit 3
  - `check=overflow`       : recurse past 1 MiB stack into `__stack_guard` -> Data Abort caught on SP_EL1! -> exit 3
  - `check=beside-device`  : read the unmapped 4 KiB page directly above VirtIO-MMIO -> Data Abort -> exit 3

If a forbidden operation is NOT caught by the MMU, prints `NOT stopped` and returns 9!
*/
#include "boot.h"
#include <stddef.h>
#include <stdint.h>

static int asked(char const * name) {
    static char const key[] = "check=";
    for (char const * p = boot_command_line; *p != 0; p++) {
        size_t i = 0;
        while (key[i] != 0 && p[i] == key[i]) i++;
        if (key[i] != 0) continue;
        p += i;
        i = 0;
        while (name[i] != 0 && p[i] == name[i]) i++;
        return name[i] == 0 && (p[i] == 0 || p[i] == ' ');
    }
    return 0;
}

static volatile uintptr_t hidden;

static void write_to(void const * where) {
    hidden = (uintptr_t)where;
    *(volatile unsigned char *)hidden = 0xAA;
}

static unsigned char read_from(uintptr_t where) {
    hidden = where;
    return *(volatile unsigned char *)hidden;
}

static void run_at(void * where) {
    hidden = (uintptr_t)where;
    /* AArch64 `ret` instruction encoding = 0xd65f03c0 */
    *(volatile uint32_t *)hidden = 0xd65f03c0U;
    __asm__ volatile("dc cvau, %0; dsb ish; ic ivau, %0; dsb ish; isb" :: "r"(hidden) : "memory");
    ((void (*)(void))hidden)();
}

static char const constant[] = "a constant";
static uint32_t in_data[4] = { 1, 2, 3, 4 };
static volatile unsigned long depth_limit = ~0UL;

static unsigned long descend(unsigned long depth) {
    volatile unsigned char frame[4096];
    frame[0] = (unsigned char)depth;
    if (depth >= depth_limit) return frame[0];
    return descend(depth + 1) + frame[0];
}

int boot_check(void) {
    if (asked("none")) {
        in_data[1] = 7;
        volatile unsigned char * heap = (volatile unsigned char *)boot_heap_start;
        heap[0] = heap[0];
        depth_limit = 64;
        int ok = (in_data[1] == 7 && descend(0) != ~0UL);
        boot_serial_puts(ok ? "check: nothing forbidden was tried\n" : "check: ordinary use failed\n");
        return ok ? 0 : 9;
    }
    if (asked("write-code")) write_to((void const *)(uintptr_t)&boot_check);
    else if (asked("write-constant")) write_to(constant);
    else if (asked("run-data")) run_at(in_data);
    else if (asked("run-heap")) run_at(boot_heap_start);
    else if (asked("run-stack")) {
        uint32_t on_stack[4] __attribute__((aligned(16)));
        run_at(on_stack);
    }
    else if (asked("read-zero")) hidden = read_from(0x10);
    else if (asked("overflow")) {
        depth_limit = ~0UL;
        hidden = descend(0);
    }
    else if (asked("beside-device")) {
        if (boot_window_count == 0) {
            boot_serial_puts("check: no device windows announced\n");
            return 8;
        }
        /* Pick the highest device window end and read the next 4 KiB page directly above it. */
        uint64_t top = 0;
        for (size_t i = 0; i < boot_window_count; i++) {
            uint64_t end = boot_windows[i].base + boot_windows[i].size;
            if (end > top) top = end;
        }
        uint64_t next_page = (top + 0xfffULL) & ~0xfffULL;
        hidden = read_from((uintptr_t)next_page);
    }
    else {
        return 1; /* no check requested on command line */
    }
    boot_serial_puts("check: that was NOT stopped\n");
    return 9;
}
