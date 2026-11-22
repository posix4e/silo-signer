/*
Capability-checked bare-metal hardware boundary: the C half of `Kernel/Hw.lean`.

Modeled directly on `silo-os/rt/bare/hw.c`:
  - Every MMIO read/write is checked against `boot_windows[]` AND hardened with the proved
    branchless `in_bounds` mask (`Mini/WordProofs.lean`) against speculative out-of-bounds loads.
  - Every DMA load/store is strictly checked inside the allocated slice of `boot_device_start`.
  - Every framebuffer blit is strictly checked inside `boot_fb_base + height * stride * bpp`.
  - Lean NEVER receives a raw pointer.
*/
#include "../rt.h"
#include "../../boot/aarch64/boot.h"

/* Branchless speculation-hardened index mask proved in `Mini/WordProofs.lean`. */
static uint64_t in_bounds(uint64_t index, uint64_t size) {
    uint64_t mask = ((index | (size - 1 - index)) >> 63) - 1;
    __asm__ volatile("" : "+r"(mask));
    return index & mask;
}

lean_obj_res silo_hw_windows(void) {
    lean_object * r = lean_alloc_array(2 * boot_window_count, 2 * boot_window_count);
    for (size_t i = 0; i < boot_window_count; i++) {
        lean_array_cptr(r)[2 * i]     = lean_box_uint64(boot_windows[i].base);
        lean_array_cptr(r)[2 * i + 1] = lean_box_uint64(boot_windows[i].size);
    }
    return r;
}

static volatile uint32_t * reg32_at(uint64_t address) {
    for (size_t i = 0; i < boot_window_count; i++) {
        uint64_t base = boot_windows[i].base;
        if ((address & 3ULL) == 0 && address >= base && boot_windows[i].size >= 4 &&
            address - base <= boot_windows[i].size - 4) {
            return (volatile uint32_t *)(uintptr_t)(base + in_bounds(address - base, boot_windows[i].size - 3));
        }
    }
    rt_stop("a driver reached for a 32-bit register outside announced MMIO windows");
}

static volatile uint64_t * reg64_at(uint64_t address) {
    for (size_t i = 0; i < boot_window_count; i++) {
        uint64_t base = boot_windows[i].base;
        if ((address & 7ULL) == 0 && address >= base && boot_windows[i].size >= 8 &&
            address - base <= boot_windows[i].size - 8) {
            return (volatile uint64_t *)(uintptr_t)(base + in_bounds(address - base, boot_windows[i].size - 7));
        }
    }
    rt_stop("a driver reached for a 64-bit register outside announced MMIO windows");
}

uint32_t silo_hw_read32(uint64_t address) {
    uint32_t v = *reg32_at(address);
    __asm__ volatile("dsb ld" ::: "memory");
    return v;
}

lean_obj_res silo_hw_write32(uint64_t address, uint32_t value) {
    __asm__ volatile("dsb st" ::: "memory");
    *reg32_at(address) = value;
    __asm__ volatile("dsb sy" ::: "memory");
    return lean_box(0);
}

uint64_t silo_hw_read64(uint64_t address) {
    uint64_t v = *reg64_at(address);
    __asm__ volatile("dsb ld" ::: "memory");
    return v;
}

lean_obj_res silo_hw_write64(uint64_t address, uint64_t value) {
    __asm__ volatile("dsb st" ::: "memory");
    *reg64_at(address) = value;
    __asm__ volatile("dsb sy" ::: "memory");
    return lean_box(0);
}

static size_t device_used = 0;

uint64_t silo_hw_alloc(size_t size) {
    size_t rounded = (size + 4095) & ~(size_t)4095;
    if (size == 0 || rounded < size || rounded > boot_device_size - device_used) return 0;
    uint8_t * block = (uint8_t *)boot_device_start + device_used;
    device_used += rounded;
    memset(block, 0, rounded);
    __asm__ volatile("dsb sy" ::: "memory");
    return (uint64_t)(uintptr_t)block;
}

static uint8_t * device_memory(uint64_t address, size_t size) {
    uint64_t start = (uint64_t)(uintptr_t)boot_device_start;
    if (address < start || address - start > device_used || size > device_used - (address - start))
        rt_stop("a driver reached outside allocated DMA memory");
    return (uint8_t *)(uintptr_t)(start + in_bounds(address - start, device_used - size + 1));
}

lean_obj_res silo_hw_load(uint64_t address, size_t size) {
    __asm__ volatile("dsb ld" ::: "memory");
    uint8_t const * from = device_memory(address, size);
    lean_object * bytes = lean_alloc_sarray(1, size, size);
    memcpy(lean_sarray_cptr(bytes), from, size);
    return bytes;
}

lean_obj_res silo_hw_store(uint64_t address, b_lean_obj_arg bytes) {
    size_t size = lean_sarray_size(bytes);
    memcpy(device_memory(address, size), lean_sarray_cptr(bytes), size);
    __asm__ volatile("dsb st" ::: "memory");
    return lean_box(0);
}

lean_obj_res silo_hw_fb_set(uint64_t base, uint32_t w, uint32_t h, uint32_t stride) {
    size_t fb_bytes = (size_t)h * (size_t)stride * 4;
    /* Verify the requested framebuffer lies inside our DMA arena! */
    (void)device_memory(base, fb_bytes);
    boot_fb_base = base;
    boot_fb_width = w;
    boot_fb_height = h;
    boot_fb_stride = stride;
    boot_fb_bpp = 4;
    return lean_box(0);
}

lean_obj_res silo_hw_fb_store(uint64_t fb_offset, b_lean_obj_arg bytes) {
    size_t size = lean_sarray_size(bytes);
    uint64_t total = (uint64_t)boot_fb_height * (uint64_t)boot_fb_stride * (uint64_t)boot_fb_bpp;
    if (boot_fb_base == 0 || fb_offset > total || size > total - fb_offset)
        rt_stop("framebuffer blit exceeded announced framebuffer bounds");
    boot_fb_console_quiet = 1;
    uint8_t * dst = (uint8_t *)(uintptr_t)(boot_fb_base + in_bounds(fb_offset, total - size + 1));
    memcpy(dst, lean_sarray_cptr(bytes), size);
    __asm__ volatile("dsb st" ::: "memory");
    return lean_box(0);
}

lean_obj_res silo_hw_fb_blit_rgba(b_lean_obj_arg pixels, uint32_t src_w, uint32_t src_h, uint8_t bgra) {
    if (boot_fb_base == 0 || boot_fb_width == 0 || boot_fb_height == 0 ||
        boot_fb_stride < boot_fb_width || src_w == 0 || src_h == 0) {
        return lean_box(0);
    }
    uint64_t need_src = (uint64_t)src_w * (uint64_t)src_h * 4ULL;
    if ((uint64_t)lean_sarray_size(pixels) < need_src) {
        rt_stop("framebuffer blit source buffer shorter than declared dimensions");
    }
    boot_fb_console_quiet = 1;
    uint8_t const * src = lean_sarray_cptr(pixels);
    volatile uint32_t * dst = (volatile uint32_t *)(uintptr_t)boot_fb_base;
    uint32_t dw = boot_fb_width;
    uint32_t dh = boot_fb_height;
    uint32_t stride = boot_fb_stride;
    for (uint32_t y = 0; y < dh; y++) {
        uint32_t sy = (uint32_t)(((uint64_t)y * (uint64_t)src_h) / (uint64_t)dh);
        uint8_t const * srow = src + ((uint64_t)sy * (uint64_t)src_w * 4ULL);
        volatile uint32_t * drow = dst + ((uint64_t)y * (uint64_t)stride);
        if (bgra) {
            for (uint32_t x = 0; x < dw; x++) {
                uint32_t sx = (uint32_t)(((uint64_t)x * (uint64_t)src_w) / (uint64_t)dw);
                uint8_t const * p = srow + ((uint64_t)sx * 4ULL);
                drow[x] = (uint32_t)p[2] | ((uint32_t)p[1] << 8) | ((uint32_t)p[0] << 16) | 0xFF000000U;
            }
        } else {
            for (uint32_t x = 0; x < dw; x++) {
                uint32_t sx = (uint32_t)(((uint64_t)x * (uint64_t)src_w) / (uint64_t)dw);
                uint8_t const * p = srow + ((uint64_t)sx * 4ULL);
                drow[x] = (uint32_t)p[0] | ((uint32_t)p[1] << 8) | ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
            }
        }
    }
    __asm__ volatile("dsb st" ::: "memory");
    return lean_box(0);
}

lean_obj_res silo_hw_fb_info(void) {
    lean_object * r = lean_alloc_array(5, 5);
    lean_array_cptr(r)[0] = lean_box_uint64(boot_fb_base);
    lean_array_cptr(r)[1] = lean_box_uint64(boot_fb_width);
    lean_array_cptr(r)[2] = lean_box_uint64(boot_fb_height);
    lean_array_cptr(r)[3] = lean_box_uint64(boot_fb_stride);
    lean_array_cptr(r)[4] = lean_box_uint64(boot_fb_bpp);
    return r;
}

lean_obj_res silo_hw_fdt(void) {
    lean_object * bytes = lean_alloc_sarray(1, boot_fdt_size, boot_fdt_size);
    if (boot_fdt_size > 0) memcpy(lean_sarray_cptr(bytes), boot_fdt_ptr, boot_fdt_size);
    return bytes;
}

lean_obj_res silo_hw_command_line(void) {
    size_t len = strlen(boot_command_line);
    lean_object * bytes = lean_alloc_sarray(1, len, len);
    memcpy(lean_sarray_cptr(bytes), boot_command_line, len);
    return bytes;
}

lean_obj_res silo_hw_rndr(void) {
    uint64_t w = 0;
    int ok = boot_rndr64(&w);
    lean_object * r = lean_alloc_array(2, 2);
    lean_array_cptr(r)[0] = lean_box_uint64(ok ? 1ULL : 0ULL);
    lean_array_cptr(r)[1] = lean_box_uint64(w);
    return r;
}

lean_obj_res silo_hw_cpu_info(void) {
    lean_object * r = lean_alloc_array(5, 5);
    lean_array_cptr(r)[0] = lean_box_uint64(boot_midr);
    lean_array_cptr(r)[1] = lean_box_uint64(boot_has_dit ? 1ULL : 0ULL);
    lean_array_cptr(r)[2] = lean_box_uint64(boot_dit_enabled ? 1ULL : 0ULL);
    lean_array_cptr(r)[3] = lean_box_uint64(boot_has_rndr ? 1ULL : 0ULL);
    lean_array_cptr(r)[4] = lean_box_uint64(boot_initial_el);
    return r;
}

lean_obj_res silo_hw_console(b_lean_obj_arg bytes) {
    boot_serial_write((char const *)lean_sarray_cptr(bytes), lean_sarray_size(bytes));
    return lean_box(0);
}

lean_obj_res silo_hw_pause(void) {
    __asm__ volatile("yield");
    return lean_box(0);
}

uint64_t silo_hw_ticks(void) {
    return boot_cntvct();
}

uint32_t silo_hw_boot_check(void) {
    return (uint32_t)boot_check();
}

lean_obj_res silo_hw_halt(uint32_t code) {
    boot_halt((int)code);
}
