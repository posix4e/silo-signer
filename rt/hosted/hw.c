/* Hosted stub for `Kernel/Hw.lean` so hosted macOS tests can import `Kernel.*` cleanly. */
#include <lean/lean.h>
#include <stdint.h>

lean_obj_res silo_hw_windows(void) { return lean_alloc_array(0, 0); }
uint32_t silo_hw_read32(uint64_t a) { (void)a; return 0; }
lean_obj_res silo_hw_write32(uint64_t a, uint32_t v) { (void)a; (void)v; return lean_box(0); }
uint64_t silo_hw_read64(uint64_t a) { (void)a; return 0; }
lean_obj_res silo_hw_write64(uint64_t a, uint64_t v) { (void)a; (void)v; return lean_box(0); }
uint64_t silo_hw_alloc(size_t s) { (void)s; return 0; }
lean_obj_res silo_hw_load(uint64_t a, size_t s) { (void)a; (void)s; return lean_alloc_sarray(1, 0, 0); }
lean_obj_res silo_hw_store(uint64_t a, b_lean_obj_arg b) { (void)a; (void)b; return lean_box(0); }
lean_obj_res silo_hw_fb_set(uint64_t b, uint32_t w, uint32_t h, uint32_t s) { (void)b; (void)w; (void)h; (void)s; return lean_box(0); }
lean_obj_res silo_hw_fb_store(uint64_t o, b_lean_obj_arg b) { (void)o; (void)b; return lean_box(0); }
lean_obj_res silo_hw_fb_blit_rgba(b_lean_obj_arg p, uint32_t w, uint32_t h, uint8_t bgra) { (void)p; (void)w; (void)h; (void)bgra; return lean_box(0); }
lean_obj_res silo_hw_fb_info(void) { return lean_alloc_array(0, 0); }
lean_obj_res silo_hw_fdt(void) { return lean_alloc_sarray(1, 0, 0); }
lean_obj_res silo_hw_command_line(void) { return lean_alloc_sarray(1, 0, 0); }
lean_obj_res silo_hw_rndr(void) { return lean_alloc_array(0, 0); }
lean_obj_res silo_hw_cpu_info(void) { return lean_alloc_array(0, 0); }
lean_obj_res silo_hw_console(b_lean_obj_arg b) { (void)b; return lean_box(0); }
lean_obj_res silo_hw_pause(void) { return lean_box(0); }
uint64_t silo_hw_ticks(void) { return 0; }
uint32_t silo_hw_boot_check(void) { return 0; }
lean_obj_res silo_hw_halt(uint32_t c) { (void)c; return lean_box(0); }
