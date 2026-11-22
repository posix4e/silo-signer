/*
Bare-metal AArch64 platform bridge (`rt/bare/platform.c`).

Wires the verified minimal runtime (`rt/object.c`, `Mini/Alloc`) to the heap and serial console
from `boot/aarch64/early.c`, and starts the Lean bare-metal kernel entry point (`tricorder_bare_main`).
*/
#include "../rt.h"
#include "../../boot/aarch64/boot.h"

extern void lean_initialize_runtime_module(void);
extern lean_obj_res initialize_tricorder_entry(uint8_t builtin);
extern lean_obj_res tricorder_bare_main(void);

lean_object * lean_mk_io_user_error(lean_object * message);

void * silo_plat_heap(size_t * size) {
    *size = boot_heap_size;
    return boot_heap_start;
}

void silo_plat_console(char const * bytes, size_t length) {
    boot_serial_write(bytes, length);
}

_Noreturn void silo_plat_halt(int code) {
    boot_halt(code);
}

/* Fallback Platform hooks (bare-metal drivers primarily use Kernel.Hw directly). */
lean_obj_res silo_plat_write(b_lean_obj_arg bytes) {
    boot_serial_write((char const *)lean_sarray_cptr(bytes), lean_sarray_size(bytes));
    return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res silo_plat_random(size_t count) {
    if (!boot_has_rndr) {
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("hardware RNDR unavailable")));
    }
    lean_object * bytes = lean_alloc_sarray(1, count, count);
    uint8_t * dst = lean_sarray_cptr(bytes);
    size_t done = 0;
    while (done < count) {
        uint64_t w = 0;
        int ok = 0;
        for (int tries = 0; tries < 32 && !ok; tries++) ok = boot_rndr64(&w);
        if (!ok) {
            lean_dec_ref(bytes);
            return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("hardware RNDR timed out")));
        }
        for (int i = 0; i < 8 && done < count; i++) dst[done++] = (uint8_t)(w >> (8 * i));
    }
    return lean_io_result_mk_ok(bytes);
}

lean_obj_res tricorder_plat_log(b_lean_obj_arg msg) {
    boot_serial_write(lean_string_cstr(msg), lean_string_size(msg) - 1);
    boot_serial_write("\n", 1);
    return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res tricorder_plat_read_file(b_lean_obj_arg p) { (void)p; return lean_io_result_mk_ok(lean_box(0)); }
lean_obj_res tricorder_plat_write_file(b_lean_obj_arg p, b_lean_obj_arg b) { (void)p; (void)b; return lean_io_result_mk_ok(lean_box(0)); }
lean_obj_res tricorder_plat_delete_file(b_lean_obj_arg p) { (void)p; return lean_io_result_mk_ok(lean_box(0)); }
lean_obj_res tricorder_plat_list_files(b_lean_obj_arg p) { (void)p; return lean_io_result_mk_ok(lean_alloc_array(0, 0)); }

void tricorder_bare_start(void) {
    lean_initialize_runtime_module();
    lean_obj_res res = initialize_tricorder_entry(1);
    if (lean_io_result_is_error(res)) {
        lean_io_result_show_error(res);
        boot_halt(70);
    }
    lean_dec_ref(res);
    lean_io_mark_end_initialization();

    lean_obj_res mres = tricorder_bare_main();
    if (lean_io_result_is_error(mres)) {
        lean_io_result_show_error(mres);
        lean_dec_ref(mres);
        boot_halt(1);
    }
    uint32_t code = (uint32_t)lean_unbox(lean_io_result_get_value(mres));
    lean_dec_ref(mres);
    boot_halt((int)code);
}
