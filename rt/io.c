/*
Start-up, and the few questions compiled Lean asks about where it is running.

The entry point Lean generates for a program calls these in order: prepare the runtime, initialise every
module, run `main`, report an uncaught error. With one thread and no event loop most of them have nothing
to do.

Elsewhere. Lean's own runtime brings libuv and a pool of task threads; MirageOS on Solo5 gets by with one
core and one loop, as this does. Here there is not even the loop: the server polls its device queues
(Kernel/Server.lean), so start-up has nothing to start.
*/
#include "rt.h"

void lean_initialize_runtime_module(void) {}

char ** lean_setup_args(int argc, char ** argv) {
    (void)argc;
    return argv;
}

void lean_io_mark_end_initialization(void) {}

void lean_init_task_manager(void) {}

void lean_finalize_task_manager(void) {}

/* Lean's runtime starts `main` on a thread with a large stack. Here the stack `main` gets is the one the
platform set up. */
lean_object * lean_run_main(lean_object * (*main_fn)(int, char **), int argc, char ** argv) {
    return main_fn(argc, argv);
}

/* An error `main` did not handle. Lean's runtime renders it with Init's `IO.Error.toString`, which would keep
a good deal of string code alive for a path that should never run. The only errors this code raises are
`IO.userError` (the last of `IO.Error`'s nineteen constructors, holding one string), so that one is printed
in full and any other is named by its constructor number. */
#define IO_ERROR_USER_ERROR 18

void lean_io_result_show_error(b_lean_obj_arg result) {
    lean_object * error = lean_io_result_get_error(result);
    rt_print("uncaught exception: ");
    if (!lean_is_scalar(error) && lean_ptr_tag(error) == IO_ERROR_USER_ERROR && lean_ctor_num_objs(error) == 1
        && !lean_is_scalar(lean_ctor_get(error, 0)) && lean_is_string(lean_ctor_get(error, 0))) {
        lean_object * text = lean_ctor_get(error, 0);
        rt_print_bytes(lean_string_cstr(text), lean_string_size(text) - 1);
    } else {
        rt_print("an IO error of kind ");
        rt_print_size(lean_obj_tag(error));
    }
    rt_print("\n");
}

/* `IO.getRandomBytes`. Init keeps it alive whether or not the program asks for random bytes; the platform's
random source is the only one there is. */
lean_object * silo_plat_random(size_t count);

lean_obj_res lean_io_get_random_bytes(size_t count) {
    return silo_plat_random(count);
}

/* Where this is running, as `System.Platform` asks. Bare metal is none of the three. */
lean_obj_res lean_system_platform_nbits(lean_obj_arg unit) {
    (void)unit;
    return lean_box(64);
}

uint8_t lean_system_platform_windows(lean_obj_arg unit) {
    (void)unit;
    return 0;
}

uint8_t lean_system_platform_osx(lean_obj_arg unit) {
    (void)unit;
#if defined(__APPLE__)
    return 1;
#else
    return 0;
#endif
}

uint8_t lean_system_platform_linux(lean_obj_arg unit) {
    (void)unit;
#if defined(__linux__)
    return 1;
#else
    return 0;
#endif
}

uint8_t lean_system_platform_emscripten(lean_obj_arg unit) {
    (void)unit;
    return 0;
}

/* The commit of the Lean toolchain this runtime matches (4.35.0). */
lean_object * lean_get_githash(lean_obj_arg unit) {
    (void)unit;
    return lean_mk_string("eb6cafb7290e8bd5f2937522d8d804f58f02bafc");
}
