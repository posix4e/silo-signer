/*
Printing and stopping.

A Lean `panic!` prints its message and stops the machine. Lean's own runtime prints and carries on with a
default value unless told otherwise; a service holding a secret that has reached a state its authors called impossible
should not carry on.

Elsewhere. Linux's panic() can be told to reboot, and its BUG() kills only the task when it can; Lean's
own runtime prints and returns a default value. Here there is nothing else running to save and nothing a
default value could mean, so the machine stops, as a seL4 kernel built with its checks on stops when one fails.
*/
#include "rt.h"

void rt_print_bytes(char const * bytes, size_t length) {
    silo_plat_console(bytes, length);
}

void rt_print(char const * text) {
    silo_plat_console(text, strlen(text));
}

void rt_print_size(size_t number) {
    char digits[24];
    size_t at = sizeof(digits);
    do {
        digits[--at] = (char)('0' + number % 10);
        number /= 10;
    } while (number != 0);
    silo_plat_console(digits + at, sizeof(digits) - at);
}

_Noreturn void rt_stop(char const * why) {
    rt_print("silo runtime: ");
    rt_print(why);
    rt_print("\n");
    silo_plat_halt(70);
}

/* The runtime is compiled with <lean/lean.h>'s assertions on: a failed one stops the machine. */
void lean_notify_assert(char const * file, int line, char const * condition) {
    rt_print("silo runtime: assertion failed: ");
    rt_print(condition);
    rt_print(" (");
    rt_print(file);
    rt_print(":");
    rt_print_size((size_t)line);
    rt_print(")\n");
    silo_plat_halt(70);
}

LEAN_NORETURN void lean_internal_panic(char const * msg) {
    rt_print("INTERNAL PANIC: ");
    rt_print(msg);
    rt_print("\n");
    silo_plat_halt(1);
}

LEAN_NORETURN void lean_internal_panic_out_of_memory(void) { lean_internal_panic("out of memory"); }
LEAN_NORETURN void lean_internal_panic_unreachable(void) { lean_internal_panic("unreachable code has been reached"); }
LEAN_NORETURN void lean_internal_panic_rc_overflow(void) { lean_internal_panic("reference counter overflowed"); }
LEAN_NORETURN void lean_internal_panic_overflow(void) { lean_internal_panic("integer overflow in runtime computation"); }

lean_object * lean_panic_fn(lean_object * default_val, lean_object * msg) {
    (void)default_val;
    rt_print_bytes(lean_string_cstr(msg), lean_string_size(msg) - 1);
    rt_print("\n");
    silo_plat_halt(1);
}

lean_object * lean_panic_fn_borrowed(b_lean_obj_arg default_val, lean_object * msg) {
    return lean_panic_fn(default_val, msg);
}
