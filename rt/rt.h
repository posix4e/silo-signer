/*
The minimal runtime: what compiled Lean stands on when Lean's own runtime is not there.

Single-threaded. No event loop, no threads, no C++ library, no C library beyond the four memory functions
declared below. It provides exactly the functions listed in rt/live-symbols/, with the object layout that
<lean/lean.h> of Lean 4.35.0 fixes, and nothing else. The platform underneath supplies three things.
*/
#pragma once

#include <lean/lean.h>

/* The platform: an ordinary process (hosted/platform.c) or bare metal (bare/platform.c). */
void * silo_plat_heap(size_t * size);                       /* one region to allocate from; asked for once */
void silo_plat_console(char const * bytes, size_t length);  /* diagnostics */
_Noreturn void silo_plat_halt(int code);                    /* stop */

/* Memory functions. The compiler may call these on its own, so bare metal has to define them too. */
void * memcpy(void * to, void const * from, size_t count);
void * memmove(void * to, void const * from, size_t count);
void * memset(void * to, int byte, size_t count);
int memcmp(void const * left, void const * right, size_t count);
size_t strlen(char const * text);

/* Allocation. Every block is zeroed when it is freed. */
void * rt_malloc(size_t size);
void rt_free(void * block);

/* Printing and stopping. */
void rt_print(char const * text);
void rt_print_bytes(char const * bytes, size_t length);
void rt_print_size(size_t number);
_Noreturn void rt_stop(char const * why);

/* Lean's hash of a run of bytes (hash.c). */
uint64_t rt_hash_bytes(uint8_t const * bytes, size_t length, uint64_t seed);

/* A Nat argument as a size, as Lean's runtime reads one: the value itself when it fits. */
size_t rt_nat_to_size(b_lean_obj_arg nat);
