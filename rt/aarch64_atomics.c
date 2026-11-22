/*
Outline-atomics helper referenced by Lean's official linux_aarch64 libInit.a / libStd.a.
Tricorder runs single-threaded on Android's main ALooper, and we still use the relaxed atomic
intrinsic so the instruction is a single LSE `ldadd` on Pixel Tensor / ARMv8.1+.
*/
#include <stdint.h>

uint32_t __aarch64_ldadd4_relax(uint32_t val, uint32_t * ptr) {
    return __atomic_fetch_add(ptr, val, __ATOMIC_RELAXED);
}
