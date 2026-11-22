/*
What the small cases (Mini/Small.lean) need from the big-number code (Mini/Number.lean).

Mini/Small.lean answers `<<<`, `^`, `log2` and "a Nat as a size" itself when everything stays below 2^63, and comes
here for the rest. Everything else there is called by compiled Lean directly, under the names
<lean/lean.h> declares.
*/
#pragma once

#include "rt.h"

/* `a <<< shift` for any natural number `a`. */
lean_obj_res rt_big_nat_shiftl(b_lean_obj_arg a, size_t shift);

/* `a ^ exponent` for any natural number `a`. */
lean_obj_res rt_big_nat_pow(b_lean_obj_arg a, size_t exponent);

/* The position of the highest set bit of `a`; 0 for 0. */
size_t rt_big_nat_log2(b_lean_obj_arg a);

/* `a` as a size if it is below 2^64. If it is not, reports "out of memory" and stops, as Lean's runtime does:
nothing that large can be the size of anything. */
size_t rt_big_nat_to_size(b_lean_obj_arg a);
