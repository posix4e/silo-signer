/*
Calling closures.

A closure is a function, the number of arguments it takes, and the arguments it already has. Applying it to
more arguments either still leaves it short (a new closure with more arguments fixed), completes it (call
the function), or over-completes it (call the function, then apply what it returns to the rest).

Functions of up to sixteen arguments take them as separate C arguments; above that they take one array.
Lean's runtime writes every combination out by hand for speed. This is the same behaviour in one function.

Elsewhere. This is the eval/apply model of Marlow and Peyton Jones's "Making a fast curry" (GHC's
stg_ap_* functions), and OCaml's caml_applyN and caml_curryN do the same for OCaml closures. Lean's own runtime
(src/runtime/apply.cpp) spells out one case per pair of arities. Here it is one function, read in one
sitting, because nothing it would save is worth a few hundred more lines under a secret.
*/
#include "rt.h"

typedef lean_object obj;

#define O obj *
#define CALL(n, types, ...) \
    case n: return ((obj * (*) types)fn)(__VA_ARGS__);

static obj * call(void * fn, unsigned arity, obj ** a) {
    switch (arity) {
    CALL(1, (O), a[0])
    CALL(2, (O, O), a[0], a[1])
    CALL(3, (O, O, O), a[0], a[1], a[2])
    CALL(4, (O, O, O, O), a[0], a[1], a[2], a[3])
    CALL(5, (O, O, O, O, O), a[0], a[1], a[2], a[3], a[4])
    CALL(6, (O, O, O, O, O, O), a[0], a[1], a[2], a[3], a[4], a[5])
    CALL(7, (O, O, O, O, O, O, O), a[0], a[1], a[2], a[3], a[4], a[5], a[6])
    CALL(8, (O, O, O, O, O, O, O, O), a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7])
    CALL(9, (O, O, O, O, O, O, O, O, O), a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8])
    CALL(10, (O, O, O, O, O, O, O, O, O, O), a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9])
    CALL(11, (O, O, O, O, O, O, O, O, O, O, O),
         a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10])
    CALL(12, (O, O, O, O, O, O, O, O, O, O, O, O),
         a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11])
    CALL(13, (O, O, O, O, O, O, O, O, O, O, O, O, O),
         a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12])
    CALL(14, (O, O, O, O, O, O, O, O, O, O, O, O, O, O),
         a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12], a[13])
    CALL(15, (O, O, O, O, O, O, O, O, O, O, O, O, O, O, O),
         a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12], a[13], a[14])
    CALL(16, (O, O, O, O, O, O, O, O, O, O, O, O, O, O, O, O),
         a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12], a[13], a[14], a[15])
    default: return ((obj * (*)(obj **))fn)(a);
    }
}

/* `f` with `n` more arguments fixed, still short of its arity. Consumes `f` and the arguments. */
static obj * fix_more(obj * f, unsigned n, obj ** as) {
    unsigned arity = lean_closure_arity(f);
    unsigned fixed = lean_closure_num_fixed(f);
    obj * r = lean_alloc_closure(lean_closure_fun(f), arity, fixed + n);
    obj ** from = lean_closure_arg_cptr(f);
    obj ** to = lean_closure_arg_cptr(r);
    if (lean_is_exclusive(f)) {
        for (unsigned i = 0; i < fixed; i++) to[i] = from[i];
        lean_free_object(f);
    } else {
        for (unsigned i = 0; i < fixed; i++) {
            to[i] = from[i];
            lean_inc(to[i]);
        }
        lean_dec_ref(f);
    }
    for (unsigned i = 0; i < n; i++) to[fixed + i] = as[i];
    return r;
}

/* Applies `f` to `n` arguments. Consumes `f` and the arguments. */
obj * lean_apply_n(obj * f, unsigned n, obj ** as) {
    for (;;) {
        if (lean_is_scalar(f)) {
            /* An erased proof stands where a function would be: there is nothing to call. */
            for (unsigned i = 0; i < n; i++) lean_dec(as[i]);
            return f;
        }
        unsigned arity = lean_closure_arity(f);
        unsigned fixed = lean_closure_num_fixed(f);
        if (fixed + n < arity) return fix_more(f, n, as);
        unsigned taken = arity - fixed;
        void * fn = lean_closure_fun(f);
        obj * args[arity];
        obj ** held = lean_closure_arg_cptr(f);
        if (lean_is_exclusive(f)) {
            for (unsigned i = 0; i < fixed; i++) args[i] = held[i];
            lean_free_object(f);
        } else {
            for (unsigned i = 0; i < fixed; i++) {
                args[i] = held[i];
                lean_inc(args[i]);
            }
            lean_dec_ref(f);
        }
        for (unsigned i = 0; i < taken; i++) args[fixed + i] = as[i];
        obj * r = call(fn, arity, args);
        if (taken == n) return r;
        f = r;
        as += taken;
        n -= taken;
    }
}

obj * lean_apply_m(obj * f, unsigned n, obj ** as) {
    return lean_apply_n(f, n, as);
}

/* lean_apply_1 to lean_apply_16: the same thing with the arguments written out. */
#define APPLY(n, parameters, ...) \
    obj * lean_apply_##n parameters { \
        obj * as[] = { __VA_ARGS__ }; \
        return lean_apply_n(f, n, as); \
    }
APPLY(1, (O f, O a), a)
APPLY(2, (O f, O a, O b), a, b)
APPLY(3, (O f, O a, O b, O c), a, b, c)
APPLY(4, (O f, O a, O b, O c, O d), a, b, c, d)
APPLY(5, (O f, O a, O b, O c, O d, O e), a, b, c, d, e)
APPLY(6, (O f, O a, O b, O c, O d, O e, O g), a, b, c, d, e, g)
APPLY(7, (O f, O a, O b, O c, O d, O e, O g, O h), a, b, c, d, e, g, h)
APPLY(8, (O f, O a, O b, O c, O d, O e, O g, O h, O i), a, b, c, d, e, g, h, i)
APPLY(9, (O f, O a, O b, O c, O d, O e, O g, O h, O i, O j), a, b, c, d, e, g, h, i, j)
APPLY(10, (O f, O a, O b, O c, O d, O e, O g, O h, O i, O j, O k), a, b, c, d, e, g, h, i, j, k)
APPLY(11, (O f, O a, O b, O c, O d, O e, O g, O h, O i, O j, O k, O l), a, b, c, d, e, g, h, i, j, k, l)
APPLY(12, (O f, O a, O b, O c, O d, O e, O g, O h, O i, O j, O k, O l, O m), a, b, c, d, e, g, h, i, j, k, l, m)
APPLY(13, (O f, O a, O b, O c, O d, O e, O g, O h, O i, O j, O k, O l, O m, O n), a, b, c, d, e, g, h, i, j, k, l, m, n)
APPLY(14, (O f, O a, O b, O c, O d, O e, O g, O h, O i, O j, O k, O l, O m, O n, O p), a, b, c, d, e, g, h, i, j, k, l, m, n, p)
APPLY(15, (O f, O a, O b, O c, O d, O e, O g, O h, O i, O j, O k, O l, O m, O n, O p, O q),
      a, b, c, d, e, g, h, i, j, k, l, m, n, p, q)
APPLY(16, (O f, O a, O b, O c, O d, O e, O g, O h, O i, O j, O k, O l, O m, O n, O p, O q, O r),
      a, b, c, d, e, g, h, i, j, k, l, m, n, p, q, r)
