/*
Objects: making permanent, constants that are built on first use, and a few kinds of object. Giving up
references and freeing is Mini/Free.lean.

Elsewhere. Lean's own runtime makes a value permanent the same way (lean_mark_persistent): its reference
count becomes zero, which counting then leaves alone. GHC's static closures and compact regions are the same
idea, memory the collector never looks at again.
*/
#include "rt.h"

/* A growable stack of objects, for walking a value without recursion. */
typedef struct {
    lean_object ** items;
    size_t count;
    size_t capacity;
} object_stack;

static void stack_push(object_stack * stack, lean_object * o) {
    if (stack->count == stack->capacity) {
        size_t capacity = stack->capacity == 0 ? 64 : stack->capacity * 2;
        lean_object ** items = rt_malloc(lean_usize_mul_checked(capacity, sizeof(lean_object *)));
        if (stack->items != NULL) {
            memcpy(items, stack->items, stack->count * sizeof(lean_object *));
            rt_free(stack->items);
        }
        stack->items = items;
        stack->capacity = capacity;
    }
    stack->items[stack->count++] = o;
}

static void stack_push_all(object_stack * stack, lean_object ** at, size_t count) {
    for (size_t i = 0; i < count; i++) stack_push(stack, at[i]);
}

/* Makes `o` and everything it reaches permanent: never counted, never freed. Used for constants. */
void lean_mark_persistent(lean_object * o) {
    object_stack todo = { NULL, 0, 0 };
    stack_push(&todo, o);
    while (todo.count > 0) {
        o = todo.items[--todo.count];
        if (lean_is_scalar(o) || !lean_has_rc(o)) continue;
        o->m_rc = 0;
        uint8_t tag = lean_ptr_tag(o);
        if (tag <= LeanMaxCtorTag) {
            stack_push_all(&todo, lean_ctor_obj_cptr(o), lean_ctor_num_objs(o));
            continue;
        }
        switch (tag) {
        case LeanScalarArray:
        case LeanString:
        case LeanMPZ:
            break;
        case LeanClosure:
            stack_push_all(&todo, lean_closure_arg_cptr(o), lean_closure_num_fixed(o));
            break;
        case LeanArray:
            stack_push_all(&todo, lean_array_cptr(o), lean_array_size(o));
            break;
        case LeanThunk: {
            lean_object * closure = lean_to_thunk(o)->m_closure;
            lean_object * value = lean_to_thunk(o)->m_value;
            if (closure != NULL) stack_push(&todo, closure);
            if (value != NULL) stack_push(&todo, value);
            break;
        }
        case LeanRef: {
            lean_object * value = lean_to_ref(o)->m_value;
            if (value != NULL) stack_push(&todo, value);
            break;
        }
        default:
            rt_stop("an object of a kind this runtime does not have was made permanent");
        }
    }
    if (todo.items != NULL) rt_free(todo.items);
}

/* Constants built on first use. One thread, so no lock: build it, keep it, say so. */
lean_object * lean_obj_once_cold(lean_object ** loc, lean_once_cell_t * tok, lean_object * (*init)(void)) {
    if (tok->state != 1) {
        *loc = init();
        lean_mark_persistent(*loc);
        tok->state = 1;
    }
    return *loc;
}

#define ONCE_COLD(name, type)                                               \
    type name(type * loc, lean_once_cell_t * tok, type (*init)(void)) {     \
        if (tok->state != 1) {                                              \
            *loc = init();                                                  \
            tok->state = 1;                                                 \
        }                                                                   \
        return *loc;                                                        \
    }

ONCE_COLD(lean_uint8_once_cold, uint8_t)
ONCE_COLD(lean_uint16_once_cold, uint16_t)
ONCE_COLD(lean_uint32_once_cold, uint32_t)
ONCE_COLD(lean_uint64_once_cold, uint64_t)
ONCE_COLD(lean_usize_once_cold, size_t)
ONCE_COLD(lean_float32_once_cold, float)
ONCE_COLD(lean_float_once_cold, double)

/* A mutable cell. */
lean_obj_res lean_st_mk_ref(lean_obj_arg a) {
    lean_ref_object * o = (lean_ref_object *)lean_alloc_small_object(sizeof(lean_ref_object));
    lean_set_st_header((lean_object *)o, LeanRef, 0);
    o->m_value = a;
    return (lean_object *)o;
}

/* Floating-point values from their bits. */
double lean_float_of_bits(uint64_t u) {
    double d;
    memcpy(&d, &u, sizeof d);
    return d;
}

float lean_float32_of_bits(uint32_t u) {
    float f;
    memcpy(&f, &u, sizeof f);
    return f;
}

/* A lazy value: computed the first time it is asked for, then kept. Called when it has not been computed. */
b_lean_obj_res lean_thunk_get_core(b_lean_obj_arg t) {
    lean_thunk_object * thunk = lean_to_thunk(t);
    lean_object * closure = thunk->m_closure;
    if (closure == NULL) rt_stop("a lazy value was asked for while it was being computed");
    thunk->m_closure = NULL;
    lean_object * value = lean_apply_1(closure, lean_box(0));
    thunk->m_value = value;
    return value;
}

/* Equality of two `Lean.Name`s: the same chain of strings and numbers. Each name keeps a hash of itself, so
most unequal pairs are told apart at once. */
uint8_t lean_name_eq(b_lean_obj_arg n1, b_lean_obj_arg n2) {
    if (n1 == n2) return true;
    if (lean_is_scalar(n1) != lean_is_scalar(n2) || lean_name_hash_ptr(n1) != lean_name_hash_ptr(n2)) return false;
    for (;;) {
        if (lean_ptr_tag(n1) != lean_ptr_tag(n2)) return false;
        if (lean_ptr_tag(n1) == 1) {
            if (!lean_string_eq(lean_ctor_get(n1, 1), lean_ctor_get(n2, 1))) return false;
        } else {
            if (!lean_nat_eq(lean_ctor_get(n1, 1), lean_ctor_get(n2, 1))) return false;
        }
        n1 = lean_ctor_get(n1, 0);
        n2 = lean_ctor_get(n2, 0);
        if (n1 == n2) return true;
        if (lean_is_scalar(n1) != lean_is_scalar(n2)) return false;
    }
}

/* Adds `n` references at once, for an `n` too large for the inline path (an array of that many copies of
one value). A count that would pass the largest a header can hold freezes instead: the object is then never
freed, which is safe. */
void lean_inc_ref_huge_n(lean_object * o, size_t n) {
    int count = o->m_rc;
    if (count <= 0) return;   /* permanent or already frozen */
    if (n > (size_t)(INT_MAX - count)) o->m_rc = LEAN_RC_STUCK_ST; else o->m_rc = count + (int)n;
}

/* ---- Objects from the allocator (Mini/Alloc.lean) ---- */

/* An object of a small fixed size. The header's size field is set, as <lean/lean.h> says it must be. */
lean_object * lean_alloc_small_object_core(unsigned sz) {
    lean_object * o = rt_malloc(sz);
    o->m_cs_sz = sz;
    return o;
}

/* An object of any size: arrays, strings, closures. */
lean_object * lean_alloc_object(size_t sz) {
    lean_object * o = rt_malloc(sz);
    o->m_cs_sz = 0;
    return o;
}

void lean_free_object(lean_object * o) {
    rt_free(o);
}
