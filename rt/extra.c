/*
Small runtime additions needed by WinnowCore / Tricorder beyond silo-os's minimal set:
- single-threaded `IO.Ref` operations (`lean_st_ref_get`, `put`, `take`, `swap`);
- UTF-8 validation/conversion using the proved `Runtime/Utf8.lean` rules (`rt_utf8_strict`,
  `rt_utf8_claims`, `rt_utf8_write`) and `Mini/String.lean`'s `lean_mk_string_unchecked` /
  `lean_string_utf8_extract`.

Compiles freestanding with `-Wall -Wextra -Werror` and zero libc beyond rt.h's memory helpers.
*/
#include "rt.h"

extern uint8_t rt_utf8_strict(uint8_t b0, uint8_t b1, uint8_t b2, uint8_t b3, size_t left);
extern uint8_t rt_utf8_claims(uint8_t c, uint8_t most);
extern uint64_t rt_utf8_write(uint32_t c);

lean_obj_res lean_nat_big_succ(b_lean_obj_arg a) {
    return lean_nat_big_add(a, lean_box(1));
}

/* ---- Single-threaded IO.Ref operations (BaseIO: return value directly) ---- */

lean_obj_res lean_st_ref_get(b_lean_obj_arg r) {
    lean_object * v = lean_to_ref(r)->m_value;
    lean_inc(v);
    return v;
}

lean_obj_res lean_st_ref_take(b_lean_obj_arg r) {
    lean_ref_object * ref = lean_to_ref(r);
    lean_object * v = ref->m_value;
    ref->m_value = lean_box(0);
    return v;
}

lean_obj_res lean_st_ref_put(b_lean_obj_arg r, lean_obj_arg v) {
    lean_ref_object * ref = lean_to_ref(r);
    lean_dec(ref->m_value);
    ref->m_value = v;
    return lean_box(0);
}

lean_obj_res lean_st_ref_swap(b_lean_obj_arg r, lean_obj_arg v) {
    lean_ref_object * ref = lean_to_ref(r);
    lean_object * old = ref->m_value;
    ref->m_value = v;
    return old;
}

/* ---- UTF-8 byte-array / string operations ---- */

static size_t count_utf8_chars(uint8_t const * p, size_t n) {
    size_t i = 0, len = 0;
    while (i < n) {
        uint8_t w = rt_utf8_claims(p[i], 6);
        if (w == 0) w = 1;
        i += w;
        len++;
    }
    return len;
}

uint8_t lean_string_validate_utf8(b_lean_obj_arg b) {
    uint8_t const * p = lean_sarray_cptr(b);
    size_t n = lean_sarray_size(b);
    size_t i = 0;
    while (i < n) {
        size_t left = n - i;
        uint8_t b0 = p[i];
        uint8_t b1 = left > 1 ? p[i + 1] : 0;
        uint8_t b2 = left > 2 ? p[i + 2] : 0;
        uint8_t b3 = left > 3 ? p[i + 3] : 0;
        uint8_t w = rt_utf8_strict(b0, b1, b2, b3, left);
        if (w == 0) return 0;
        i += w;
    }
    return 1;
}

lean_obj_res lean_string_from_utf8_unchecked(lean_obj_arg b) {
    uint8_t const * p = lean_sarray_cptr(b);
    size_t n = lean_sarray_size(b);
    size_t len = count_utf8_chars(p, n);
    lean_object * s = lean_mk_string_unchecked((char const *)p, n, len);
    lean_dec_ref(b);
    return s;
}

lean_obj_res lean_string_utf8_extract_fast(b_lean_obj_arg s, b_lean_obj_arg b, b_lean_obj_arg e) {
    return lean_string_utf8_extract(s, b, e);
}

lean_obj_res lean_string_utf8_set(lean_obj_arg s, b_lean_obj_arg i_obj, uint32_t c) {
    size_t sz = lean_string_size(s);
    size_t n = sz > 0 ? sz - 1 : 0;
    size_t idx = rt_nat_to_size(i_obj);
    if (idx >= n) return s;

    uint64_t packed = rt_utf8_write(c);
    uint8_t new_w = (uint8_t)(packed >> 32);
    uint8_t new_bytes[4];
    new_bytes[0] = (uint8_t)(packed & 0xffu);
    new_bytes[1] = (uint8_t)((packed >> 8) & 0xffu);
    new_bytes[2] = (uint8_t)((packed >> 16) & 0xffu);
    new_bytes[3] = (uint8_t)((packed >> 24) & 0xffu);

    uint8_t const * src = (uint8_t const *)lean_string_cstr(s);
    uint8_t old_w = rt_utf8_claims(src[idx], 4);
    if (old_w == 0) old_w = 1;
    if (idx + old_w > n) old_w = (uint8_t)(n - idx);

    size_t new_n = n - old_w + new_w;
    lean_object * tmp = lean_alloc_sarray(1, new_n, new_n);
    uint8_t * dst = lean_sarray_cptr(tmp);
    memcpy(dst, src, idx);
    memcpy(dst + idx, new_bytes, new_w);
    memcpy(dst + idx + new_w, src + idx + old_w, n - (idx + old_w));
    size_t len = count_utf8_chars(dst, new_n);
    lean_object * res = lean_mk_string_unchecked((char const *)dst, new_n, len);
    lean_dec_ref(tmp);
    lean_dec_ref(s);
    return res;
}
