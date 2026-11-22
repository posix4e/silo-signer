/*
Minimal freestanding memory & string primitives for bare-metal AArch64 (no libc, no Bionic, no glibc).
Compiled with `-fno-builtin` so clang never turns these loops back into self-calls.
*/
#include <stddef.h>

void * memcpy(void * to, void const * from, size_t count) {
    unsigned char * t = (unsigned char *)to;
    unsigned char const * f = (unsigned char const *)from;
    if ((((unsigned long)t | (unsigned long)f) & 7UL) == 0) {
        unsigned long long * t64 = (unsigned long long *)t;
        unsigned long long const * f64 = (unsigned long long const *)f;
        size_t words = count >> 3;
        for (size_t i = 0; i < words; i++) t64[i] = f64[i];
        size_t done = words << 3;
        for (size_t i = done; i < count; i++) t[i] = f[i];
        return to;
    }
    for (size_t i = 0; i < count; i++) t[i] = f[i];
    return to;
}

void * memmove(void * to, void const * from, size_t count) {
    unsigned char * t = (unsigned char *)to;
    unsigned char const * f = (unsigned char const *)from;
    if (t < f) {
        for (size_t i = 0; i < count; i++) t[i] = f[i];
    } else {
        for (size_t i = count; i > 0; i--) t[i - 1] = f[i - 1];
    }
    return to;
}

void * memset(void * to, int byte, size_t count) {
    unsigned char * t = (unsigned char *)to;
    for (size_t i = 0; i < count; i++) t[i] = (unsigned char)byte;
    return to;
}

int memcmp(void const * left, void const * right, size_t count) {
    unsigned char const * l = (unsigned char const *)left;
    unsigned char const * r = (unsigned char const *)right;
    for (size_t i = 0; i < count; i++) {
        if (l[i] != r[i]) return l[i] < r[i] ? -1 : 1;
    }
    return 0;
}

size_t strlen(char const * text) {
    size_t length = 0;
    while (text[length] != 0) length++;
    return length;
}
