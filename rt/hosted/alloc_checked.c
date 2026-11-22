/*
The runtime's allocator, replaced for testing.

Every request becomes one block from the C library, so that AddressSanitizer puts a guard zone around each
one and sees every read or write past its end and every use after it is freed. The real allocator (alloc.c)
carves blocks out of one region, where a stray write lands in a neighbour and nothing notices.

New blocks are filled with a non-zero byte, so that code which only works because fresh memory happens to be
zero fails here.

Used by scripts/build-checked only. Never part of an image.
*/
#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>

void * rt_malloc(size_t size) {
    void * block = malloc(size == 0 ? 1 : size);
    if (block == NULL) abort();
    memset(block, 0xA5, size);
    return block;
}

void rt_free(void * block) {
    free(block);
}
