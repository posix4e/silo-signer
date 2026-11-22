/*
The allocator as printed and compiled, driven a request at a time from its standard input.

    alloc-harness <bytes of heap>

It first prints where its heap is. Then, for each line it reads, it does one thing and prints one line:

    m <size> 0        rt_malloc(size); prints the address
    f <address> 0     rt_free(address); prints 0
    w <address> <v>   writes the word v at address; prints 0
    r <address> 0     prints the word at address
    q 0 0             ends the run

If the allocator stops the machine it prints "stop" and why; if it runs out of memory, "oom". Either ends the
run. scripts/fuzz-alloc sets this against the same program run as its language defines it (MiniFuzz.lean).
*/
#include "rt.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

static void * region;
static size_t region_size;

void * silo_plat_heap(size_t * size) {
    *size = region_size;
    return region;
}

_Noreturn void rt_stop(char const * why) {
    printf("stop %s\n", why);
    fflush(stdout);
    exit(0);
}

LEAN_NORETURN void lean_internal_panic_out_of_memory(void) {
    printf("oom\n");
    fflush(stdout);
    exit(0);
}

int main(int argc, char ** argv) {
    if (argc != 2) return 2;
    region_size = (size_t)strtoull(argv[1], NULL, 10);
    region = mmap(NULL, region_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
    if (region == MAP_FAILED) return 2;
    printf("%llu\n", (unsigned long long)(uintptr_t)region);
    fflush(stdout);
    char what;
    unsigned long long a, b;
    while (scanf(" %c %llu %llu", &what, &a, &b) == 3) {
        uint64_t word = 0;
        switch (what) {
        case 'm': word = (uint64_t)(uintptr_t)rt_malloc((size_t)a); break;
        case 'f': rt_free((void *)(uintptr_t)a); break;
        case 'w': word = b; memcpy((void *)(uintptr_t)a, &word, sizeof word); word = 0; break;
        case 'r': memcpy(&word, (void *)(uintptr_t)a, sizeof word); break;
        case 'q': return 0;
        default: return 2;
        }
        printf("%llu\n", (unsigned long long)word);
        fflush(stdout);
    }
    return 0;
}
