/*
Bare-metal AArch64 entry stub (`boot/aarch64/entry.S`).

Starts with the exact 64-byte ARM64 Linux `Image` header (`ARM\x64` magic at +0x38) so BOTH
`qemu-system-aarch64 -M virt -kernel` AND Pixel 9 Pro XL's ABL (`boot.img` v4) jump directly here.

Responsibilities (kept minimal and auditable):
  1. Park secondary cores (MPIDR_EL1.Aff0 != 0).
  2. Save bootloader's FDT pointer (`x0`) and initial exception level.
  3. Drop cleanly from EL2 -> EL1h if entered at EL2 (allowing EL1 CNTVCT access).
  4. Enable FP/SIMD (no traps) and ARMv8.4 FEAT_DIT (`PSTATE.DIT = 1`, data-independent timing).
  5. Zero `.bss`, install `VBAR_EL1` exception vector table, set `SP_EL1` = exception stack and
     `SP_EL0` = guarded main stack, switch to EL1t (`SPSel = 0`) so stack overflow traps onto
     the separate `SP_EL1` exception stack without ever triple-faulting!
  6. Call `early_boot(fdt_phys, initial_el)`.
*/

.section .text.head, "ax"
.global _image_start
_image_start:
    b       _start_code              /* 0x00: code0 — branch over header */
    .word   0                        /* 0x04: code1 */
    .quad   0x0000000000200000       /* 0x08: text_offset = 2 MiB (LOAD_BASE = RAM + 2 MiB) */
    .quad   __image_size             /* 0x10: image_size (includes .bss, stacks, page tables) */
    .quad   0x000000000000000A       /* 0x18: flags: LE, 4K pages, place anywhere */
    .quad   0                        /* 0x20: res2 */
    .quad   0                        /* 0x28: res3 */
    .quad   0                        /* 0x30: res4 */
    .ascii  "ARM\x64"                /* 0x38: Linux ARM64 Image magic */
    .word   0                        /* 0x3c: res5 */

.section .text.boot, "ax"
.global _start_code
_start_code:
    /* Mask all interrupts (DAIF) immediately. */
    msr     DAIFSet, #0xf

    /* Save FDT physical address (`x0`) in x19 and initial EL in x20. */
    mov     x19, x0
    mrs     x20, CurrentEL
    lsr     x20, x20, #2

    /* If entered at EL2, configure EL1 AArch64 (no FP/timer traps) and ERET down to EL1h. */
    cmp     x20, #2
    b.ne    .Lat_el1

    mov     x1, #(1 << 31)           /* HCR_EL2.RW = 1 (EL1 is AArch64, E2H = 0) */
    msr     HCR_EL2, x1
    msr     CPTR_EL2, xzr            /* Do NOT trap FP/SIMD/SVE from EL1 to EL2! */
    mov     x1, #3                   /* CNTHCTL_EL2: EL1PCTEN | EL1PCEN */
    msr     CNTHCTL_EL2, x1
    msr     CNTVOFF_EL2, xzr
    msr     SCTLR_EL1, xzr
    mov     x1, #0x3c5               /* SPSR_EL2: DAIF masked, EL1h */
    msr     SPSR_EL2, x1
    adr     x1, .Lat_el1
    msr     ELR_EL2, x1
    isb
    eret

.Lat_el1:
    /* Enable FP/SIMD at EL1 (CPACR_EL1.FPEN = 0b11). */
    mov     x1, #(3 << 20)
    msr     CPACR_EL1, x1
    isb

    /* Self-relocate to linked LOAD_BASE (`_image_start`) if bootloader (e.g. Pixel ABL) loaded us elsewhere! */
    adr     x21, _image_start        /* actual physical address where ABL/QEMU loaded us */
    ldr     x22, =_image_start       /* linked LOAD_BASE */
    cmp     x21, x22
    b.eq    .Lrelocated
    ldr     x23, =__file_size        /* exact loaded bytes (.text + .rodata + .data) */
    cmp     x22, x21
    b.lo    .Lcopy_fwd
    /* Backward copy (safe if destination overlaps above source) */
    add     x1, x21, x23
    add     x2, x22, x23
.Lcopy_bwd:
    cbz     x23, .Lcopy_done
    sub     x23, x23, #8
    ldr     x3, [x1, #-8]!
    str     x3, [x2, #-8]!
    b       .Lcopy_bwd
.Lcopy_fwd:
    mov     x1, x21
    mov     x2, x22
.Lcopy_fwd_loop:
    cbz     x23, .Lcopy_done
    sub     x23, x23, #8
    ldr     x3, [x1], #8
    str     x3, [x2], #8
    b       .Lcopy_fwd_loop
.Lcopy_done:
    dsb     sy
    ic      iallu
    dsb     sy
    isb
    ldr     x1, =.Lrelocated
    br      x1

.Lrelocated:
    /* Enable ARMv8.4 FEAT_DIT (Data-Independent Timing) if supported: ID_AA64PFR0_EL1[51:48] != 0. */
    mrs     x1, ID_AA64PFR0_EL1
    ubfx    x1, x1, #48, #4
    cbz     x1, .Lno_dit
    mov     x2, #(1 << 24)           /* DIT bit [24] in S3_3_C4_C2_5 */
    msr     S3_3_C4_C2_5, x2
    isb
.Lno_dit:

    /* Zero .bss + page-table pool (aligned 8 bytes). */
    adrp    x1, __bss_start
    add     x1, x1, :lo12:__bss_start
    adrp    x2, __image_end
    add     x2, x2, :lo12:__image_end
.Lzero_bss:
    cmp     x1, x2
    b.hs    .Lzero_done
    str     xzr, [x1], #8
    b       .Lzero_bss
.Lzero_done:

    /* Install EL1 exception vector table. */
    adrp    x1, tricorder_vectors
    add     x1, x1, :lo12:tricorder_vectors
    msr     VBAR_EL1, x1
    isb

    /* Set SP_EL1 = dedicated exception stack, SP_EL0 = guarded main stack, then select SP_EL0 (EL1t). */
    adrp    x1, __exc_stack_top
    add     x1, x1, :lo12:__exc_stack_top
    mov     sp, x1

    adrp    x2, __stack_top
    add     x2, x2, :lo12:__stack_top
    msr     SP_EL0, x2
    msr     SPSel, #0                /* Switch to EL1t (SP_EL0); faults automatically switch back to SP_EL1! */
    isb

    mov     x0, x19                  /* arg0: fdt_phys */
    mov     x1, x20                  /* arg1: initial_el */
    bl      early_boot

.Lpark:
    wfi
    b       .Lpark
