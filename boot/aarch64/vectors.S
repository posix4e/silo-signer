/*
AArch64 EL1 Exception Vector Table (`boot/aarch64/vectors.S`).

2 KiB-aligned (`16 × 128 bytes`). Every unexpected synchronous fault (W^X violation, null deref,
stack guard overflow, unmapped MMIO read/write, illegal instruction) automatically enters on the
dedicated `SP_EL1` exception stack, saves ESR_EL1 / FAR_EL1 / ELR_EL1, and calls
`early_fault_handler(esr, far, elr, kind)` which reports the exact violation and halts cleanly!
*/

.section .text.boot, "ax"
.balign 2048
.global tricorder_vectors
tricorder_vectors:

.macro VEC kind
.balign 128
    mov     x3, #\kind
    b       .Lfault_common
.endm

    /* Current EL with SP_EL0 (our normal execution mode EL1t!) */
    VEC 0    /* Synchronous */
    VEC 1    /* IRQ */
    VEC 2    /* FIQ */
    VEC 3    /* SError */

    /* Current EL with SP_ELx */
    VEC 4    /* Synchronous */
    VEC 5    /* IRQ */
    VEC 6    /* FIQ */
    VEC 7    /* SError */

    /* Lower EL using AArch64 */
    VEC 8
    VEC 9
    VEC 10
    VEC 11

    /* Lower EL using AArch32 */
    VEC 12
    VEC 13
    VEC 14
    VEC 15

.Lfault_common:
    /* Ensure we are running on SP_EL1 (exception stack) cleanly. */
    msr     SPSel, #1
    mrs     x0, ESR_EL1
    mrs     x1, FAR_EL1
    mrs     x2, ELR_EL1
    bl      early_fault_handler
1:
    wfi
    b       1b
