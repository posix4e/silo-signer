/*
Linker script for bare-metal AArch64 Tricorder OS.

Page-aligned section boundaries enforce strict W^X in Stage-1 MMU tables:
  [__text_start .. __text_end)      -> Normal-WB, EL1 RO, EL1 Exec, UXN=1
  [__rodata_start .. __rodata_end)  -> Normal-WB, EL1 RO, PXN=1, UXN=1
  [__stack_guard .. __stack_bottom) -> UNMAPPED (64 KiB guard hole; overflow traps cleanly on SP_EL1!)
  [__stack_bottom .. __stack_top)   -> Normal-WB, EL1 RW, PXN=1, UXN=1 (1 MiB main EL1t stack)
  [__exc_stack_bot .. __exc_stack_top) -> Normal-WB, EL1 RW, PXN=1, UXN=1 (32 KiB exception SP_EL1)
  [__data_start .. __bss_end)       -> Normal-WB, EL1 RW, PXN=1, UXN=1
  [__image_end ..)                  -> Heap (64 MiB) + DMA/Framebuffer arena (16 MiB)
*/

ENTRY(_image_start)

/* Default load base for QEMU -M virt (0x40000000 + text_offset 0x200000).
   Override with --defsym=LOAD_BASE=0x80200000 for Pixel 9 Pro XL (komodo). */
PROVIDE(LOAD_BASE = 0x40200000);

SECTIONS {
    . = LOAD_BASE;
    __image_start = .;

    .text.boot : ALIGN(4096) {
        __text_start = .;
        KEEP(*(.text.head))
        *(.text.boot)
    }

    .text : ALIGN(4096) {
        *(.text .text.*)
        . = ALIGN(4096);
        __text_end = .;
    }

    .rodata : ALIGN(4096) {
        __rodata_start = .;
        *(.rodata .rodata.*)
        *(.data.rel.ro .data.rel.ro.*)
        *(.got .got.*)
        . = ALIGN(4096);
        __rodata_end = .;
    }

    /* Separate writable data & BSS on fresh 4 KiB page boundary */
    .data : ALIGN(4096) {
        __data_start = .;
        *(.data .data.*)
        . = ALIGN(4096);
        __file_end = .;
    }

    __file_size = __file_end - __image_start;

    .bss (NOLOAD) : ALIGN(4096) {
        __bss_start = .;
        *(.bss .bss.*)
        *(COMMON)
        . = ALIGN(4096);
        __bss_end = .;

        /* Dedicated 32 KiB EL1 exception stack (SP_EL1) */
        __exc_stack_bot = .;
        . += 0x8000;
        __exc_stack_top = .;

        /* 64 KiB UNMAPPED stack guard hole directly beneath the main stack! */
        . = ALIGN(65536);
        __stack_guard = .;
        . += 0x10000;
        __stack_bottom = .;

        /* 1 MiB main thread stack (SP_EL0 in EL1t mode) */
        . += 0x100000;
        __stack_top = .;

        /* 2 MiB of zeroed page-table pool for Stage-1 L1/L2/L3 tables */
        . = ALIGN(4096);
        __pt_pool_start = .;
        . += 0x200000;
        __pt_pool_end = .;

        . = ALIGN(2097152);
        __image_end = .;
    }

    __image_size = __image_end - __image_start;

    /DISCARD/ : {
        *(.comment)
        *(.eh_frame*)
        *(.note*)
    }
}
