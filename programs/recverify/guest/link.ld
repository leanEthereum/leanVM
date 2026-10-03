/* sdk/link.ld with a larger RAM and a heap: the verifier allocates. The heap runs from the end of .bss up to
   the stack's reserved megabyte below the top of RAM. */
ENTRY(_start)

MEMORY {
  TEXT (rx)   : ORIGIN = 0x10000000, LENGTH = 256M
  ADVICE (rw) : ORIGIN = 0x20000000, LENGTH = 512M
  RAM (rw)    : ORIGIN = 0x40000000, LENGTH = 64M
}

SECTIONS {
  .text : { KEEP(*(.text._start)) *(.text .text.*) } > TEXT

  .data : {
    *(.rodata .rodata.* .srodata .srodata.*)
    *(.data .data.* .sdata .sdata.*)
    *(.got .got.*)
  } > RAM
  .bss (NOLOAD) : { *(.bss .bss.* .sbss .sbss.*) } > RAM
  . = ALIGN(16);
  __heap_start = .;

  __stack_top = ORIGIN(RAM) + LENGTH(RAM);
  __heap_end = __stack_top - 1M;
  __advice = ORIGIN(ADVICE);
  __advice_top = ORIGIN(ADVICE) + (DEFINED(__advice_bytes) ? __advice_bytes : 64K);

  /DISCARD/ : { *(.eh_frame .eh_frame_hdr .comment .riscv.attributes) }
}
