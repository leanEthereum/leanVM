/* The memory map of leanvm_core::rv. Text and RAM share one 2 GiB window (the medany code
   model) below 0x7FFFF800, and each base is a multiple of its region's largest size. */
ENTRY(_start)

MEMORY {
  TEXT (rx)   : ORIGIN = 0x10000000, LENGTH = 256M
  ADVICE (rw) : ORIGIN = 0x20000000, LENGTH = 512M
  RAM (rw)    : ORIGIN = 0x40000000, LENGTH = 1023M
}

SECTIONS {
  .text : { KEEP(*(.text._start)) *(.text .text.*) } > TEXT

  /* The stack opens RAM and grows down toward its base, so an overflow leaves RAM and traps.
     A guest sets its size with `leanvm_guest::stack_words!`, 64 KiB otherwise. */
  __stack_top = ORIGIN(RAM) + (DEFINED(__stack_bytes) ? __stack_bytes : 64K);

  /* Everything else that is not code follows: the text is not mapped as data. */
  .data __stack_top : {
    *(.rodata .rodata.* .srodata .srodata.*)
    *(.data .data.* .sdata .sdata.*)
    *(.got .got.*)
  } > RAM
  /* RAM is zero wherever nothing is loaded, so there is no .bss to clear. */
  .bss (NOLOAD) : { *(.bss .bss.* .sbss .sbss.*) } > RAM

  /* RAM is the smallest power of two holding the stack and the data, which the prover commits whole. */
  __ram_top = ORIGIN(RAM) + (1 << LOG2CEIL(ADDR(.bss) + SIZEOF(.bss) - ORIGIN(RAM)));
  /* The advice region: nothing is loaded there, the prover fills it. Its end tells the loader its size,
     which a guest sets with `leanvm_guest::advice_words!`, 64 KiB otherwise. */
  __advice = ORIGIN(ADVICE);
  __advice_top = ORIGIN(ADVICE) + (DEFINED(__advice_bytes) ? __advice_bytes : 64K);

  /DISCARD/ : { *(.eh_frame .eh_frame_hdr .comment .riscv.attributes) }
}
