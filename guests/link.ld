/* The memory map of lean_vm::rv. Text and RAM share one 2 GiB window (the medany code
   model) below 0x7FFFF800, and each base is a multiple of its region's largest size. */
ENTRY(_start)

MEMORY {
  TEXT (rx)   : ORIGIN = 0x10000000, LENGTH = 256M
  ADVICE (rw) : ORIGIN = 0x20000000, LENGTH = 64K
  RAM (rw)    : ORIGIN = 0x40000000, LENGTH = 1M
}

SECTIONS {
  .text : { KEEP(*(.text._start)) *(.text .text.*) } > TEXT

  /* RAM's first four words are the run's public input: nothing is loaded there. */
  .input (NOLOAD) : { __input = .; . += 32; } > RAM
  /* Everything that is not code lives in RAM: the text is not mapped as data. */
  .data : {
    *(.rodata .rodata.* .srodata .srodata.*)
    *(.data .data.* .sdata .sdata.*)
    *(.got .got.*)
  } > RAM
  /* RAM is zero wherever nothing is loaded, so there is no .bss to clear. */
  .bss (NOLOAD) : { *(.bss .bss.* .sbss .sbss.*) } > RAM

  /* The stack grows down from the end of RAM, which also tells the loader RAM's size. */
  __stack_top = ORIGIN(RAM) + LENGTH(RAM);
  /* The advice region: nothing is loaded there, the prover fills it. Its end tells the loader its size. */
  __advice = ORIGIN(ADVICE);
  __advice_top = ORIGIN(ADVICE) + LENGTH(ADVICE);

  /DISCARD/ : { *(.eh_frame .eh_frame_hdr .comment .riscv.attributes) }
}
