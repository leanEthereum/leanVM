/* ACT4's test layout on leanVM's memory map (sdk/link.ld): the code in the text,
   every other section in RAM, and one word of advice. Sail runs the same file on the
   regions sail.json describes, so the two agree on every address.
   RAM is the smallest power of two holding the image, the loader reading its size off
   __stack_top: the tests use no stack. */
OUTPUT_ARCH("riscv")
ENTRY(rvtest_entry_point)

MEMORY {
  TEXT (rx)   : ORIGIN = 0x10000000, LENGTH = 256M
  ADVICE (rw) : ORIGIN = 0x20000000, LENGTH = 8
  RAM (rw)    : ORIGIN = 0x40000000, LENGTH = 1M
}

PROVIDE(__stack_size = 0);
PROVIDE(__num_harts = 1);

SECTIONS {
  /* Separate output sections, so that a test's alignment does not move the entry. The
     model's code comes last: it differs between the self-checking build and Sail's. */
  .text.init ORIGIN(TEXT) : { *(.text.init) } > TEXT
  .text.rvtest : { *(.text.rvtest) *(.text.rvtest.*) } > TEXT
  .text.rvmodel : { *(.text.rvmodel) *(.text.rvmodel.*) *(.text) *(.text.*) } > TEXT

  .data ORIGIN(RAM) : {
    *(.rodata) *(.rodata.*) *(.srodata) *(.srodata.*)
    *(.data) *(.data.*) *(.sdata) *(.sdata.*)
  } > RAM
  /* Sail's tohost, which the self-checking build does not have. */
  .tohost : { *(.tohost) } > RAM
  .bss (NOLOAD) : {
    __bss_start = .;
    *(.sbss) *(.sbss.*) *(.bss) *(.bss.*) *(COMMON)
    __bss_end = .;
  } > RAM

  __stack_bottom = .;
  _end = .;
  __stack_top = ORIGIN(RAM) + (1 << LOG2CEIL(_end - ORIGIN(RAM)));
  __advice_top = ORIGIN(ADVICE) + LENGTH(ADVICE);
  ASSERT(__stack_top <= ORIGIN(RAM) + LENGTH(RAM), "the test does not fit RAM: grow RAM here and in sail.json")

  /DISCARD/ : { *(.comment) }
}
