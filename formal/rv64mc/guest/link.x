/* riscv-zkvm's memory map: code in its own immutable map at 0x80000000; data, constants and the stack in the RAM
   window 0xa0000000..0xc0000000; the inputs and the heap in the low window 0x20..0x78000000. */
ENTRY(_start)
SECTIONS {
  . = 0x80000000;
  .text : { *(.text.entry) *(.text .text.*) }
  . = 0xa0000000;
  .rodata : { *(.rodata .rodata.*) *(.srodata .srodata.*) }
  .data : { *(.data .data.*) }
  .sdata : { __global_pointer$ = . + 0x800; *(.sdata .sdata.*) }
  .bss : { *(.sbss .sbss.*) *(.bss .bss.*) *(COMMON) }
  /DISCARD/ : { *(.eh_frame*) *(.comment) }
}
