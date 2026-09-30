//! Where a run starts and how it ends: the entry point and the panic.

use core::arch::global_asm;

// The run starts here: a stack, `main`, the output made from what was committed, then
// `exit` with it in `a0..a3`.
global_asm!(
    ".section .text._start",
    ".globl _start",
    "_start:",
    ".option push",
    ".option norelax",
    "la sp, __stack_top",
    ".option pop",
    "call main",
    "call {finish}",
    "la t0, {output}",
    "ld a0, 0(t0)",
    "ld a1, 8(t0)",
    "ld a2, 16(t0)",
    "ld a3, 24(t0)",
    "li a7, 93",
    "ecall",
    finish = sym crate::io::vm::finish,
    output = sym crate::io::vm::OUTPUT,
);

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    // `unimp`: an illegal instruction, so a panicking run has no proof.
    unsafe { core::arch::asm!("unimp", options(noreturn)) }
}
