//! The verifier as a bare-metal RV64IM program.
//!
//! The loader puts the input, a sequence of little-endian 64-bit words, at `INPUT` and its length in words in `a0`,
//! and jumps to `_start`. The program halts (`ECALL` with `t0 = 0`) with `a0` = 1 if the proof verifies, 0 if the
//! verifier rejects it, and 2 if the input is malformed or memory runs out; a panic traps (`panic = "immediate-abort"`).
//! The input, in words:
//!
//! ```text
//! bytecode: n, then n table words
//! public input: 4 words (the 32 bytes, little-endian)
//! stream: n, then n scalars of 3 words each
//! openings: n phases; each phase: n paths; each path: leaf index, leaf length l, l words, height h, h digests of 4 words
//! ```
#![no_std]
#![no_main]

extern crate alloc;

use alloc::vec::Vec;
use core::alloc::{GlobalAlloc, Layout};
use core::arch::{asm, global_asm};
use verifier::{Bytecode, E, K, MerklePath, Proof, verify_execution};

const INPUT: usize = 0x1000_0000;
const HEAP_START: usize = 0x2000_0000;
const HEAP_END: usize = 0x7800_0000;

const ACCEPT: u64 = 1;
const REJECT: u64 = 0;
const ABORT: u64 = 2;

global_asm!(
    ".section .text.entry",
    ".globl _start",
    "_start:",
    ".option push",
    ".option norelax",
    "la gp, __global_pointer$",
    ".option pop",
    "li sp, 0xbffffff0",
    "call main",
    "li t0, 0",
    "ecall",
);

fn halt(verdict: u64) -> ! {
    unsafe { asm!("ecall", in("t0") 0, in("a0") verdict, options(noreturn)) }
}

/// Never frees: the program runs once.
struct Bump;
static mut NEXT: usize = HEAP_START;

unsafe impl GlobalAlloc for Bump {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        unsafe {
            let start = NEXT.next_multiple_of(layout.align());
            match start.checked_add(layout.size()) {
                Some(end) if end <= HEAP_END => {
                    NEXT = end;
                    start as *mut u8
                }
                _ => halt(ABORT),
            }
        }
    }

    unsafe fn dealloc(&self, _: *mut u8, _: Layout) {}
}

#[global_allocator]
static ALLOCATOR: Bump = Bump;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    halt(ABORT)
}

struct Input<'a>(&'a [u64]);

impl Input<'_> {
    fn word(&mut self) -> u64 {
        match self.0.split_first() {
            Some((&word, rest)) => {
                self.0 = rest;
                word
            }
            None => halt(ABORT),
        }
    }

    fn words(&mut self, n: u64) -> &[u64] {
        if n > self.0.len() as u64 {
            halt(ABORT)
        }
        let (head, rest) = self.0.split_at(n as usize);
        self.0 = rest;
        head
    }

    fn scalar(&mut self) -> E {
        E { c0: self.word(), c1: self.word(), c2: self.word() }
    }

    fn digest(&mut self) -> [u8; 32] {
        let mut bytes = [0u8; 32];
        for chunk in bytes.as_chunks_mut::<8>().0 {
            *chunk = self.word().to_le_bytes();
        }
        bytes
    }
}

#[unsafe(no_mangle)]
extern "C" fn main(len: u64) -> u64 {
    let mut input = Input(unsafe { core::slice::from_raw_parts(INPUT as *const u64, len as usize) });
    let n = input.word();
    let bytecode = Bytecode::new(input.words(n));
    let public_input = input.digest();
    let n = input.word();
    let stream: Vec<E> = (0..n).map(|_| input.scalar()).collect();
    let phases = input.word();
    let merkle_openings = (0..phases)
        .map(|_| {
            let paths = input.word();
            (0..paths)
                .map(|_| {
                    let leaf_index = input.word();
                    let l = input.word();
                    let leaf = input.words(l).iter().map(|&word| K(word)).collect();
                    let h = input.word();
                    let siblings = (0..h).map(|_| input.digest()).collect();
                    MerklePath { leaf_index, leaf, siblings }
                })
                .collect()
        })
        .collect();
    if !input.0.is_empty() {
        halt(ABORT)
    }
    let proof = Proof { stream, merkle_openings };
    match verify_execution(&bytecode, &public_input, &proof) {
        Ok(_) => ACCEPT,
        Err(_) => REJECT,
    }
}
