//! The runtime of a leanVM guest: where a run starts, how it ends, its public input
//! and output. A guest is a `no_std`, `no_main` binary defining
//!
//! ```ignore
//! #[unsafe(no_mangle)]
//! extern "C" fn main() { leanvm_guest::output([..]) }
//! ```
//!
//! The environment has no traps to handle: an illegal instruction, a misaligned or
//! unmapped access, or an `ecall` that is not `exit` leave a run with no proof. So a
//! panic is one illegal instruction, and nothing else is needed.
#![no_std]

use core::arch::global_asm;

// The run starts here: a stack, `main`, then `exit` with the output in `a0..a3`.
global_asm!(
    ".section .text._start",
    ".globl _start",
    "_start:",
    ".option push",
    ".option norelax",
    "la sp, __stack_top",
    ".option pop",
    "call main",
    "la t0, {output}",
    "ld a0, 0(t0)",
    "ld a1, 8(t0)",
    "ld a2, 16(t0)",
    "ld a3, 24(t0)",
    "li a7, 93",
    "ecall",
    output = sym OUTPUT,
);

static mut OUTPUT: [u64; 4] = [0; 4];

unsafe extern "C" {
    /// RAM's first four words, and the advice region's bounds (`link.ld`).
    static __input: [u64; 4];
    static __advice: u64;
    static __advice_top: u64;
}

/// The run's public input.
pub fn input() -> [u64; 4] {
    // SAFETY: the linker script reserves these words, and nothing writes them.
    unsafe { core::ptr::read_volatile(&raw const __input) }
}

/// The advice: words the prover supplies, which the statement says nothing about, so
/// a guest has to check what it reads here.
pub fn advice() -> &'static [u64] {
    // The two symbols bound the region without belonging to one object, so the length
    // is address arithmetic rather than `offset_from`, which asks for one allocation.
    let (start, end) = (&raw const __advice, &raw const __advice_top);
    let words = (end as usize - start as usize) / size_of::<u64>();
    // SAFETY: the linker script reserves the region, it holds whole words, and nothing
    // in this crate writes it.
    unsafe { core::slice::from_raw_parts(start, words) }
}

/// Set the run's public output, which the run returns in `a0..a3` when `main` does.
pub fn output(words: [u64; 4]) {
    // SAFETY: one hart, no interrupts: nothing else touches `OUTPUT`.
    unsafe { core::ptr::write_volatile(&raw mut OUTPUT, words) }
}

/// The block the `blake2s` instruction works on (`lean_vm::rv::hash`): the chaining
/// value, where the result goes, then the message, at an address aligned to the block
/// so that word `k` of it is the cell at `base ^ 8k`.
#[repr(C, align(128))]
struct Block {
    h: [u32; 8],
    out: [u32; 8],
    m: [u8; 64],
}

/// Streaming BLAKE2s-256 through the machine's compression instruction.
pub struct Blake2s {
    block: Block,
    /// Bytes of the message in the block, and bytes compressed before them.
    filled: usize,
    done: u64,
}

impl Default for Blake2s {
    fn default() -> Self {
        Self::new()
    }
}

impl Blake2s {
    pub fn new() -> Self {
        // The IV with the parameter block folded in: no key, a 32-byte digest.
        let mut h = [
            0x6A09_E667, 0xBB67_AE85, 0x3C6E_F372, 0xA54F_F53A, 0x510E_527F, 0x9B05_688C, 0x1F83_D9AB, 0x5BE0_CD19,
        ];
        h[0] ^= 0x0101_0020;
        Self {
            block: Block {
                h,
                out: [0; 8],
                m: [0; 64],
            },
            filled: 0,
            done: 0,
        }
    }

    /// `blake2s` on the block, its result becoming the chaining value.
    fn compress(&mut self, last: bool) {
        let (block, t) = (&raw mut self.block, self.done + self.filled as u64);
        // SAFETY: the instruction reads and writes the block, which is what the
        // pointer names and nothing else holds; the counter is a plain register.
        unsafe {
            if last {
                core::arch::asm!(".insn r 0x0b, 1, 0, x0, {0}, {1}", in(reg) block, in(reg) t, options(nostack));
            } else {
                core::arch::asm!(".insn r 0x0b, 0, 0, x0, {0}, {1}", in(reg) block, in(reg) t, options(nostack));
            }
        }
        self.block.h = self.block.out;
    }

    pub fn update(&mut self, mut data: &[u8]) -> &mut Self {
        while !data.is_empty() {
            // A full block is held back until more input follows, since the last one
            // is compressed differently.
            if self.filled == 64 {
                self.compress(false);
                self.done += 64;
                self.filled = 0;
            }
            let n = data.len().min(64 - self.filled);
            self.block.m[self.filled..self.filled + n].copy_from_slice(&data[..n]);
            self.filled += n;
            data = &data[n..];
        }
        self
    }

    pub fn finalize(mut self) -> [u8; 32] {
        self.block.m[self.filled..].fill(0);
        self.compress(true);
        let mut out = [0u8; 32];
        for (chunk, word) in out.chunks_exact_mut(4).zip(&self.block.h) {
            chunk.copy_from_slice(&word.to_le_bytes());
        }
        out
    }

    pub fn hash(data: &[u8]) -> [u8; 32] {
        let mut hasher = Self::new();
        hasher.update(data);
        hasher.finalize()
    }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    // `unimp`: an illegal instruction, so a panicking run has no proof.
    unsafe { core::arch::asm!("unimp", options(noreturn)) }
}
