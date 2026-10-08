//! The machine's custom instructions: the precompiles, each proven as one row rather than
//! as the RISC-V instructions it replaces, and a hint's two markers. They exist on the VM only.

use crate::blake2s::Block;
use core::mem::MaybeUninit;

/// The BLAKE2s compression of message block `m` onto chaining value `h`, `t` bytes into
/// the message, `last` on the final block: one `blake2s` instruction (custom-0, opcode
/// `0x0b`, `funct3` the finalization flag, the counter in `rs2`).
#[inline(always)]
pub fn blake2s_compress(h: &[u64; 4], m: &[u64; 8], t: u64, last: bool) -> [u64; 4] {
    // Built here and nowhere else: a block kept in the hasher is copied whenever the hasher moves.
    let mut block = MaybeUninit::<Block>::uninit();
    let base = block.as_mut_ptr();
    // SAFETY: the chaining value and the message are written before the instruction reads
    // them, and it writes the compression before it is read.
    // The block is this frame's, and nothing else holds it.
    unsafe {
        (&raw mut (*base).h).write(*h);
        (&raw mut (*base).m).write(*m);
        blake2s_compress_in_place(base, t, last);
        (&raw const (*base).out).read().assume_init()
    }
}

/// The `blake2s` instruction on the block at `base`: its `out` becomes the compression of its `m` onto its `h`.
///
/// # Safety
///
/// `base` points to a block whose `h` and `m` are initialized and whose `out` is writable.
#[inline(always)]
pub(crate) unsafe fn blake2s_compress_in_place(base: *mut Block, t: u64, last: bool) {
    // SAFETY: the caller's; the instruction reads `h` and `m` and writes `out`.
    unsafe {
        if last {
            core::arch::asm!(".insn r 0x0b, 1, 0, x0, {0}, {1}", in(reg) base, in(reg) t, options(nostack));
        } else {
            core::arch::asm!(".insn r 0x0b, 0, 0, x0, {0}, {1}", in(reg) base, in(reg) t, options(nostack));
        }
    }
}

/// A hash chain in the one-block message of the block at `base`, `t` bytes long: for each `c` in `first..end`, the
/// `u32` at message byte `COUNTER` becomes `c`, the two words at message byte `VALUE` become `value`, and `value`
/// becomes the first two words of the final compression. Returns the last `value`: `value` itself if `first == end`.
///
/// One loop of eight instructions a step, the compression one of them: the counter doubles as the loop's.
///
/// # Safety
///
/// `base` points to a block whose `h` and `m` are initialized, whose `out` is writable, and which nothing else
/// holds; the `u32` at message byte `COUNTER` and the two words at message byte `VALUE` are aligned and inside the
/// message; `first <= end`.
#[inline(always)]
pub(crate) unsafe fn blake2s_chain<const COUNTER: usize, const VALUE: usize>(
    base: *mut Block,
    t: u64,
    first: u32,
    end: u32,
    value: [u64; 2],
) -> [u64; 2] {
    let [mut v0, mut v1] = value;
    // SAFETY: the caller's; each step writes the message's counter and value, the instruction reads `h` and `m` and
    // writes `out`, and the loop reads `out`'s first two words. The counter, zero-extended, counts up to `end`.
    unsafe {
        core::arch::asm!(
            "beq {c}, {end}, 2f",
            "1:",
            "sw {c}, {counter}({base})",
            "sd {v0}, {value}({base})",
            "sd {v1}, {value}+8({base})",
            ".insn r 0x0b, 1, 0, x0, {base}, {t}",
            "ld {v0}, 32({base})",
            "ld {v1}, 40({base})",
            "addi {c}, {c}, 1",
            "bne {c}, {end}, 1b",
            "2:",
            base = in(reg) base,
            t = in(reg) t,
            c = inout(reg) u64::from(first) => _,
            end = in(reg) u64::from(end),
            v0 = inout(reg) v0,
            v1 = inout(reg) v1,
            counter = const 64 + COUNTER,
            value = const 64 + VALUE,
            options(nostack),
        );
    }
    [v0, v1]
}

/// One extension-field instruction (custom-1, opcode `0x2b`) on the elements at `c`, `a` and `b`.
///
/// `FUNCT3` is the instruction: bit 0 accumulates into `c`, and bit 1 reads `b` as one base-field word.
///
/// # Safety
///
/// - `a` and `c` point to three readable words, and `c` to three writable ones.
/// - `b` points to three readable words, or one for a base-field `b`.
/// - Every word is 8-byte aligned.
#[inline(always)]
pub unsafe fn ext<const FUNCT3: u32>(c: *mut [u64; 3], a: *const [u64; 3], b: *const u64) {
    // SAFETY: the caller's pointers name what the instruction reads and writes, and nothing else.
    unsafe {
        core::arch::asm!(
            ".insn r 0x2b, {f3}, 0, {c}, {a}, {b}",
            f3 = const FUNCT3,
            c = in(reg) c,
            a = in(reg) a,
            b = in(reg) b,
            options(nostack, preserves_flags),
        );
    }
}

/// `hint.enter` (custom-2, opcode `0x5b`, `funct3 = 0`): false, as the proof runs it. The executor first runs the code
/// it opens with it true, unproven, to that code's [`hint_exit`], then rewinds the run to it.
#[inline(always)]
pub(crate) fn hint_enter() -> bool {
    let entered: u64;
    // SAFETY: the instruction writes its register and nothing else the proof sees; it stays a barrier to memory, so
    // the hint's words are read after it.
    unsafe { core::arch::asm!(".insn r 0x5b, 0, 0, {0}, x0, x0", out(reg) entered, options(nostack)) };
    entered != 0
}

/// `hint.exit` (custom-2, `funct3 = 1`): the `n` words at `from` become the advice words at `to`, and the hint's code
/// ends. The proof never reaches it: its entry is illegal.
///
/// # Safety
///
/// `from` points to `n` readable words.
#[inline(always)]
pub(crate) unsafe fn hint_exit(to: *const u64, from: *const u64, n: usize) -> ! {
    // SAFETY: the caller's; the executor reads the words and leaves the code.
    unsafe {
        core::arch::asm!(
            ".insn r 0x5b, 1, 0, {0}, {1}, {2}",
            in(reg) to,
            in(reg) from,
            in(reg) n,
            options(noreturn, nostack),
        )
    }
}
