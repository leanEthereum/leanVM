//! The machine's custom instructions, the precompiles: each proven as one row rather than
//! as the RISC-V instructions it replaces. They exist on the VM only.

use crate::blake2s::Block;
use core::mem::MaybeUninit;

/// The BLAKE2s compression of message block `m` onto chaining value `h`, `t` bytes into
/// the message, `last` on the final block: one `blake2s` instruction (custom-0, opcode
/// `0x0b`, four registers: the result's pointer, the chaining value's, the message's, and
/// the counter; `funct2` bit 0 the finalization flag).
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
        let (h, out, m) = (&raw const (*base).h, &raw mut (*base).out, &raw const (*base).m);
        if last {
            core::arch::asm!(".insn r4 0x0b, 0, 1, {0}, {1}, {2}, {3}", in(reg) out, in(reg) h, in(reg) m, in(reg) t, options(nostack));
        } else {
            core::arch::asm!(".insn r4 0x0b, 0, 0, {0}, {1}, {2}, {3}", in(reg) out, in(reg) h, in(reg) m, in(reg) t, options(nostack));
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
            ".insn r4 0x0b, 0, 1, {out}, {base}, {m}, {t}",
            "ld {v0}, 32({base})",
            "ld {v1}, 40({base})",
            "addi {c}, {c}, 1",
            "bne {c}, {end}, 1b",
            "2:",
            base = in(reg) base,
            out = in(reg) &raw mut (*base).out,
            m = in(reg) &raw const (*base).m,
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

/// One extension-field instruction (custom-1, opcode `0x2b`) on the extension registers `fD`, `fA` and `fB`.
///
/// `FUNCT3` is the instruction: bit 0 accumulates into `fD`, and bit 2 requires a zero result.
///
/// A register's number is its five-bit field, then two bits of the function-7 field, `fD`'s lowest.
#[inline(always)]
pub fn ext<const FUNCT3: u32, const D: u8, const A: u8, const B: u8>() {
    // SAFETY: the instruction reads and writes extension registers alone, which the compiler knows nothing of.
    unsafe {
        core::arch::asm!(
            ".4byte {word}",
            word = const {
                let (d, a, b) = (D as u32, A as u32, B as u32);
                0x2b | (d & 31) << 7
                    | FUNCT3 << 12
                    | (a & 31) << 15
                    | (b & 31) << 20
                    | (d >> 5 | (a >> 5) << 2 | (b >> 5) << 4) << 25
            },
            options(nomem, nostack, preserves_flags),
        );
    }
}

/// One extension-field instruction whose second operand is the base-field word `b`, in an integer register.
///
/// `FUNCT3` is the instruction, its bit 1 set: bit 0 accumulates into `fD`, and bit 2 requires a zero result.
#[inline(always)]
pub fn ext_base<const FUNCT3: u32, const D: u8, const A: u8>(b: u64) {
    // SAFETY: the instruction reads `b`'s register, and reads and writes extension registers alone.
    unsafe {
        core::arch::asm!(
            ".insn r 0x2b, {f3}, {f7}, x{d}, x{a}, {b}",
            f3 = const FUNCT3,
            f7 = const { (D as u32) >> 5 | ((A as u32) >> 5) << 2 },
            d = const { D & 31 },
            a = const { A & 31 },
            b = in(reg) b,
            options(nomem, nostack, preserves_flags),
        );
    }
}
