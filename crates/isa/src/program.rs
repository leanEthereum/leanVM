//! A compiled program with its stacked bytecode, shared by both provers.

use crate::{CompiledProgram, Op};
use std::ops::{Deref, Range};
use std::sync::OnceLock;
use verifier::K;
use verifier::layout::{BUS_BITS, OP_DEREF, OP_JUMP, OP_KECCAK, OP_MUL, OP_SET, OP_XOR};

/// Operand slots of a bytecode tuple, after the opcode.
const BYTECODE_OPERANDS: usize = 12;

/// The bus tuple coordinate of the opcode: a bytecode tuple leads with its tag, pc and read count.
const OPCODE_SLOT: usize = 3;
const _: () = assert!(OPCODE_SLOT + 1 + BYTECODE_OPERANDS <= 1 << BUS_BITS);

/// The bus coordinates the stacked bytecode fills, the opcode's and the operand slots: it is zero at every other.
pub const BYTECODE_SLOTS: Range<usize> = OPCODE_SLOT..OPCODE_SLOT + 1 + BYTECODE_OPERANDS;

/// A compiled program and its stacked bytecode.
#[derive(Debug)]
pub struct Program {
    compiled: CompiledProgram,
    /// Bus coordinate `s` of every instruction at `s * prog.len()`, for `s < 2^BUS_BITS`.
    stacked_bytecode: Vec<u64>,
    /// Its Fiat-Shamir IV, all a prover reads of the prepared bytecode.
    fiat_shamir_iv: [u8; 32],
    /// `stacked_bytecode` prepared for the verifier, on first use.
    bytecode: OnceLock<verifier::Bytecode>,
}

/// # Panics
///
/// If the bytecode is not a power of two long, or longer than `2^MAX_LOG_BYTECODE`.
impl From<CompiledProgram> for Program {
    #[inline(never)]
    fn from(compiled: CompiledProgram) -> Self {
        let n = compiled.prog.len();
        assert!(n.is_power_of_two(), "the bytecode must be a power of two long, not {n}");
        let mut stacked = vec![0; n << BUS_BITS];
        for (pc, op) in compiled.prog.iter().enumerate() {
            for (i, word) in encode(op).into_iter().enumerate() {
                stacked[(OPCODE_SLOT + i) * n + pc] = word;
            }
        }
        Self {
            compiled,
            fiat_shamir_iv: verifier::fiat_shamir_iv(&stacked),
            bytecode: OnceLock::new(),
            stacked_bytecode: stacked,
        }
    }
}

impl Deref for Program {
    type Target = CompiledProgram;

    fn deref(&self) -> &CompiledProgram {
        &self.compiled
    }
}

impl Program {
    /// The stacked bytecode (§sec:e2e-bc).
    pub fn stacked_bytecode(&self) -> &[u64] {
        &self.stacked_bytecode
    }

    /// The Fiat-Shamir IV every transcript of this program starts from.
    pub fn fiat_shamir_iv(&self) -> [u8; 32] {
        self.fiat_shamir_iv
    }

    /// [`Self::stacked_bytecode`] prepared for the verifier, built on first use.
    pub fn bytecode(&self) -> &verifier::Bytecode {
        self.bytecode.get_or_init(|| {
            verifier::Bytecode::new(&self.stacked_bytecode).expect("encode gives the encoding of a program")
        })
    }
}

/// An instruction's bytecode tuple after its pc: the opcode `g^op`, then the operand slots, offsets as g-powers, a
/// `SET` immediate as its two limbs and the flags as 0 or 1. Unused slots are zero.
fn encode(op: &Op) -> [u64; 1 + BYTECODE_OPERANDS] {
    let flag = u64::from;
    // The opcode and the first `n` offsets as exponents, then four words.
    let (exponents, n, words) = match *op {
        Op::Xor { a, b, c } => ([OP_XOR as u32, a, b, c, 0, 0, 0, 0, 0], 4, [0; 4]),
        Op::Mul { a, b, c } => ([OP_MUL as u32, a, b, c, 0, 0, 0, 0, 0], 4, [0; 4]),
        Op::Set { o, k } => ([OP_SET as u32, o, 0, 0, 0, 0, 0, 0, 0], 2, [k.c0, k.c1, 0, 0]),
        Op::Deref { o1, o2, o3, mode } => {
            let words = [flag(mode.f_pc()), flag(mode.f_fp()), 0, 0];
            ([OP_DEREF as u32, o1, o2, o3, 0, 0, 0, 0, 0], 4, words)
        }
        Op::Jump { oc, od, of } => ([OP_JUMP as u32, oc, od, of, 0, 0, 0, 0, 0], 4, [0; 4]),
        Op::Keccak {
            m: [m0, m1, m2, m3],
            tail,
            b8,
            cap,
            out,
            in_odd,
            out_odd,
            out_cells,
        } => {
            let (out_two, out_all) = out_cells.flags();
            let words = [flag(in_odd), flag(out_odd), flag(out_two), flag(out_all)];
            ([OP_KECCAK as u32, m0, m1, m2, m3, tail, b8, cap, out], 9, words)
        }
    };
    let mut tuple = [0; 1 + BYTECODE_OPERANDS];
    for (slot, &e) in tuple.iter_mut().zip(&exponents[..n]) {
        *slot = g_pow(e);
    }
    tuple[n..n + 4].copy_from_slice(&words);
    tuple
}

/// `g^e`, the word of `K`, from two tables of `2^16` powers built once, `e = hi 2^16 + lo`: one load, or two and a
/// product.
#[inline(never)]
pub fn g_pow(e: u32) -> u64 {
    static TABLES: OnceLock<[Vec<K>; 2]> = OnceLock::new();
    let [low, high] = TABLES.get_or_init(|| {
        let powers = |step: K| -> Vec<K> {
            std::iter::successors(Some(K(1)), |&power| Some(power * step))
                .take(1 << 16)
                .collect()
        };
        let low = powers(K(2));
        let high = powers(low[(1 << 16) - 1] * K(2));
        [low, high]
    });
    match e >> 16 {
        0 => low[e as usize].0,
        hi => (low[e as usize & 0xFFFF] * high[hi as usize]).0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use verifier::E;
    use verifier::layout::gpow;

    /// The split tables against square-and-multiply, on both sides of the `2^16` boundary and at the ends of the range.
    #[test]
    fn g_pow_matches_square_and_multiply() {
        for e in [0, 1, 63, 64, (1 << 16) - 1, 1 << 16, (1 << 16) + 1, 1 << 28, u32::MAX] {
            assert_eq!(E::from(K(g_pow(e))), gpow(u64::from(e)), "g^{e}");
        }
    }
}
