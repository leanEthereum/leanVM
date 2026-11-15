//! A program as both provers prove it and every verifier checks it: the compiler's output, its bytecode encoded into
//! the one public table, and that table prepared for the verifier.

use crate::{CompiledProgram, Op};
use std::ops::{Deref, Range};
use std::sync::{Arc, OnceLock};
use verifier::K;
use verifier::layout::{BUS_BITS, OP_DEREF, OP_JUMP, OP_KECCAK, OP_MUL, OP_SET, OP_XOR};

/// Operand slots of a bytecode tuple, after the opcode.
const BYTECODE_OPERANDS: usize = 12;

/// The bus tuple coordinate of the opcode: a bytecode tuple leads with its tag, pc and read count.
const OPCODE_SLOT: usize = 3;
const _: () = assert!(OPCODE_SLOT + 1 + BYTECODE_OPERANDS <= 1 << BUS_BITS);

/// The public columns of a bytecode, one word an instruction: the opcode, then the operand slots.
pub type BytecodeColumns = [Column; 1 + BYTECODE_OPERANDS];

/// A run of words in a shared table, cheap to clone: a bytecode column, a slot of [`Program::table`].
#[derive(Clone, Debug)]
pub struct Column {
    table: Arc<[u64]>,
    words: Range<usize>,
}

/// The whole of `words`.
impl From<Vec<u64>> for Column {
    fn from(words: Vec<u64>) -> Self {
        Self {
            words: 0..words.len(),
            table: words.into(),
        }
    }
}

impl Deref for Column {
    type Target = [u64];

    fn deref(&self) -> &[u64] {
        &self.table[self.words.clone()]
    }
}

/// A compiled program with its bytecode table, computed once.
#[derive(Debug)]
pub struct Program {
    compiled: CompiledProgram,
    /// The stacked bytecode polynomial's evaluations: `2^BUS_BITS` slots of `prog.len()` words, slot `s` holding bus
    /// tuple coordinate `s` of every instruction (the columns from [`OPCODE_SLOT`] on, zeros elsewhere). It is what
    /// the Fiat-Shamir IV hashes and what a deferred bytecode claim evaluates.
    table: Arc<[u64]>,
    /// The table prepared for the verifier, with the IV.
    bytecode: verifier::Bytecode,
}

/// # Panics
///
/// If the bytecode is not a power of two long.
impl From<CompiledProgram> for Program {
    fn from(compiled: CompiledProgram) -> Self {
        let n = compiled.prog.len();
        assert!(n.is_power_of_two(), "the bytecode must be a power of two long, not {n}");
        let mut table = vec![0; n << BUS_BITS];
        for (pc, op) in compiled.prog.iter().enumerate() {
            for (i, word) in encode(op).into_iter().enumerate() {
                table[(OPCODE_SLOT + i) * n + pc] = word;
            }
        }
        let bytecode = verifier::Bytecode::new(&table);
        Self {
            compiled,
            table: table.into(),
            bytecode,
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
    /// The bytecode's public columns, which ride the bus's bytecode blocks: the table's slots from [`OPCODE_SLOT`] on.
    pub fn columns(&self) -> BytecodeColumns {
        let n = self.prog.len();
        std::array::from_fn(|i| Column {
            table: self.table.clone(),
            words: (OPCODE_SLOT + i) * n..(OPCODE_SLOT + i + 1) * n,
        })
    }

    /// The stacked bytecode polynomial (§sec:e2e-bc): the columns at their bus tuple coordinates, along `2^BUS_BITS`
    /// slots. An outermost verifier is handed it in place of the program.
    pub fn table(&self) -> &[u64] {
        &self.table
    }

    /// [`Self::table`] as the verifier takes it, and the Fiat-Shamir IV every proof of the program starts from.
    pub fn bytecode(&self) -> &verifier::Bytecode {
        &self.bytecode
    }
}

/// An instruction's bytecode tuple after its pc: the opcode `g^op`, then the operand slots, offsets as g-powers, a
/// `SET` immediate as its two limbs and the flags as 0 or 1. Unused slots are zero.
fn encode(op: &Op) -> [u64; 1 + BYTECODE_OPERANDS] {
    let flag = u64::from;
    let (opcode, operands): (usize, Vec<u64>) = match *op {
        Op::Xor { a, b, c } => (OP_XOR, vec![g_pow(a), g_pow(b), g_pow(c)]),
        Op::Mul { a, b, c } => (OP_MUL, vec![g_pow(a), g_pow(b), g_pow(c)]),
        Op::Set { o, k } => (OP_SET, vec![g_pow(o), k.c0, k.c1]),
        Op::Deref { o1, o2, o3, mode } => (
            OP_DEREF,
            vec![g_pow(o1), g_pow(o2), g_pow(o3), flag(mode.f_pc()), flag(mode.f_fp())],
        ),
        Op::Jump { oc, od, of } => (OP_JUMP, vec![g_pow(oc), g_pow(od), g_pow(of)]),
        Op::Keccak {
            m,
            tail,
            b8,
            cap,
            out,
            in_odd,
            out_odd,
            out_cells,
        } => {
            let (out_two, out_all) = out_cells.flags();
            let mut operands: Vec<u64> = m.into_iter().chain([tail, b8, cap, out]).map(g_pow).collect();
            operands.extend([in_odd, out_odd, out_two, out_all].map(flag));
            (OP_KECCAK, operands)
        }
    };
    let mut tuple = [0; 1 + BYTECODE_OPERANDS];
    tuple[0] = g_pow(opcode as u32);
    tuple[1..=operands.len()].copy_from_slice(&operands);
    tuple
}

/// `g^e` for `g = x`, from two tables of `2^16` powers built once: `e = hi·2^16 + lo`.
fn g_pow(e: u32) -> u64 {
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
    /// The split tables against square-and-multiply, on both sides of the `2^16` boundary and at the ends of the range.
    #[test]
    fn g_pow_matches_square_and_multiply() {
        for e in [0, 1, 63, 64, (1 << 16) - 1, 1 << 16, (1 << 16) + 1, 1 << 28, u32::MAX] {
            assert_eq!(super::g_pow(e), verifier::E::new(2, 0).pow(u64::from(e)).c0, "g^{e}");
        }
    }
}
