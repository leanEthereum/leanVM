//! A compiled program with its stacked bytecode, shared by both provers.

use crate::{CompiledProgram, Op};
use std::ops::Deref;
use verifier::layout::{BUS_BITS, OP_DEREF, OP_JUMP, OP_KECCAK, OP_MUL, OP_SET, OP_XOR};

/// Operand slots of a bytecode tuple, after the opcode.
const BYTECODE_OPERANDS: usize = 12;

/// The bus tuple coordinate of the opcode: a bytecode tuple leads with its tag, pc and read count.
const OPCODE_SLOT: usize = 3;
const _: () = assert!(OPCODE_SLOT + 1 + BYTECODE_OPERANDS <= 1 << BUS_BITS);

/// A compiled program and its stacked bytecode.
#[derive(Debug)]
pub struct Program {
    compiled: CompiledProgram,
    /// Bus coordinate `s` of every instruction at `s * prog.len()`, for `s < 2^BUS_BITS`.
    stacked_bytecode: Vec<u64>,
    /// `stacked_bytecode` prepared for the verifier, with its Fiat-Shamir IV.
    bytecode: verifier::Bytecode,
}

/// # Panics
///
/// If the bytecode is not a power of two long.
impl From<CompiledProgram> for Program {
    fn from(compiled: CompiledProgram) -> Self {
        let n = compiled.prog.len();
        assert!(n.is_power_of_two(), "the bytecode must be a power of two long, not {n}");
        let mut stacked = vec![0; n << BUS_BITS];
        for (pc, op) in compiled.prog.iter().enumerate() {
            for (i, word) in encode(op).into_iter().enumerate() {
                stacked[(OPCODE_SLOT + i) * n + pc] = word;
            }
        }
        let bytecode = verifier::Bytecode::new(&stacked);
        Self {
            compiled,
            stacked_bytecode: stacked,
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
    /// The stacked bytecode (§sec:e2e-bc).
    pub fn stacked_bytecode(&self) -> &[u64] {
        &self.stacked_bytecode
    }

    /// [`Self::stacked_bytecode`] prepared for the verifier, with its Fiat-Shamir IV.
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

/// An offset's operand: `g^e`.
fn g_pow(e: u32) -> u64 {
    verifier::layout::gpow_u32(e).0
}
