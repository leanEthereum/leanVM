//! Per-opcode trace rows, emitted during execution and assembled into a [`Trace`].
//!
//! A row carries only what the witness fill cannot recover: the step's
//! `(pc, fp)`, the access counts read at access time, and `DEREF`'s resolved
//! store index. Everything else is a function of those:
//! operands and immediates come from `prog[pc]`, addresses from `fp` plus those
//! operands, and values from the final memory image, which is write-once and so
//! still holds what each accessed cell held at the time it was accessed. The
//! rows are the interpreter's largest write stream, so what they do not carry
//! they do not pay for, twice: once writing them and once reading them back.
//!
//! An access count is held as its exponent: the column holds `g^k`, the row `k`,
//! and the fill looks the power up.

/// `XOR` or `MUL` row: the three cells are `fp·g^{a,b,c}`.
pub(crate) struct Xrow {
    pub(crate) pc: u32,
    pub(crate) fp: u32, // frame base: address = fp + offset, operand = g^offset
    pub(crate) ra: u32,
    pub(crate) rb: u32,
    pub(crate) rc: u32,
    pub(crate) bytecode_read: u32,
}
pub(crate) struct Srow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) r: u32,
    pub(crate) bytecode_read: u32,
}
pub(crate) struct Drow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) r1: u32,
    pub(crate) r2: u32,
    pub(crate) r3: u32,
    pub(crate) bytecode_read: u32,
}
pub(crate) struct Jrow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) rc: u32,
    pub(crate) rd: u32,
    pub(crate) rf: u32,
    pub(crate) bytecode_read: u32,
}

/// `KECCAK` row: the per-cell memory access counts, in the order the table flushes
/// them (`tables::KeccakOp::cell`): the four `m` cells, the four `tail` cells, `b8`, the
/// four `cap` cells, then the thirteen output cells, zero for one the row does not write.
/// The input lanes are read back from the final memory image, the output lanes their permutation.
pub(crate) struct Krow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) r: [u32; crate::keccak::ROW_CELLS],
    pub(crate) bytecode_read: u32,
}

pub(crate) struct Trace {
    pub(crate) xor: Vec<Xrow>,
    pub(crate) mul: Vec<Xrow>,
    pub(crate) set: Vec<Srow>,
    pub(crate) deref: Vec<Drow>,
    pub(crate) jump: Vec<Jrow>,
    pub(crate) keccak: Vec<Krow>,
    pub(crate) bytecode_count: Vec<u32>, // per-pc execution count; the column holds g^{A[pc]}
    /// One past the highest access count, of a cell or a pc: the `g`-powers a fill looks up.
    pub(crate) counts: usize,
}

impl Trace {
    /// Rows per instruction table, in [`crate::cpu::Stats::TABLES`] order.
    pub(crate) fn row_counts(&self) -> [usize; crate::tables::N_TABLES] {
        [
            self.xor.len(),
            self.mul.len(),
            self.set.len(),
            self.deref.len(),
            self.jump.len(),
            self.keccak.len(),
        ]
    }
}
