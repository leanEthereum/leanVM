//! Per-opcode trace rows, emitted during execution and assembled into a [`Trace`].
//!
//! A row carries only what the witness fill cannot recover: the step's
//! `(pc, fp)` and `DEREF`'s resolved store index. Everything else is a function
//! of those: operands and immediates come from `prog[pc]`, addresses from `fp`
//! plus those operands, and values from the final memory image, which is
//! write-once and so still holds what each accessed cell held at the time it was
//! accessed. The rows are the interpreter's largest write stream, so what they do
//! not carry they do not pay for, twice: once writing them and once reading them
//! back.

/// One executed instruction: the cells it touches are `fp·g^{operand}`.
pub(crate) struct Row {
    pub(crate) pc: u32,
    pub(crate) fp: u32, // frame base: address = fp + offset, operand = g^offset
}
pub(crate) type Xrow = Row;
pub(crate) type Srow = Row;
pub(crate) type Jrow = Row;
pub(crate) type Brow = Row;

/// `DEREF` row: the store target is pointer-relative, so its cell index is not a
/// function of `(pc, fp)` alone.
pub(crate) struct Drow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) target: u32,
}

pub(crate) struct Trace {
    pub(crate) xor: Vec<Xrow>,
    pub(crate) mul: Vec<Xrow>,
    pub(crate) set: Vec<Srow>,
    pub(crate) deref: Vec<Drow>,
    pub(crate) jump: Vec<Jrow>,
    pub(crate) blake2s: Vec<Brow>,
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
            self.blake2s.len(),
        ]
    }
}
