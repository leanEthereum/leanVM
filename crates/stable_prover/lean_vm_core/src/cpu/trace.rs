//! Per-opcode trace rows, emitted during execution and assembled into a [`Trace`].
//!
//! A row carries only what the witness fill cannot recover: the step's `(pc, fp)` and its cycle, `step`. Everything
//! else is a function of those: operands and immediates come from `prog[pc]`, addresses from `fp` plus those operands,
//! and values from the final memory image, which is write-once and so still holds what each accessed cell held at the
//! time it was accessed. The one exception is a `DEREF`'s store cell, which depends on the pointer the run read.

/// A row of `XOR`, `MUL`, `SET`, `JUMP` or `KECCAK`: an `XOR`/`MUL` row's three cells are `fp + a`, `fp + b`, `fp + c`;
/// a `KECCAK` row's cells are read back from the instruction (`tables::KeccakOp::cell`), the input lanes from the final
/// memory image and the output lanes as their permutation.
pub(crate) struct Row {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) step: u32,
}

/// `DEREF` row: `store` is the cell the pointer names, `p·g^{o2}`'s index.
pub(crate) struct Drow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) step: u32,
    pub(crate) store: u32,
}

pub(crate) struct Trace {
    pub(crate) xor: Vec<Row>,
    pub(crate) mul: Vec<Row>,
    pub(crate) set: Vec<Row>,
    pub(crate) deref: Vec<Drow>,
    pub(crate) jump: Vec<Row>,
    pub(crate) keccak: Vec<Row>,
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
