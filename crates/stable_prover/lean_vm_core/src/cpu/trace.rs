//! Per-opcode trace rows, emitted during execution and assembled into a [`Trace`].
//!
//! A row carries only what the witness fill cannot recover: the step's `(pc, fp)` and the access counts read at access
//! time. Everything else is a function of those: operands and immediates come from `prog[pc]`, addresses from `fp`
//! plus those operands, and values from the final memory image, which is write-once and so still holds what each
//! accessed cell held at the time it was accessed. The rows are the interpreter's largest write stream, so what they do
//! not carry they do not pay for, twice: once writing them and once reading them back.
//!
//! An access count is held as its exponent: the column holds `g^k`, the row `k`,
//! and the fill looks the power up.

use crate::tables::{N_TABLES, Table, tables};

/// The longest row, a `KECCAK` row's.
pub(crate) const MAX_ROW: usize = 3 + crate::keccak::ROW_CELLS;

pub(crate) struct Trace {
    /// Each table's rows, [`row_len`] words a row: `pc`, `fp`, then the exponents of the table's read-count columns
    /// in column order ([`Table::count_columns`]), the bytecode's last. A `KECCAK` row's counts are its cells' in
    /// flush order (`tables::KeccakOp::cell`), zero for an output cell the row does not write.
    pub(crate) rows: [Vec<u32>; N_TABLES],
    pub(crate) bytecode_count: Vec<u32>, // per-pc execution count; the column holds g^{A[pc]}
    /// One past the highest access count, of a cell or a pc: the `g`-powers a fill looks up.
    pub(crate) counts: usize,
}

/// Words in a row of `table`.
pub(crate) fn row_len(table: Table) -> usize {
    2 + table.count_columns().len()
}

impl Trace {
    /// Rows per instruction table, in [`crate::cpu::Stats::TABLES`] order.
    pub(crate) fn row_counts(&self) -> [usize; N_TABLES] {
        tables().map(|t| self.rows[t as usize].len() / row_len(t))
    }
}
