//! Fill blocks: extra rows so every table's height is a power of two.
//!
//! A table is proven over a power-of-two number of rows, so a table whose execution
//! needs fewer has to make up the difference. The alternative to this module is padding
//! rows, which are not real rows: they put default tuples on the bus that nothing
//! matches, so the verifier has to be told each table's real row count and divide those
//! tuples back out. That correction was the most delicate part of the bus argument, and
//! it existed only for the instruction tables; unread memory cells and unexecuted
//! program entries already need nothing, their seed and finalize tuples cancelling.
//!
//! So run the difference off instead. Every program carries, past `main`'s halt, one
//! block per table per size in `lean_vm::cpu::filler::SIZES`: that many dummy
//! instructions of the table's opcode, then a `JUMP` back to the block's own first
//! instruction. Each block is therefore a cycle, and no program code enters one: on the
//! bus its state tuples cancel against each other rather than against the program's
//! chain, so it can be traversed any number of times, and the interpreter walks the
//! blocks itself once the program has halted
//! (`lean_vm::cpu::Program::execute`).
//!
//! Nothing in a block counts, tests, or allocates: a traversal of the size-`s` block
//! costs exactly `s + 1` rows, `s` of its table and one `JUMP`. That is where the sizes
//! earn their keep: powers of two make any fill reachable exactly, while the bulk rides
//! the largest block at one jump per 128 rows. A table already on a power of two is
//! never entered.

/// What a table's dummy instruction is: the cheapest instruction of that opcode that can
/// be executed any number of times in one frame, given write-once memory. All but
/// `Blake2s` and `Sha3` name a single scratch cell as every operand, so the value they write there is
/// the value already there (`FnLower::lower_filler_blocks` fixes the frame offsets).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FillerOp {
    /// `XOR s, s -> s`: pins the scratch cell to `m[s] + m[s] = 0`.
    Xor,
    /// `MUL s, s -> s`: pins it to `m[s]^2`, so to `0` given the above.
    Mul,
    /// `SET s = 0`.
    Set,
    /// `DEREF` through the frame's pointer cell, which the interpreter sets to `g^0`, so
    /// the address is memory cell `0` and the value read is the public input's.
    Deref,
    /// `JUMP` on a cell nothing ever writes: a zero condition falls through, so the row
    /// fills the table without closing the block's cycle.
    Jump,
    /// One compression of message and chaining-value cells nothing ever writes, its
    /// digest placed clear of them, so every traversal compresses the same input.
    Blake2s,
    /// One sponge step over input cells nothing ever writes, its output placed clear
    /// of them, so every traversal permutes the same state.
    Sha3,
}

/// The tables, in `lean_vm::cpu::Stats::TABLES` order, which is how the solver indexes
/// them.
pub const TABLES: [(u8, FillerOp); 7] = [
    (0, FillerOp::Xor),
    (1, FillerOp::Mul),
    (2, FillerOp::Set),
    (3, FillerOp::Deref),
    (4, FillerOp::Jump),
    (5, FillerOp::Blake2s),
    (6, FillerOp::Sha3),
];
