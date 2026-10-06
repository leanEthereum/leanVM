//! The recursion machine's circuit: a fixed list of rows, one table per operation, wired by copy cycles.
//!
//! A wire holds a `K` word, an `E` element (three limbs) or a digest (four words).
//! Every row names one wire per slot, and every slot carries its wire on the bus.
//! The slots naming one wire form a cycle on the bus, which balances only if they all carry one value.
//! A wire in one slot is a cycle of one: it constrains nothing, which is what a value the prover sends is.
//!
//! The rows depend on the shapes of what is verified, never on values.
//! So the verifier rebuilds the same circuit with no proof, its values computed from zeros.

mod builder;
mod compression;

pub use builder::Builder;
pub(crate) use compression::digest_limbs;
pub use compression::{Compression, PARAM_IV, chain, zero_prefix};

use super::table::{PerRecTable, Table};

/// A wire's value as four `K` words: a `K` wire uses the first, an `E` wire the first three.
pub type Limbs = [u64; 4];

/// What a wire holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum WireKind {
    /// One `K` word.
    K,
    /// One `E` element, three `K` limbs.
    E,
    /// A digest, four `K` words.
    D,
}

/// A `K` wire.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Kw(pub(crate) u32);

/// An `E` wire.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Ew(pub(crate) u32);

/// A digest wire.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Dw(pub(crate) u32);

/// Where a public row's value comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PubSource {
    /// A constant of the circuit.
    Const(Limbs),
    /// Word `i` of the statement.
    Statement(usize),
}

/// Every table's rows, row-major, one number per slot: a wire, or the class of wires it is held equal to.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct TableSlots(PerRecTable<Vec<u32>>);

impl TableSlots {
    /// Append a row to a table.
    fn push(&mut self, table: Table, slots: &[u32]) {
        debug_assert_eq!(slots.len(), table.n_slots());
        self.0[table].extend_from_slice(slots);
    }

    /// Put a one-slot table's rows in the given order of their old indices.
    fn reorder(&mut self, table: Table, order: &[usize]) {
        debug_assert_eq!(table.n_slots(), 1);
        let rows = &self.0[table];
        self.0[table] = order.iter().map(|&i| rows[i]).collect();
    }

    /// A table's slots, row-major.
    pub(crate) fn of(&self, table: Table) -> &[u32] {
        &self.0[table]
    }

    /// How many rows a table has.
    pub(crate) fn len(&self, table: Table) -> usize {
        self.of(table).len() / table.n_slots()
    }

    /// Every table's slots, each number replaced through `f`.
    pub(crate) fn map(&self, mut f: impl FnMut(u32) -> u32) -> Self {
        Self(PerRecTable::from_fn(|t| self.0[t].iter().map(|&w| f(w)).collect()))
    }
}

/// The fixed part of a circuit: its rows, and the wire class each slot names.
///
/// The statement's public rows come first, in statement order, then the constants'.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Circuit {
    /// Each slot's wire class.
    pub(crate) classes: TableSlots,
    /// Per public row, where its value comes from.
    pub(crate) pubs: Vec<PubSource>,
    /// How many words the statement has.
    pub(crate) statement_len: usize,
    /// Each table's least height, as a base-two logarithm.
    pub(crate) floor: PerRecTable<usize>,
}

impl Circuit {
    /// Each table's number of rows.
    pub fn row_counts(&self) -> PerRecTable<usize> {
        PerRecTable::from_fn(|t| self.classes.len(t))
    }

    /// Each table's base-two logarithm of rows: the least power of two holding its rows, and at least its floor.
    pub fn heights(&self) -> PerRecTable<usize> {
        let counts = self.row_counts();
        PerRecTable::from_fn(|t: Table| t.height_log(counts[t]).max(self.floor[t]))
    }

    /// How many wire classes the slots name.
    pub(crate) fn n_classes(&self) -> usize {
        (Table::ALL.iter())
            .flat_map(|&t| self.classes.of(t))
            .max()
            .map_or(0, |&c| c as usize + 1)
    }
}

/// What the prover adds to a circuit: every wire's value and every hash row's inputs.
#[derive(Clone, Debug)]
pub struct Assignment {
    /// Each slot's own wire, whose value the slot carries.
    pub(crate) wires: TableSlots,
    /// Each wire's value.
    pub(crate) values: Vec<Limbs>,
    /// Each hash row's compression.
    pub(crate) hash: Vec<Compression>,
    /// The statement's words.
    pub(crate) statement: Vec<Limbs>,
}

impl Assignment {
    /// The statement's words.
    pub fn statement(&self) -> &[Limbs] {
        &self.statement
    }

    /// The value slot `s` of a table's row `z` carries.
    pub(crate) fn value(&self, table: Table, z: usize, s: usize) -> Limbs {
        self.values[self.wires.of(table)[z * table.n_slots() + s] as usize]
    }
}

/// A finished circuit, the values of the run that built it, and the checks that failed on them.
#[derive(Clone, Debug)]
pub struct Finished {
    /// The circuit.
    pub circuit: Circuit,
    /// The run's values.
    pub assignment: Assignment,
    /// The checks that failed, each under its scope's name, then a count of those past the first few.
    pub failures: Vec<String>,
}
