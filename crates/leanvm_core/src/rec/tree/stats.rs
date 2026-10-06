//! What a tree's circuits cost.

use super::{Kind, Tree};
use crate::rec::table::Table;

/// What one of a tree's circuits costs.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct CircuitStats {
    /// Each table of the recursion machine, in the machine's order.
    pub tables: Vec<TableStats>,
    /// The words a proof of the circuit commits.
    pub committed: usize,
}

/// One table of a circuit: its rows, and the height they are padded to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct TableStats {
    /// The table's name.
    pub name: &'static str,
    /// The rows the circuit puts in the table.
    pub rows: usize,
    /// The base-two logarithm of the table's height.
    ///
    /// The height is a power of two, at least the rows.
    pub height_log: usize,
}

impl Tree<'_> {
    /// What the circuit of one kind of node costs.
    #[must_use]
    pub fn stats(&self, kind: Kind) -> CircuitStats {
        // The circuit's rows per table, and the padded heights it is proven at.
        let circuit = self.circuit(kind);
        let (rows, heights) = (circuit.row_counts(), circuit.heights());

        // One entry per table of the recursion machine, in its order.
        let tables = (Table::ALL.iter())
            .map(|&table| TableStats {
                name: table.name(),
                rows: rows[table],
                height_log: heights[table],
            })
            .collect();

        // Invariant: building the tree refused any circuit that fits no commitment.
        let committed = circuit.committed_words().expect("a tree's circuits fit one commitment");
        CircuitStats { tables, committed }
    }
}
