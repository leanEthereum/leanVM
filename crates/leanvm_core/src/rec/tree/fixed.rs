//! The nodes' fixed polynomial `W_node`: each circuit's fixed columns stacked, the first level's circuit's then the node's.
//!
//! The two circuits share their heights, so their stacks have one layout, and one more variable, the kind's bit, selects the circuit.

use crate::rec::fixed::{FixedColumn, FixedColumns};
use crate::rec::table::Table;
use primitives::field::F64;

/// Where each fixed column sits in one circuit's stack: the circuit's fixed polynomial over `kappa_fix` variables.
///
/// Columns are stacked largest first, each at an offset that is a multiple of its length.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FixedLayout {
    /// Each column's variables.
    taus: Vec<usize>,
    /// Each column's offset in the stack.
    offsets: Vec<usize>,
    /// The stack's variables, `kappa_fix`.
    kappa: usize,
}

impl FixedLayout {
    /// The stack of a circuit's fixed columns at the given table heights.
    pub(crate) fn new(taus: &[usize; Table::COUNT]) -> Self {
        let taus: Vec<usize> = (0..FixedColumn::COUNT)
            .map(|c| taus[FixedColumn::at(c).table() as usize])
            .collect();
        let kappas: Vec<Option<usize>> = taus.iter().copied().map(Some).collect();
        let (offsets, placed) = crate::witness::stack_offsets(&kappas);
        Self {
            taus,
            offsets,
            kappa: crate::log2_ceil_usize(placed.max(1)),
        }
    }

    /// The stack's variables.
    pub(crate) const fn kappa(&self) -> usize {
        self.kappa
    }

    /// A column's variables.
    pub(crate) fn tau(&self, column: FixedColumn) -> usize {
        self.taus[column.index()]
    }

    /// A column's offset in the stack, as the bits of its block's index: `offset >> tau`, over `kappa_fix - tau` bits.
    pub(crate) fn block(&self, column: FixedColumn) -> usize {
        self.offsets[column.index()] >> self.tau(column)
    }

    /// The stack of a circuit's fixed columns, zero between them.
    fn stack(&self, columns: &FixedColumns) -> Vec<F64> {
        let mut out = vec![F64::ZERO; 1 << self.kappa];
        for (c, &offset) in self.offsets.iter().enumerate() {
            let column = columns.get(FixedColumn::at(c));
            out[offset..offset + column.len()].copy_from_slice(column);
        }
        out
    }

    /// The fixed polynomial of the two circuits' columns, the first level's half first.
    pub(crate) fn polynomial(&self, columns: [&FixedColumns; 2]) -> Vec<F64> {
        columns.map(|c| self.stack(c)).concat()
    }
}
