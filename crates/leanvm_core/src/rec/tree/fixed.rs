//! The fixed polynomials: circuits' fixed columns stacked, one stack per circuit, the stacks side by side.
//!
//! - The nodes' `W_node` holds each kind's circuit, by the kind's code. The kinds' circuits share their heights, so their stacks have one layout, and the code's bits select the circuit.
//! - The leaves' `W_leaf` holds each leaf circuit, by its slot. Each has its own heights and layout, its stack zero padded to the largest.

use crate::rec::fixed::{FixedColumn, FixedColumns};
use crate::rec::table::PerRecTable;
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
    pub(crate) fn new(taus: &PerRecTable<usize>) -> Self {
        let taus: Vec<usize> = (0..FixedColumn::COUNT)
            .map(|c| taus[FixedColumn::at(c).table()])
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

    /// Write a circuit's fixed columns into its stack `out`, zero until then: zero between and after them.
    pub(crate) fn write(&self, columns: &FixedColumns, out: &mut [F64]) {
        assert!(out.len() >= 1 << self.kappa, "the stack holds the layout");
        for (c, &offset) in self.offsets.iter().enumerate() {
            let column = columns.get(FixedColumn::at(c));
            out[offset..offset + column.len()].copy_from_slice(column);
        }
    }
}

/// Circuits' stacks of `2^kappa` words each side by side, zero stacks after them up to `2^bits`: the polynomial of `kappa + bits` variables whose top `bits` select a stack.
pub(crate) fn side_by_side<'c>(
    stacks: impl IntoIterator<Item = (&'c FixedLayout, &'c FixedColumns)>,
    kappa: usize,
    bits: usize,
) -> Vec<F64> {
    let mut out = vec![F64::ZERO; 1 << (kappa + bits)];
    let mut slots = out.chunks_exact_mut(1 << kappa);
    for (layout, columns) in stacks {
        layout.write(columns, slots.next().expect("the selector's bits name every stack"));
    }
    out
}
