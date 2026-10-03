//! The recursion circuits' fixed columns as dense polynomials: each circuit's bus columns that the circuit fixes
//! (`machine::fixed_columns`), stacked largest first at aligned offsets. The lift's stack is a polynomial of its
//! own; the two node circuits share their heights, so their stacks are one polynomial under one more variable, the
//! node's kind bit (whether its children are nodes).

use crate::rec::circuit::N_TABLES;
use crate::rec::machine::{self, Fixed};
use primitives::field::F64;

/// Where each fixed column sits in one circuit's stack, for circuits of heights `taus`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixedLayout {
    pub columns: Vec<Fixed>,
    pub offsets: Vec<usize>,
    /// `log2` of one circuit's stack.
    pub omega: usize,
}

impl FixedLayout {
    pub fn new(taus: &[usize; N_TABLES]) -> Self {
        let columns = machine::fixed_columns();
        let kappas: Vec<Option<usize>> = columns.iter().map(|c| Some(taus[c.table() as usize])).collect();
        let (offsets, placed) = crate::witness::stack_offsets(&kappas);
        Self {
            columns,
            offsets,
            omega: crate::log2_ceil_usize(placed.max(1)),
        }
    }

    /// One circuit's stack of its fixed columns' `values`, zero between them.
    pub fn stack(&self, values: &[Vec<F64>]) -> Vec<F64> {
        let mut out = vec![F64::ZERO; 1 << self.omega];
        for (&offset, column) in self.offsets.iter().zip(values) {
            out[offset..offset + column.len()].copy_from_slice(column);
        }
        out
    }
}
