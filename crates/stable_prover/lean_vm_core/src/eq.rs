//! Sums against `eq(point, ·)`, with the table split in two so that none of the hypercube's size is built.

use crate::{load_e, load_k};
use primitives::field::{Acc8, F64, F128, F128x8};
use primitives::multilinear::eq_table;

/// `eq(point, z) = lo[z mod 2^lo_bits]·hi[z >> lo_bits]`: a table over the low variables, up to [`Self::LO_BITS`]
/// of them, and one over the rest.
pub(crate) struct SplitEq {
    pub(crate) lo: Vec<F128>,
    pub(crate) hi: Vec<F128>,
    lo_bits: usize,
}

impl SplitEq {
    /// The low table's variables: a few kilobytes, which stay in cache.
    const LO_BITS: usize = 10;

    pub(crate) fn new(point: &[F128]) -> Self {
        let lo_bits = point.len().min(Self::LO_BITS);
        Self {
            lo: eq_table(&point[..lo_bits]),
            hi: eq_table(&point[lo_bits..]),
            lo_bits,
        }
    }

    /// `eq` at `8k..8k + 8`, zero past the hypercube.
    #[inline]
    pub(crate) fn lanes(&self, k: usize) -> F128x8 {
        let (block, at) = ((8 * k) >> self.lo_bits, (8 * k) & (self.lo.len() - 1));
        match (self.hi.get(block), self.lo.get(at..at + 8)) {
            (Some(&hi), Some(lo)) => F128x8::load(lo) * F128x8::splat(hi),
            (Some(&hi), None) => F128x8::from_array(&std::array::from_fn(|p| {
                self.lo.get(at + p).map_or(F128::ZERO, |&lo| lo * hi)
            })),
            (None, _) => F128x8::ZERO,
        }
    }
}

/// `Σ_z eq(point, z)·c(z)` for every column `c`, in one pass over the rows. A column shorter than `2^point.len()` is
/// zero past its end.
///
/// A task is a run of rows of the high table, one row unless the sum is small: each row's sums are taken against the
/// low table and scaled once.
pub(crate) fn eq_sums(point: &[F128], columns: &[&[F64]]) -> Vec<F128> {
    let SplitEq { lo, hi, lo_bits } = SplitEq::new(point);
    let rows = if hi.len() * lo.len() < 8 * crate::SERIAL_BELOW {
        hi.len()
    } else {
        1
    };
    let zero = || vec![F128::ZERO; columns.len()];
    let task = |task: usize| {
        let mut sums = zero();
        for h in task * rows..hi.len().min((task + 1) * rows) {
            let z0 = h << lo_bits;
            for (sum, column) in sums.iter_mut().zip(columns) {
                let row = (0..lo.len().div_ceil(8)).fold(Acc8::ZERO, |acc, v| {
                    let (i, z) = (8 * v, z0 + 8 * v);
                    acc + load_e(&lo, i, lo.len() - i).mul_base_unreduced(load_k(
                        column,
                        z,
                        column.len().saturating_sub(z),
                    ))
                });
                *sum += hi[h] * row.sum();
            }
        }
        sums
    };
    let add = |a: Vec<F128>, b: Vec<F128>| a.iter().zip(b).map(|(&a, b)| a + b).collect();
    parallel::map_reduce(hi.len().div_ceil(rows), zero, task, add)
}
