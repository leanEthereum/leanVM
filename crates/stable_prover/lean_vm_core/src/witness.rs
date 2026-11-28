//! `K`-valued columns stacked into one committed witness (§sec:stacking): columns laid end to end, largest first at
//! aligned offsets ([`verifier::stack_offsets`]), into one multilinear `q` over `F64`. An evaluation claim on a column at
//! `ζ ∈ E` is a claim on the stack at `ζ` and the column's place.

use ::pcs::{StackClaim, SumPart};
use primitives::field::{F64, F128, dot_base};

/// Where a column sits in the stacked witness. A [`Placement::VIRTUAL`] column has no placement of its own: either its
/// words are committed inside another column, and its evaluation claims settle there (the KECCAK columns `q_keccak`
/// carries), or they are not committed at all and something else proves them (the KECCAK output lanes).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Placement {
    pub n_vars: usize,
    pub offset: usize,
}

impl Placement {
    pub const VIRTUAL: Placement = Placement {
        n_vars: usize::MAX,
        offset: 0,
    };

    pub fn is_virtual(&self) -> bool {
        self.n_vars == usize::MAX
    }

    /// The `2^n_vars` rows from `start`, a multiple of `2^n_vars`, as a column of their own.
    pub fn rows(&self, start: usize, n_vars: usize) -> Placement {
        assert!(start.is_multiple_of(1 << n_vars) && start + (1 << n_vars) <= 1 << self.n_vars);
        Placement {
            n_vars,
            offset: self.offset + start,
        }
    }

    /// The claim on the column at row `point`, on the stack.
    pub fn claim(&self, point: Vec<F128>) -> StackClaim {
        assert!(
            !self.is_virtual() && point.len() == self.n_vars,
            "a committed column's row point"
        );
        StackClaim::Point {
            offset: self.offset,
            low_point: point,
        }
    }

    /// One part of a [`StackClaim::Sum`] at row `point`, scaled by `scale`.
    pub fn sum_part(&self, point: Vec<F128>, scale: F128) -> SumPart {
        let StackClaim::Point { offset, low_point } = self.claim(point) else {
            unreachable!("a column's claim is a point")
        };
        SumPart {
            offset,
            low_point,
            scale,
        }
    }

    /// The column's rows in `q`, the stack.
    pub fn view<'a>(&self, q: &'a [F64]) -> &'a [F64] {
        assert!(!self.is_virtual(), "a virtual column is not in the stack");
        &q[self.offset..][..1 << self.n_vars]
    }
}

/// Each column's multilinear extension at `point`, a column shorter than `2^point.len()` zero past its end.
pub fn mle_eval_cols(cols: &[&[F64]], point: &[F128]) -> Vec<F128> {
    let eq = primitives::multilinear::eq_table(point);
    parallel::map_collect(cols.len(), |c| dot_base(&eq[..cols[c].len()], cols[c]))
}

/// The committed stack's shape. `mu` is the log size everything public is derived from (the claims' selector coords,
/// the PCS level ladder), while `n_lanes` counts the `2^(mu - LOG_BATCH)`-word lanes that carry data: the PCS commits
/// `committed_len()` words and never encodes or hashes the zero tail past them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StackShape {
    pub mu: usize,
    pub n_lanes: usize,
}

impl StackShape {
    /// Words committed: the placed columns rounded up to a whole lane.
    pub fn committed_len(&self) -> usize {
        self.n_lanes << (self.mu - crate::pcs::LOG_BATCH)
    }
}

/// Per-column placements and the stack's [`StackShape`] from the columns' log-sizes, `None` for a virtual column, by
/// [`verifier::stack_offsets`] over the committed columns in column order.
pub fn placements_of(kappas: &[Option<usize>]) -> (Vec<Placement>, StackShape) {
    let committed: Vec<usize> = kappas.iter().flatten().copied().collect();
    let (offsets, placed_log) = verifier::stack_offsets(&committed);
    let mut offsets = offsets.into_iter();
    let placements = kappas
        .iter()
        .map(|k| match *k {
            Some(n_vars) => Placement {
                n_vars,
                offset: offsets.next().unwrap() as usize,
            },
            None => Placement::VIRTUAL,
        })
        .collect();
    let mu = placed_log.max(crate::pcs::MIN_STACKED_LOG);
    // The columns tile from 0, so the padding is the tail: the lanes past the placed columns are never committed.
    let placed: usize = committed.iter().map(|k| 1 << k).sum();
    let n_lanes = placed.div_ceil(1 << (mu - crate::pcs::LOG_BATCH)).max(1);
    (placements, StackShape { mu, n_lanes })
}

/// Carve the stack `q` into one window per committed column, in column order, so that each column is written in its
/// final place. A virtual column gets an empty window: its values need storage of their own.
pub fn split_stack<'a>(q: &'a mut [F64], placements: &[Placement]) -> Vec<&'a mut [F64]> {
    let mut order: Vec<usize> = (0..placements.len()).filter(|&i| !placements[i].is_virtual()).collect();
    order.sort_unstable_by_key(|&i| placements[i].offset);
    let mut windows: Vec<&mut [F64]> = Vec::with_capacity(placements.len());
    windows.resize_with(placements.len(), || &mut []);
    let (mut rest, mut placed) = (q, 0);
    for i in order {
        assert_eq!(placements[i].offset, placed, "the stacked columns tile from 0");
        let len = 1 << placements[i].n_vars;
        let (window, tail) = std::mem::take(&mut rest).split_at_mut(len);
        windows[i] = window;
        (rest, placed) = (tail, placed + len);
    }
    windows
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The shape covers the placed columns with as few lanes as possible: the prover commits `committed_len()` words,
    /// so anything short of the columns would leave a claim outside the commitment, and any extra whole lane is wasted
    /// work. Each column's view reads what `split_stack` hands out.
    #[test]
    fn placements_cover_the_columns_in_the_fewest_lanes() {
        let lanes = 1usize << crate::pcs::LOG_BATCH;
        // A power-of-two total, one word over one, one just under, virtual columns in the middle, and a stack far
        // below the MIN_STACKED_LOG floor.
        let cases: [Vec<Option<usize>>; 5] = [
            vec![Some(20), Some(20)],
            vec![Some(20), Some(20), Some(0)],
            vec![Some(20), Some(19), Some(18), Some(17)],
            vec![Some(15), None, Some(19), None, Some(21)],
            vec![Some(3), Some(2)],
        ];
        for kappas in cases {
            let placed: usize = kappas.iter().flatten().map(|k| 1usize << k).sum();
            let (placements, shape) = placements_of(&kappas);
            let lane_block = 1usize << (shape.mu - crate::pcs::LOG_BATCH);
            assert_eq!(
                shape.mu,
                crate::log2_ceil_usize(placed).max(crate::pcs::MIN_STACKED_LOG)
            );
            assert!((1..=lanes).contains(&shape.n_lanes), "lane count out of range");
            assert!(shape.committed_len() >= placed, "columns must fit the commitment");
            assert!(
                shape.committed_len() - placed < lane_block,
                "a whole lane of the commitment carries no data"
            );
            let mut q = vec![F64::ZERO; shape.committed_len()];
            for (c, window) in split_stack(&mut q, &placements).into_iter().enumerate() {
                assert_eq!(window.len(), kappas[c].map_or(0, |k| 1 << k));
                window.fill(F64(c as u64 + 1));
            }
            for (c, p) in placements.iter().enumerate().filter(|(_, p)| !p.is_virtual()) {
                assert!(p.offset.is_multiple_of(1 << p.n_vars), "column {c} is aligned");
                assert!(p.view(&q).iter().all(|&w| w == F64(c as u64 + 1)), "column {c}");
            }
        }
    }
}
