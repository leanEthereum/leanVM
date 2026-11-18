//! `K`-valued columns stacked into one committed witness (§sec:stacking): columns laid
//! end to end, largest first at aligned offsets, into one multilinear `q` over
//! `F64`. An evaluation claim on column `i` at `ζ ∈ E` becomes the claim
//! `q̂(ζ, sel_i) = c` on the stack, where `sel_i` is the high-bit selector of
//! the column's offset.

use primitives::field::F64;

/// Where a column sits in the stacked witness. A [`Placement::VIRTUAL`] column has no
/// placement of its own: either its words are committed inside another column, and its
/// evaluation claims settle there (the KECCAK columns `q_keccak` carries), or they are not
/// committed at all and something else proves them (the KECCAK output lanes).
#[derive(Clone, Copy, Debug)]
pub struct Placement {
    pub n_vars: usize,
    pub offset: usize,
}

impl Placement {
    pub const VIRTUAL: Placement = Placement {
        n_vars: usize::MAX,
        offset: 0,
    };

    pub(crate) fn is_virtual(&self) -> bool {
        self.n_vars == usize::MAX
    }
}

/// The committed stack's shape. `mu` is the log size everything public is derived
/// from (the claims' selector coords, the PCS level ladder), while `n_lanes` counts
/// the `2^(mu - LOG_BATCH)`-word lane blocks that actually carry data: the PCS
/// commits `committed_len()` words and never encodes or hashes the zero tail past
/// them. The level-0 openings leave out the zero words every opened row starts
/// with, the absent lanes among them.
#[derive(Clone, Copy, Debug)]
pub struct StackShape {
    pub mu: usize,
    pub n_lanes: usize,
}

impl StackShape {
    /// Words actually committed: the placed columns rounded up to a whole lane.
    pub fn committed_len(&self) -> usize {
        self.n_lanes << (self.mu - crate::pcs::LOG_BATCH)
    }
}

/// Per-column placements (offset + n_vars) and the stack's [`StackShape`] from the
/// columns' log-sizes alone, largest-first at aligned offsets. A `None` kappa marks
/// a virtual (uncommitted) column. Depends only on lengths, so the verifier can
/// reconstruct it.
pub(crate) fn placements_of(kappas: &[Option<usize>]) -> (Vec<Placement>, StackShape) {
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
    // Floor at the PCS minimum (WHIR's level ladder needs room); tiny
    // witnesses zero-pad up. Both sides derive this identically from the kappas.
    let mu = placed_log.max(crate::pcs::MIN_STACKED_LOG);
    let placed: usize = committed.iter().map(|k| 1 << k).sum();
    // The columns tile from 0, so the padding is the tail: round it up to a whole
    // lane and the lanes past that are never committed at all.
    let n_lanes = placed.div_ceil(1 << (mu - crate::pcs::LOG_BATCH)).max(1);
    (placements, StackShape { mu, n_lanes })
}

/// A run of a column's rows the stack holds as a block: its first row, its log length and where it sits.
#[derive(Clone, Copy, Debug)]
pub struct Run {
    pub start: usize,
    pub n_vars: usize,
    pub offset: usize,
}

/// The committed stack of the columns of these log sizes (`None` virtual), each table column of `rows` rows stacked as
/// its runs (`verifier::layout::dyadic_pieces`): per column its runs, and the stack's shape. `table` names a column's
/// table, if it has one. Both sides derive this from the announced sizes alone.
pub(crate) fn runs_of(
    kappas: &[Option<usize>],
    table: impl Fn(usize) -> Option<usize>,
    rows: &[usize],
) -> (Vec<Vec<Run>>, StackShape) {
    let pieces: Vec<(usize, u64, usize)> = kappas
        .iter()
        .enumerate()
        .filter_map(|(column, k)| k.map(|kappa| (column, kappa)))
        .flat_map(|(column, kappa)| {
            let runs = match table(column) {
                Some(t) => verifier::layout::dyadic_pieces(rows[t] as u64, kappa),
                None => vec![(0, kappa)],
            };
            runs.into_iter().map(move |(start, log)| (column, start, log))
        })
        .collect();
    let sizes: Vec<usize> = pieces.iter().map(|p| p.2).collect();
    let (offsets, placed_log) = verifier::stack_offsets(&sizes);
    let mut runs = vec![Vec::new(); kappas.len()];
    for ((column, start, n_vars), offset) in pieces.into_iter().zip(offsets) {
        runs[column].push(Run {
            start: start as usize,
            n_vars,
            offset: offset as usize,
        });
    }
    let mu = placed_log.max(crate::pcs::MIN_STACKED_LOG);
    let placed: usize = sizes.iter().map(|k| 1 << k).sum();
    let n_lanes = placed.div_ceil(1 << (mu - crate::pcs::LOG_BATCH)).max(1);
    (runs, StackShape { mu, n_lanes })
}

/// The stack of `runs`, each copied from its column's window of `arena` at `placements`, the tail zero.
pub(crate) fn stack_runs(arena: &[F64], placements: &[Placement], runs: &[Vec<Run>], shape: StackShape) -> Vec<F64> {
    let mut q = parallel::filled(shape.committed_len(), F64::ZERO);
    for (column, column_runs) in runs.iter().enumerate() {
        for run in column_runs {
            let len = 1 << run.n_vars;
            q[run.offset..][..len].copy_from_slice(&arena[placements[column].offset + run.start..][..len]);
        }
    }
    q
}

/// Carve the stack into one mutable window per committed column, in column order, so that each column is
/// written in its final place. A virtual column gets an empty window: it is not in the stack, so its values need
/// storage of their own.
pub(crate) fn split_stack<'a>(q: &'a mut [F64], placements: &[Placement]) -> Vec<&'a mut [F64]> {
    let mut order: Vec<usize> = (0..placements.len()).filter(|&i| !placements[i].is_virtual()).collect();
    order.sort_unstable_by_key(|&i| placements[i].offset);

    let mut windows: Vec<&mut [F64]> = Vec::with_capacity(placements.len());
    windows.resize_with(placements.len(), || &mut []);
    let mut rest = q;
    let mut placed = 0usize;
    for &i in &order {
        assert_eq!(
            placements[i].offset, placed,
            "the stacked columns must tile from 0 with no gap"
        );
        let (window, tail) = rest.split_at_mut(1 << placements[i].n_vars);
        windows[i] = window;
        rest = tail;
        placed += 1 << placements[i].n_vars;
    }
    windows
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The shape has to cover the placed columns with as few lanes as possible: the
    /// prover commits `committed_len()` words, so anything short of `placed` would
    /// leave a claim outside the commitment, and any extra whole lane is wasted
    /// work. `mu` stays the announced `2^mu` size both sides derive their layout from.
    #[test]
    fn placements_cover_the_columns_in_the_fewest_lanes() {
        let lanes = 1usize << crate::pcs::LOG_BATCH;
        // A power-of-two total, one word over one, one just under, a virtual column
        // in the middle, and a stack far below the MIN_STACKED_LOG floor.
        let cases: [Vec<Option<usize>>; 5] = [
            vec![Some(20), Some(20)],
            vec![Some(20), Some(20), Some(0)],
            vec![Some(20), Some(19), Some(18), Some(17)],
            vec![Some(21), None, Some(19), None, Some(15)],
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
            assert!(shape.committed_len() <= 1usize << shape.mu);
            // And every column really does live inside those lanes.
            for p in placements.iter().filter(|p| !p.is_virtual()) {
                assert!(p.offset + (1usize << p.n_vars) <= shape.committed_len());
            }
        }
    }
}
