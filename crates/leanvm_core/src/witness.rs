//! `K`-valued columns stacked into one committed witness (§sec:stacking): columns laid
//! end to end, largest first at aligned offsets, into one multilinear `q` over
//! `F64`. An evaluation claim on column `i` at `ζ ∈ E` becomes the claim
//! `q̂(ζ, sel_i) = c` on the stack, where `sel_i` is the high-bit selector of
//! the column's offset. A column committed in pieces places each piece the same way.

use primitives::field::{F64, F192};
use primitives::multilinear::eq_eval;

/// Where a column, or one piece of it, sits in the stacked witness.
#[derive(Clone, Copy, Debug)]
pub struct Placement {
    pub n_vars: usize,
    pub offset: usize,
}

/// A column's pieces in the stack (§sec:stacking): where each sits, largest first, the cells they hold, and what every
/// cell past them holds.
///
/// A column committed whole is one piece holding every cell.
/// A VIRTUAL column has no piece: its words are either committed inside another column, whose claims settle there
/// (the KECCAK columns `q_keccak` carries), or not committed at all, something else proving them (the KECCAK output
/// lanes).
#[derive(Clone, Debug)]
pub struct Pieces {
    /// Where each piece sits, largest first.
    pub placements: Vec<Placement>,
    /// The cells the pieces hold.
    pub cells: usize,
    /// What every cell past them holds.
    pub pad: F64,
}

impl Pieces {
    /// The column's one placement, if it is committed whole.
    pub fn whole(&self) -> Option<Placement> {
        match self.placements.as_slice() {
            [placement] if self.cells == 1 << placement.n_vars => Some(*placement),
            _ => None,
        }
    }
}

/// The coefficient each piece carries in a claim at `point` on a column committed in pieces of `2^k_i` cells, largest first.
///
/// Piece `i` holds the cells from `o_i = sum_{j<i} 2^k_j` (§sec:stacking), so its scalar is
///
/// ```text
/// e_i(r) = eq(r_{>=k_i}, bits(o_i >> k_i))
/// ```
pub fn piece_coefficients(point: &[F192], pieces: &[usize]) -> Vec<F192> {
    let mut start = 0usize;
    pieces
        .iter()
        .map(|&k| {
            let above: Vec<F192> = (k..point.len())
                .map(|bit| F192::new(((start >> bit) & 1) as u64, 0, 0))
                .collect();
            start += 1 << k;
            eq_eval(&above, &point[k..])
        })
        .collect()
}

/// The committed stack's shape. `mu` is the log size everything public is derived
/// from (the claims' selector coords, the PCS level ladder), while `n_lanes` counts
/// the `2^(mu - LOG_BATCH)`-word lane blocks that actually carry data: the PCS
/// commits `committed_len()` words and never encodes or hashes the zero tail past
/// them. The verifier's view of the commitment is the same `2^mu`-word witness
/// either way; it derives `n_lanes` from the announced layout only to read the
/// pruned level-0 rows, which leave the zero lanes out.
#[derive(Clone, Copy, Debug)]
pub struct StackShape {
    pub mu: usize,
    pub n_lanes: usize,
}

impl StackShape {
    /// Words actually committed: the placed columns rounded up to a whole lane.
    pub fn committed_len(&self) -> usize {
        // Both fields are `pub`, and in release the shift below would mask an
        // underflowed amount into a plausible wrong length rather than panic.
        assert!(self.mu >= crate::pcs::LOG_BATCH, "a stack is at least one lane block");
        self.n_lanes << (self.mu - crate::pcs::LOG_BATCH)
    }
}

/// Lay `2^kappa`-sized items end to end, largest first at aligned offsets and ties
/// broken by index, returning the per-item offset and `Σ 2^kappa`. A `None`
/// kappa takes no space and its offset is meaningless. Depends only on the sizes, so
/// the verifier reconstructs the same tiling.
pub(crate) fn stack_offsets(kappas: &[Option<usize>]) -> (Vec<usize>, usize) {
    let n = kappas.len();
    let mut order: Vec<usize> = (0..n).filter(|&i| kappas[i].is_some()).collect();
    order.sort_by(|&a, &b| kappas[b].unwrap().cmp(&kappas[a].unwrap()).then(a.cmp(&b)));

    let mut offsets = vec![0usize; n];
    let mut off = 0usize;
    for &i in &order {
        let kappa = kappas[i].unwrap();
        assert!(
            kappa < usize::BITS as usize,
            "kappa {kappa} is a log-size, not a length"
        );
        offsets[i] = off;
        off += 1 << kappa;
    }
    (offsets, off)
}

/// Per-column piece placements (offset + n_vars) and the stack's shape from the pieces' log-sizes alone.
///
/// Largest-first at aligned offsets, ties broken by column then piece.
/// A column with no piece is virtual (uncommitted).
/// Depends only on lengths, so the verifier can reconstruct it.
pub fn placements_of(kappas: &[Vec<usize>]) -> (Vec<Vec<Placement>>, StackShape) {
    let blocks: Vec<Option<usize>> = kappas.iter().flatten().copied().map(Some).collect();
    let (offsets, placed) = stack_offsets(&blocks);
    let mut offsets = offsets.into_iter();
    let placements = kappas
        .iter()
        .map(|pieces| {
            pieces
                .iter()
                .map(|&n_vars| Placement {
                    n_vars,
                    offset: offsets.next().expect("an offset per piece"),
                })
                .collect()
        })
        .collect();
    // Floor at the PCS minimum (WHIR's level ladder needs room); tiny
    // witnesses zero-pad up. Both sides derive this identically from the kappas.
    let mu = crate::log2_ceil_usize(placed.max(1)).max(crate::pcs::MIN_MU);
    // The columns tile from 0, so the padding is the tail: round it up to a whole
    // lane and the lanes past that are never committed at all.
    let n_lanes = placed.div_ceil(1 << (mu - crate::pcs::LOG_BATCH)).max(1);
    (placements, StackShape { mu, n_lanes })
}

/// Chunk width for the bulk writes below: big enough to amortize the dispatch,
/// small enough to spread one column across cores.
const FILL_CHUNK: usize = 1 << 16;

/// The uninitialized stacked witness: [`StackShape::committed_len`] slots, the
/// placed columns rounded up to a whole lane rather than all the way to `2^mu`.
///
/// # Safety
/// Every slot must be written before it is read. [`split_stack`] hands out one
/// window per committed column and zeroes the pad tail, which together cover the
/// whole allocation, so the obligation reduces to each column's fill writing its
/// own window.
pub unsafe fn alloc_stack(shape: StackShape) -> Vec<F64> {
    // SAFETY: forwarded to the caller by the contract above.
    unsafe { primitives::uninit_vec::<F64>(shape.committed_len()) }
}

/// Carve the stack into one mutable window per committed piece, by column then piece,
/// and zero the pad tail past the last one. A virtual column gets no window: it is not in
/// the stack, so its values need storage of their own.
///
/// Writing each column into its final place is what lets the whole witness be
/// written once. Copying columns in afterwards would move the entire stack a
/// second time (a gigabyte at scale) for nothing, and allocating the stack zeroed
/// would memset all `2^m` slots only for the columns to overwrite them.
///
/// Safe despite [`alloc_stack`]'s uninitialized allocation: [`placements_of`]
/// tiles the columns from offset 0, checked here, so consecutive `split_at_mut`
/// hands out disjoint windows covering `[0, placed)` and this zeroes the rest.
pub fn split_stack<'a>(q: &'a mut [F64], columns: &[Pieces]) -> Vec<Vec<&'a mut [F64]>> {
    let placements: Vec<&[Placement]> = columns.iter().map(|column| column.placements.as_slice()).collect();
    let mut order: Vec<(usize, usize)> = placements
        .iter()
        .enumerate()
        .flat_map(|(column, pieces)| (0..pieces.len()).map(move |piece| (column, piece)))
        .collect();
    order.sort_unstable_by_key(|&(column, piece)| placements[column][piece].offset);

    let mut windows: Vec<Vec<&mut [F64]>> = placements
        .iter()
        .map(|pieces| pieces.iter().map(|_| <&mut [F64]>::default()).collect())
        .collect();
    let mut rest = q;
    let mut placed = 0usize;
    for (column, piece) in order {
        let placement = placements[column][piece];
        assert_eq!(
            placement.offset, placed,
            "the stacked columns must tile from 0 with no gap"
        );
        let (window, tail) = rest.split_at_mut(1 << placement.n_vars);
        windows[column][piece] = window;
        rest = tail;
        placed += 1 << placement.n_vars;
    }
    parallel::chunks_mut(rest, FILL_CHUNK, |_, pad| pad.fill(F64::ZERO));
    windows
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The shape has to cover the placed columns with as few lanes as possible: the
    /// prover commits `committed_len()` words, so anything short of `placed` would
    /// leave a claim outside the commitment, and any extra whole lane is work the
    /// change exists to avoid. `mu` stays the announced `2^mu` size both sides
    /// derive their layout from.
    #[test]
    fn placements_cover_the_columns_in_the_fewest_lanes() {
        let lanes = 1usize << crate::pcs::LOG_BATCH;
        // A power-of-two total, one word over one, one just under, a virtual column
        // in the middle, and a stack far below the MIN_MU floor.
        let cases: [Vec<Vec<usize>>; 6] = [
            vec![vec![20], vec![20]],
            vec![vec![20], vec![20], vec![0]],
            vec![vec![20], vec![19], vec![18], vec![17]],
            vec![vec![21], vec![], vec![19], vec![], vec![15]],
            vec![vec![3], vec![2]],
            vec![vec![20, 18, 11], vec![19], vec![]],
        ];
        for kappas in cases {
            let placed: usize = kappas.iter().flatten().map(|k| 1usize << k).sum();
            let (placements, shape) = placements_of(&kappas);
            let lane_block = 1usize << (shape.mu - crate::pcs::LOG_BATCH);

            assert_eq!(shape.mu, crate::log2_ceil_usize(placed).max(crate::pcs::MIN_MU));
            assert!((1..=lanes).contains(&shape.n_lanes), "lane count out of range");
            assert!(shape.committed_len() >= placed, "columns must fit the commitment");
            assert!(
                shape.committed_len() - placed < lane_block,
                "a whole lane of the commitment carries no data"
            );
            assert!(shape.committed_len() <= 1usize << shape.mu);
            // And every column really does live inside those lanes.
            for p in placements.iter().flatten() {
                assert!(p.offset + (1usize << p.n_vars) <= shape.committed_len());
            }
        }
    }
}
