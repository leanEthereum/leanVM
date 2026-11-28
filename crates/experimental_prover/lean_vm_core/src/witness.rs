//! `K`-valued columns stacked into one committed witness (§sec:stacking): columns laid
//! end to end, largest first at aligned offsets, into one multilinear `q` over
//! `F64`. An evaluation claim on column `i` at `ζ ∈ E` becomes the claim
//! `q̂(ζ, sel_i) = c` on the stack, where `sel_i` is the high-bit selector of
//! the column's offset.

use ::pcs::stack_open::{StackClaim, SumPart};
use primitives::field::{F64, F128};
use std::mem::MaybeUninit;

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

    /// The `2^n_vars` rows from `start` (a multiple of `2^n_vars`) as a column of their own.
    pub(crate) fn rows(&self, start: usize, n_vars: usize) -> Placement {
        assert!(start.is_multiple_of(1 << n_vars) && start + (1 << n_vars) <= 1 << self.n_vars);
        Placement {
            n_vars,
            offset: self.offset + start,
        }
    }

    /// The claim that the column takes `value` at row `point`, on the stack.
    pub(crate) fn claim(&self, point: Vec<F128>, value: F128) -> StackClaim {
        self.check_point(&point);
        StackClaim::Point {
            offset: self.offset,
            low_point: point,
            value,
        }
    }

    /// One part of a [`StackClaim::Sum`] at row `point`.
    pub(crate) fn sum_part(&self, point: Vec<F128>, scale: F128) -> SumPart {
        self.check_point(&point);
        SumPart {
            offset: self.offset,
            low_point: point,
            scale,
        }
    }

    /// The column's rows in `q`, the stack.
    pub(crate) fn view<'a>(&self, q: &'a [F64]) -> &'a [F64] {
        assert!(!self.is_virtual(), "a virtual column is not in the stack");
        &q[self.offset..][..1 << self.n_vars]
    }

    fn check_point(&self, point: &[F128]) {
        assert!(
            !self.is_virtual() && point.len() == self.n_vars,
            "a committed column's row point"
        );
    }
}

/// A column to write: the window a fill writes, in the stack or in a buffer of its own. Rows on
/// different threads may be written at once, so each write is `unsafe`, and the caller keeps them disjoint.
pub struct ColMut<'a> {
    words: parallel::SendPtr<F64>,
    len: usize,
    _q: std::marker::PhantomData<&'a mut [MaybeUninit<F64>]>,
}

// SAFETY: a `ColMut` writes only through `unsafe` calls whose callers keep the rows of concurrent writes disjoint.
unsafe impl Sync for ColMut<'_> {}
unsafe impl Send for ColMut<'_> {}

impl<'a> ColMut<'a> {
    /// No window: a column held elsewhere.
    pub const EMPTY: Self = Self {
        words: parallel::SendPtr(std::ptr::NonNull::dangling().as_ptr()),
        len: 0,
        _q: std::marker::PhantomData,
    };

    pub fn new(words: &'a mut [MaybeUninit<F64>]) -> Self {
        Self {
            words: parallel::SendPtr(words.as_mut_ptr().cast()),
            len: words.len(),
            _q: std::marker::PhantomData,
        }
    }

    pub const fn len(&self) -> usize {
        self.len
    }

    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Write `values` to rows `start..`.
    ///
    /// # Safety
    /// The rows are the column's, and no concurrent write or read reaches them.
    #[inline]
    pub unsafe fn write(&self, stream: &primitives::stream::Stream, start: usize, values: &[F64]) {
        debug_assert!(start + values.len() <= self.len);
        // SAFETY: forwarded to the caller.
        unsafe { stream.copy_uninit(self.words.0.add(start), values) };
    }

    /// Disjoint runs of `len` rows each, which split the column.
    pub fn runs_of(self, len: usize) -> Vec<&'a mut [MaybeUninit<F64>]> {
        assert!(len > 0 && self.len.is_multiple_of(len));
        (0..self.len / len)
            // SAFETY: the runs are disjoint rows of this window, and `self` is consumed.
            .map(|k| unsafe { std::slice::from_raw_parts_mut(self.words.0.add(k * len).cast(), len) })
            .collect()
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
        // Both fields are `pub`, and in release the shift below would mask an
        // underflowed amount into a plausible wrong length rather than panic.
        assert!(self.mu >= crate::pcs::LOG_BATCH, "a stack is at least one lane block");
        self.n_lanes << (self.mu - crate::pcs::LOG_BATCH)
    }
}

/// Per-column placements (offset + n_vars) and the stack's [`StackShape`] from the
/// columns' log-sizes alone, largest-first at aligned offsets ([`verifier::stack_offsets`]).
/// A `None` kappa marks a virtual (uncommitted) column. Depends only on lengths, so the
/// verifier can reconstruct it.
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
    // Floor at the PCS minimum (WHIR's level ladder needs room); tiny
    // witnesses zero-pad up. Both sides derive this identically from the kappas.
    let mu = placed_log.max(crate::pcs::MIN_STACKED_LOG);
    let placed: usize = committed.iter().map(|k| 1 << k).sum();
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
/// [`split_stack`] hands out one window per committed column and zeroes the pad
/// tail, which together cover the whole allocation, so it is written once each
/// column's fill has written its own window.
pub(crate) fn alloc_stack(shape: StackShape) -> Vec<MaybeUninit<F64>> {
    primitives::uninit_vec::<F64>(shape.committed_len())
}

/// Carve the stack into one window per committed column, in column order, and zero
/// the pad tail past the last one. A virtual column gets an empty window: it is not
/// in the stack, so its values need storage of their own.
///
/// Writing each column into its final place is what lets the whole witness be
/// written once. Copying columns in afterwards would move the entire stack a
/// second time for nothing, and allocating the stack zeroed
/// would memset all `2^m` slots only for the columns to overwrite them.
///
/// [`placements_of`] tiles the columns from offset 0, checked here, so consecutive
/// `split_at_mut` hands out disjoint windows covering `[0, placed)` and this zeroes
/// the rest.
pub(crate) fn split_stack<'a>(q: &'a mut [MaybeUninit<F64>], placements: &[Placement]) -> Vec<ColMut<'a>> {
    let mut order: Vec<usize> = (0..placements.len()).filter(|&i| !placements[i].is_virtual()).collect();
    order.sort_unstable_by_key(|&i| placements[i].offset);

    let mut windows: Vec<ColMut> = (0..placements.len()).map(|_| ColMut::EMPTY).collect();
    let mut rest = q;
    let mut placed = 0usize;
    for &i in &order {
        assert_eq!(
            placements[i].offset, placed,
            "the stacked columns must tile from 0 with no gap"
        );
        let (window, tail) = rest.split_at_mut(1 << placements[i].n_vars);
        windows[i] = ColMut::new(window);
        rest = tail;
        placed += 1 << placements[i].n_vars;
    }
    parallel::chunks_mut(rest, FILL_CHUNK, |_, pad| pad.fill(MaybeUninit::new(F64::ZERO)));
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
        // in the middle, and a stack far below the MIN_STACKED_LOG floor.
        let cases: [Vec<Option<usize>>; 5] = [
            vec![Some(20), Some(20)],
            vec![Some(20), Some(20), Some(0)],
            vec![Some(20), Some(19), Some(18), Some(17)],
            vec![Some(21), None, Some(19), None, Some(15)],
            vec![Some(3), Some(2)],
        ];
        for kappas in cases {
            let placed: usize = kappas.iter().flatten().map(|&k| 1usize << k).sum();
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
            // And every column really does live inside those lanes, aligned to its size.
            for p in placements.iter().filter(|p| !p.is_virtual()) {
                assert!(p.offset + (1usize << p.n_vars) <= shape.committed_len());
                assert_eq!(p.offset % (1 << p.n_vars), 0);
            }
        }
    }

    /// The windows of [`split_stack`] cover every committed word once, each column's rows in order, and zero the rest.
    #[test]
    fn the_stack_holds_the_columns() {
        let kappas = [Some(15), Some(13), None, Some(13), Some(10), Some(14), Some(9), Some(0)];
        let (placements, shape) = placements_of(&kappas);
        let value = |i: usize, u: usize| F64(((i as u64) << 32) + u as u64 + 1);
        let mut q = vec![F64(u64::MAX); shape.committed_len()];
        // SAFETY: the windows write only words.
        let windows = split_stack(unsafe { primitives::as_uninit_mut(&mut q) }, &placements);
        let stream = primitives::stream::Stream::new();
        for (i, window) in windows.iter().enumerate() {
            let column: Vec<F64> = (0..window.len()).map(|u| value(i, u)).collect();
            let cut = column.len().min(3);
            // SAFETY: the rows are the window's, written once.
            unsafe {
                window.write(&stream, 0, &column[..cut]);
                window.write(&stream, cut, &column[cut..]);
            }
        }
        drop(windows);
        let mut covered = 0;
        for (i, p) in placements.iter().enumerate().filter(|(_, p)| !p.is_virtual()) {
            let col = p.view(&q);
            assert!(
                (0..1 << p.n_vars).all(|u| col[u] == value(i, u)),
                "column {i} reads back in row order"
            );
            covered += 1 << p.n_vars;
        }
        assert_eq!(
            q.iter().filter(|w| w.0 != 0).count(),
            covered,
            "every other word is zero"
        );
    }
}
