//! `K`-valued columns stacked into one committed witness (§sec:stacking): columns laid
//! end to end, largest first at aligned offsets, into one multilinear `q` over
//! `F64`. An evaluation claim on column `i` at `ζ ∈ E` becomes the claim
//! `q̂(ζ, sel_i) = c` on the stack, where `sel_i` is the high-bit selector of
//! the column's offset.

use crate::pcs::{RingSwitch, SliceClaim, StackClaim};
use primitives::field::F64;

/// What a column is, before it is placed.
#[derive(Clone, Copy, Debug)]
pub enum Source {
    /// A committed column of `2^kappa` words.
    Committed(usize),
    /// Not committed: port `port` of every instance of the committed column `column`, a
    /// packed witness whose instances are `2^stride_log` words apart. It carries data
    /// for the bus, while its evaluation claims settle against that witness.
    Port {
        column: usize,
        port: usize,
        stride_log: usize,
    },
    /// Not committed: a field of a committed word, which the opening reads through the word's bit slices.
    Sliced,
}

/// A committed column's window in the stacked witness: `2^n_vars` words from `offset`.
#[derive(Clone, Copy, Debug)]
pub struct Window {
    pub offset: usize,
    pub n_vars: usize,
}

impl Window {
    /// The window as a ring-switched region holding one claim.
    pub fn ring<E>(self, claim: SliceClaim<E>) -> RingSwitch<E> {
        RingSwitch {
            offset: self.offset,
            qflock_vars: self.n_vars,
            claims: vec![claim],
        }
    }
}

/// Where a column sits in the stacked witness.
#[derive(Clone, Copy, Debug)]
pub enum Placement {
    Committed(Window),
    /// Port `port` of every instance of the packed witness at `offset`, instances
    /// `2^stride_log` words apart.
    Port {
        offset: usize,
        port: usize,
        stride_log: usize,
    },
    /// A field of a committed word: its claims are its bits', which the opening ring-switches.
    Sliced,
}

impl Placement {
    /// The column's window, if it is committed.
    pub const fn window(&self) -> Option<Window> {
        match *self {
            Self::Committed(window) => Some(window),
            Self::Port { .. } | Self::Sliced => None,
        }
    }

    /// A claim on the column at `point`, located in the stack.
    ///
    /// - A committed column's is at its window, the point as the low point.
    /// - A port's is a strided evaluation of its packed witness: the low coordinates frozen to the port's bits.
    /// - A sliced column's is none: its bits' ring-switched claim stands for it.
    pub fn claim<E>(self, point: Vec<E>, value: E) -> Option<StackClaim<E>> {
        match self {
            Self::Committed(window) => Some(StackClaim::Point {
                offset: window.offset,
                low_point: point,
                value,
            }),
            Self::Port {
                offset,
                port,
                stride_log,
            } => Some(StackClaim::Strided {
                offset,
                slot: port,
                stride_log,
                point,
                value,
            }),
            Self::Sliced => None,
        }
    }
}

/// The committed stack's shape. `mu` is the log size everything public is derived
/// from (the claims' selector coords, the PCS level ladder), while `n_lanes` counts
/// the `2^(mu - LOG_BATCH)`-word lane blocks that actually carry data: the PCS
/// commits `committed_len()` words and never encodes or hashes the zero tail past
/// them. Only the prover needs `n_lanes`; the verifier's view of the commitment is
/// the same `2^mu`-word witness either way.
///
/// A zero-knowledge proof commits one more lane after them, of uniform words (`random_lane`).
#[derive(Clone, Copy, Debug)]
pub struct StackShape {
    pub mu: usize,
    pub n_lanes: usize,
    pub random_lane: bool,
}

impl StackShape {
    /// The lanes committed: the data's, then the random lane if there is one.
    pub const fn committed_lanes(&self) -> usize {
        self.n_lanes + self.random_lane as usize
    }

    /// Words actually committed: the placed columns rounded up to a whole lane, then the random lane.
    pub fn committed_len(&self) -> usize {
        // Both fields are `pub`, and in release the shift below would mask an
        // underflowed amount into a plausible wrong length rather than panic.
        assert!(self.mu >= crate::pcs::LOG_BATCH, "a stack is at least one lane block");
        self.committed_lanes() << (self.mu - crate::pcs::LOG_BATCH)
    }

    /// The shape a zero-knowledge proof commits for `placed` words: its lanes long enough for one random lane to hide the opening ([`::pcs::whir::config::MIN_LOG_N_HIDING`]), and room for that lane.
    pub fn hiding(placed: usize) -> Self {
        let mut mu = crate::log2_ceil_usize(placed.max(1))
            .max(crate::pcs::MIN_MU)
            .max(::pcs::whir::config::MIN_LOG_N_HIDING);
        loop {
            let n_lanes = placed.div_ceil(1 << (mu - crate::pcs::LOG_BATCH)).max(1);
            if n_lanes < 1 << crate::pcs::LOG_BATCH {
                return Self {
                    mu,
                    n_lanes,
                    random_lane: true,
                };
            }
            mu += 1;
        }
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

/// The committed columns' total length, before the stack's zero pad: the real witness size.
pub fn committed_len(placements: &[Placement]) -> usize {
    placements
        .iter()
        .filter_map(Placement::window)
        .map(|w| 1usize << w.n_vars)
        .sum()
}

/// Per-column placements and the stack's [`StackShape`] from the columns' sources
/// alone, the committed columns largest-first at aligned offsets. Depends only on
/// lengths, so the verifier can reconstruct it.
pub fn placements_of(sources: &[Source]) -> (Vec<Placement>, StackShape) {
    let kappas: Vec<Option<usize>> = sources
        .iter()
        .map(|s| match *s {
            Source::Committed(kappa) => Some(kappa),
            Source::Port { .. } | Source::Sliced => None,
        })
        .collect();
    let (offsets, placed) = stack_offsets(&kappas);
    let placements = sources
        .iter()
        .zip(&offsets)
        .map(|(s, &offset)| match *s {
            Source::Committed(n_vars) => Placement::Committed(Window { offset, n_vars }),
            Source::Port {
                column,
                port,
                stride_log,
            } => {
                assert!(kappas[column].is_some(), "a port is of a committed column");
                Placement::Port {
                    offset: offsets[column],
                    port,
                    stride_log,
                }
            }
            Source::Sliced => Placement::Sliced,
        })
        .collect();
    // Floor at the PCS minimum (WHIR's level ladder needs room); tiny
    // witnesses zero-pad up. Both sides derive this identically from the kappas.
    let mu = crate::log2_ceil_usize(placed.max(1)).max(crate::pcs::MIN_MU);
    // The columns tile from 0, so the padding is the tail: round it up to a whole
    // lane and the lanes past that are never committed at all.
    let n_lanes = placed.div_ceil(1 << (mu - crate::pcs::LOG_BATCH)).max(1);
    (
        placements,
        StackShape {
            mu,
            n_lanes,
            random_lane: false,
        },
    )
}

/// Chunk width for the bulk writes below: big enough to amortize the dispatch,
/// small enough to spread one column across cores.
const FILL_CHUNK: usize = 1 << 16;

/// Carve the stack into one mutable window per committed column, in column order,
/// and zero the pad tail past the last one. A port gets an empty window:
/// it is not in the stack, so its values need storage of their own.
///
/// Writing each column into its final place is what lets the whole witness be
/// written once. Copying columns in afterwards would move the entire stack a
/// second time (a gigabyte at scale) for nothing, and allocating the stack zeroed
/// would memset all `2^m` slots only for the columns to overwrite them.
///
/// The columns must tile from offset zero without gaps.
/// The returned windows are disjoint.
/// The remaining tail is zeroed.
pub fn split_stack<'a>(q: &'a mut [F64], placements: &[Placement]) -> Vec<&'a mut [F64]> {
    let mut order: Vec<(usize, Window)> = (placements.iter().enumerate())
        .filter_map(|(i, p)| Some((i, p.window()?)))
        .collect();
    order.sort_unstable_by_key(|&(_, w)| w.offset);

    let mut windows: Vec<&mut [F64]> = Vec::with_capacity(placements.len());
    windows.resize_with(placements.len(), || &mut []);
    let mut rest = q;
    let mut placed = 0usize;
    for (i, w) in order {
        assert_eq!(w.offset, placed, "the stacked columns must tile from 0 with no gap");
        let (window, tail) = rest.split_at_mut(1 << w.n_vars);
        windows[i] = window;
        rest = tail;
        placed += 1 << w.n_vars;
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
        // A power-of-two total, one word over one, one just under, a port
        // in the middle, and a stack far below the MIN_MU floor.
        let port = Source::Port {
            column: 0,
            port: 1,
            stride_log: 2,
        };
        let cases: [Vec<Option<usize>>; 5] = [
            vec![Some(20), Some(20)],
            vec![Some(20), Some(20), Some(0)],
            vec![Some(20), Some(19), Some(18), Some(17)],
            vec![Some(21), None, Some(19), None, Some(15)],
            vec![Some(3), Some(2)],
        ];
        for kappas in cases {
            let placed: usize = kappas.iter().flatten().map(|k| 1usize << k).sum();
            let sources: Vec<Source> = kappas.iter().map(|k| k.map_or(port, Source::Committed)).collect();
            let (placements, shape) = placements_of(&sources);
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
            for w in placements.iter().filter_map(Placement::window) {
                assert!(w.offset + (1usize << w.n_vars) <= shape.committed_len());
            }
        }
    }
}
