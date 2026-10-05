use primitives::field::{F192, mul4};
use primitives::multilinear::{eq_table, eq_table_seeded};

use super::{RingSwitch, StackClaim};
use crate::ring_switch::{DeferredWeight, combine_deferred_chunk};
use crate::whir::INITIAL_BASIS_CHUNK;

/// One variable of a claim's equality weight.
#[derive(Clone, Copy)]
enum Coord {
    /// Fixed to a bit: the weight is zero off it.
    Bit(bool),
    /// A coordinate of the claim's point.
    Value(F192),
}

impl Coord {
    /// The equality factor `eq(c, r)`, which is `1 + c + r` in characteristic 2.
    fn eq(self, r: F192) -> F192 {
        match self {
            Self::Bit(true) => r,
            Self::Bit(false) => F192::ONE + r,
            Self::Value(c) => F192::ONE + c + r,
        }
    }
}

/// A claim's equality weight, nonzero only on one slot of each stride of an aligned block.
///
/// Over the stack's variables, the lowest are fixed to the slot's bits, the next ones are the point's, and the rest are fixed to the block offset's bits.
#[derive(Clone, Debug, PartialEq)]
struct EqWeight {
    offset: usize,
    slot: usize,
    stride_log: usize,
    point: Vec<F192>,
}

impl EqWeight {
    fn of(claim: &StackClaim) -> Self {
        match claim {
            StackClaim::Point { offset, low_point, .. } => Self {
                offset: *offset,
                slot: 0,
                stride_log: 0,
                point: low_point.clone(),
            },
            StackClaim::Strided {
                offset,
                slot,
                stride_log,
                point,
                ..
            } => Self {
                offset: *offset,
                slot: *slot,
                stride_log: *stride_log,
                point: point.clone(),
            },
        }
    }

    /// The weight once its lane variables are folded by the challenges, and the factor they leave.
    ///
    /// - Folding a variable multiplies the weight by its equality factor at the challenge.
    /// - The variables above the folded ones move down by one per challenge.
    /// - A bit left between point coordinates becomes the coordinate 0 or 1, which has the same weight.
    ///
    /// ```text
    ///     before:  [ slot bits | point coordinates | offset bits ]
    ///     folded:              [ lane variables ]                 (a window anywhere in the line)
    ///     after:   [ slot bits | point coordinates | offset bits ]  shorter by the window
    /// ```
    fn fold_lanes(&self, lane_vars: usize, rs: &[F192]) -> (F192, Self) {
        let block_vars = self.stride_log + self.point.len();
        let top = block_vars.max(lane_vars + rs.len());
        let mut coords: Vec<Coord> = (0..top)
            .map(|i| match i {
                _ if i < self.stride_log => Coord::Bit((self.slot >> i) & 1 == 1),
                _ if i < block_vars => Coord::Value(self.point[i - self.stride_log]),
                _ => Coord::Bit((self.offset >> i) & 1 == 1),
            })
            .collect();
        let factor =
            (coords.drain(lane_vars..lane_vars + rs.len()).zip(rs)).fold(F192::ONE, |acc, (c, &r)| acc * c.eq(r));

        // Re-split: the bits below the first point coordinate are the slot, those past the last one the offset.
        let is_value = |c: &Coord| matches!(c, Coord::Value(_));
        let first = coords.iter().position(is_value).unwrap_or(coords.len());
        let end = coords.iter().rposition(is_value).map_or(first, |i| i + 1);
        let bit = |i: usize| usize::from(matches!(coords[i], Coord::Bit(true))) << i;
        let point = coords[first..end]
            .iter()
            .map(|&c| match c {
                Coord::Bit(false) => F192::ZERO,
                Coord::Bit(true) => F192::ONE,
                Coord::Value(v) => v,
            })
            .collect();
        let folded = Self {
            offset: (end..coords.len()).map(bit).sum::<usize>() | (self.offset >> top) << coords.len(),
            slot: (0..first).map(bit).sum(),
            stride_log: first,
            point,
        };
        (factor, folded)
    }
}

/// One claim's batched weight, laid out for fills one aligned chunk at a time.
struct PointWeight {
    offset: usize,
    end: usize,
    slot: usize,
    stride: usize,
    /// The equality table over the point coordinates inside one chunk.
    low: Vec<F192>,
    /// The batched equality table over the rest: one scale per chunk.
    high: Vec<F192>,
}

impl PointWeight {
    fn new(weight: &EqWeight, lambda: F192, chunk_log: usize) -> Self {
        let EqWeight {
            offset,
            slot,
            stride_log,
            ref point,
        } = *weight;
        let len = 1usize << (stride_log + point.len());
        let stride = 1usize << stride_log;
        assert!(offset.is_multiple_of(len), "claim must be aligned to its support");
        assert!(slot < stride, "claim slot must fit the stride");
        let low_vars = point.len().min(chunk_log.saturating_sub(stride_log));
        let (low, high) = point.split_at(low_vars);
        Self {
            offset,
            end: offset + len,
            slot,
            stride,
            low: eq_table(low),
            high: eq_table_seeded(high, lambda),
        }
    }

    fn add(&self, start: usize, dst: &mut [F192]) {
        let base = self.offset + self.slot;
        let lo = start.max(base);
        let hi = (start + dst.len()).min(self.end);
        if lo >= hi {
            return;
        }
        let first = (lo - base).div_ceil(self.stride);
        let end = (hi - base).div_ceil(self.stride);
        if first == end {
            return;
        }
        let len = self.low.len();
        assert!(first.is_multiple_of(len) && end - first == len);
        // The chunk's entries are the low table scaled by the chunk's high entry.
        let scale = self.high[first / len];
        let dst = &mut dst[base + first * self.stride - start..];
        let (quads, tail) = self.low.as_chunks::<4>();
        for (q, &low) in quads.iter().enumerate() {
            for (k, p) in mul4([scale; 4], low).into_iter().enumerate() {
                dst[(4 * q + k) * self.stride] += p;
            }
        }
        for (i, &low) in tail.iter().enumerate() {
            dst[(4 * quads.len() + i) * self.stride] += scale * low;
        }
    }
}

/// The batched weights of several claims over a stack, indexed by the lane blocks they meet.
pub(crate) struct PointWeights {
    weights: Vec<PointWeight>,
    /// For each lane block, the claims whose support meets it.
    by_lane: Vec<Vec<usize>>,
    lane_block: usize,
}

impl PointWeights {
    fn new<'w>(len: usize, lane_block: usize, weights: impl IntoIterator<Item = (&'w EqWeight, F192)>) -> Self {
        // A fill writes one chunk, or one whole lane block when blocks are smaller.
        let chunk_log = lane_block.min(INITIAL_BASIS_CHUNK).ilog2() as usize;
        let weights: Vec<_> = weights
            .into_iter()
            .map(|(weight, lambda)| PointWeight::new(weight, lambda, chunk_log))
            .collect();

        // Index the claims by the lane blocks they touch, so a fill visits only those.
        let mut by_lane = vec![Vec::new(); len.div_ceil(lane_block)];
        for (index, weight) in weights.iter().enumerate() {
            for lane in &mut by_lane[weight.offset / lane_block..weight.end.div_ceil(lane_block)] {
                lane.push(index);
            }
        }
        Self {
            weights,
            by_lane,
            lane_block,
        }
    }

    /// Adds the weights of one aligned fill chunk of words.
    pub(crate) fn add(&self, start: usize, dst: &mut [F192]) {
        for &index in &self.by_lane[start / self.lane_block] {
            self.weights[index].add(start, dst);
        }
    }
}

/// A ring-switched region of the stack and its claims' weights.
struct RingRegion<'a> {
    offset: usize,
    end: usize,
    outputs: &'a [DeferredWeight],
}

/// The stacked opening's lifted weight, one aligned chunk at a time.
///
/// It is the lambda-weighted sum of every claim's weight over the stack:
///
/// - each ring-switched region's combined weight, over that region;
/// - each point claim's equality weight, over its own support.
///
/// It is never stored whole: the opening's first pass refills the chunks it reads.
/// The first fold refills only the ring-switched part, and folds the point claims in closed form.
pub(crate) struct StackWeight<'a> {
    /// Each point claim's equality weight, with its batching scalar.
    claims: Vec<(EqWeight, F192)>,
    points: PointWeights,
    regions: Vec<RingRegion<'a>>,
    lane_block: usize,
}

impl<'a> StackWeight<'a> {
    /// The weight of `claims` batched by `lambdas`, plus the ring-switched regions `rings`.
    pub(crate) fn new(
        stack_len: usize,
        lane_block: usize,
        claims: &[StackClaim],
        lambdas: &[F192],
        rings: &[RingSwitch],
        rs_outputs: &'a [DeferredWeight],
    ) -> Self {
        assert_eq!(claims.len(), lambdas.len());
        let claims: Vec<_> = claims.iter().map(EqWeight::of).zip(lambdas.iter().copied()).collect();
        let points = PointWeights::new(stack_len, lane_block, claims.iter().map(|(w, lambda)| (w, *lambda)));

        // Each ring's outputs are its own run of the outputs, in ring order.
        let mut first = 0;
        let regions = rings
            .iter()
            .map(|ring| {
                let outputs = &rs_outputs[first..first + ring.claims.len()];
                first += ring.claims.len();
                RingRegion {
                    offset: ring.offset,
                    end: ring.offset + (1usize << ring.qflock_vars),
                    outputs,
                }
            })
            .collect();
        assert_eq!(first, rs_outputs.len());

        Self {
            claims,
            points,
            regions,
            lane_block,
        }
    }

    /// Writes the weight of words `start..start + dst.len()`, one aligned fill chunk.
    pub(crate) fn fill(&self, start: usize, dst: &mut [F192]) {
        if !self.fill_rings(start, dst) {
            dst.fill(F192::ZERO);
        }
        self.points.add(start, dst);
    }

    /// Writes the ring-switched part of the weight of words `start..start + dst.len()`.
    ///
    /// # Returns
    ///
    /// Whether a ring-switched region meets the words: if none does, the buffer is left untouched.
    pub(crate) fn fill_rings(&self, start: usize, dst: &mut [F192]) -> bool {
        let mut met = false;
        for region in &self.regions {
            let lo = start.max(region.offset);
            let hi = (start + dst.len()).min(region.end);
            if lo < hi {
                if !met {
                    dst.fill(F192::ZERO);
                    met = true;
                }
                combine_deferred_chunk(region.outputs, lo - region.offset, &mut dst[lo - start..hi - start]);
            }
        }
        met
    }

    /// The point claims' part of the weight once its lane bits are folded by the challenges, over the folded words.
    ///
    /// # Why closed form
    ///
    /// Folding the lane variables of `lambda eq(p, .)` by `rs` leaves `lambda eq(p_lane, rs) eq(p_rest, .)`.
    /// That is again a claim's weight, so the fold costs no pass over the lanes it spans.
    pub(crate) fn fold_points(&self, rs: &[F192], len: usize) -> PointWeights {
        let lane_vars = self.lane_block.ilog2() as usize;
        let folded: Vec<_> = (self.claims.iter())
            .map(|(weight, lambda)| {
                let (factor, folded) = weight.fold_lanes(lane_vars, rs);
                (folded, *lambda * factor)
            })
            .collect();
        PointWeights::new(len, self.lane_block, folded.iter().map(|(w, lambda)| (w, *lambda)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_util::Rng;

    /// The weight written out word by word.
    fn dense(weight: &EqWeight, len: usize) -> Vec<F192> {
        let mut out = vec![F192::ZERO; len];
        for j in 0..1usize << weight.point.len() {
            let w = (weight.point.iter().enumerate()).fold(F192::ONE, |w, (i, &p)| {
                w * if (j >> i) & 1 == 1 { p } else { F192::ONE + p }
            });
            out[weight.offset + weight.slot + (j << weight.stride_log)] += w;
        }
        out
    }

    #[test]
    fn a_folded_weight_is_the_lane_fold_of_the_weight() {
        let mut rng = Rng::new(0xF01D);
        for (lane_vars, lanes, rounds) in [(0usize, 16usize, 4usize), (3, 40, 4), (4, 37, 4), (2, 5, 2), (3, 64, 1)] {
            let lane_block = 1 << lane_vars;
            let len = lanes * lane_block;
            let group = 1 << rounds;
            let n_out = lanes.div_ceil(group);
            // Supports below, at and above one lane, spanning some or all of the folded lane bits, strides
            // that reach into the lane bits, and a single word.
            let mut weights = Vec::new();
            for vars in 0..=(len.ilog2() as usize) {
                for stride_log in 0..=vars {
                    let size = 1usize << vars;
                    let offset = (rng.next_u64() as usize % (len / size)) * size;
                    weights.push(EqWeight {
                        offset,
                        slot: rng.next_u64() as usize % (1 << stride_log),
                        stride_log,
                        point: rng.ext_vec(vars - stride_log),
                    });
                }
            }
            let rs = rng.ext_vec(rounds);
            let lane_eq = eq_table(&rs);
            for weight in &weights {
                // Oracle: fold the dense weight lane by lane, the absent lanes zero.
                let w = dense(weight, len);
                let mut expected = vec![F192::ZERO; n_out * lane_block];
                for (lane, words) in w.chunks_exact(lane_block).enumerate() {
                    for (e, &x) in expected[(lane / group) * lane_block..].iter_mut().zip(words) {
                        *e += lane_eq[lane % group] * x;
                    }
                }
                let (factor, folded) = weight.fold_lanes(lane_vars, &rs);
                let actual: Vec<F192> = dense(&folded, n_out * lane_block).iter().map(|&x| factor * x).collect();
                assert_eq!(actual, expected, "lane_vars={lane_vars}, lanes={lanes}, {weight:?}");
            }
        }
    }
}
