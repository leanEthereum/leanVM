use std::mem::MaybeUninit;

use primitives::field::F192;
use primitives::multilinear::fill_eq_table_uninit;
use zk_alloc::ArenaVec;

use super::{StackClaim, Term};
use crate::ring_switch::{DeferredRingSwitchOutput, combine_deferred_chunk};
use crate::whir::INITIAL_BASIS_CHUNK;

/// One term of a point claim: its slice, and its eq table split at the fill chunk.
struct PointWeight<'a> {
    offset: usize,
    end: usize,
    slot: usize,
    stride: usize,
    low: &'a [F192],
    high: ArenaVec<F192>,
}

impl<'a> PointWeight<'a> {
    fn new(claim: &'a StackClaim, term: &Term, lambda: F192, chunk_log: usize) -> Self {
        let (offset, slot, stride_log) = (term.offset, claim.slot, claim.stride_log);
        let point = &claim.point[..term.n_vars];
        let len = 1usize << (stride_log + point.len());
        let stride = 1usize << stride_log;
        assert!(offset.is_multiple_of(len), "claim must be aligned to its support");
        assert!(slot < stride, "claim slot must fit the stride");
        let low_vars = point.len().min(chunk_log.saturating_sub(stride_log));
        let (low, high_point) = point.split_at(low_vars);
        let mut high = zk_alloc::alloc_uninit(1 << high_point.len());
        fill_eq_table_uninit(high_point, lambda * term.scale, &mut high);
        // SAFETY: the seeded equality build initializes the whole table.
        let high = unsafe { zk_alloc::assume_init(high) };
        Self {
            offset,
            end: offset + len,
            slot,
            stride,
            low,
            high,
        }
    }

    fn add(&self, start: usize, dst: &mut [F192], scratch: &mut [MaybeUninit<F192>]) {
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
        let len = 1usize << self.low.len();
        assert!(first.is_multiple_of(len) && end - first == len);
        fill_eq_table_uninit(self.low, self.high[first / len], &mut scratch[..len]);
        // SAFETY: the build above initializes this prefix before the scatter reads it.
        let eq = unsafe { std::slice::from_raw_parts(scratch.as_ptr().cast::<F192>(), len) };
        let dst_offset = base + first * self.stride - start;
        for (i, &value) in eq.iter().enumerate() {
            dst[dst_offset + i * self.stride] += value;
        }
    }
}

/// The stacked opening's lifted weight, one aligned chunk at a time.
///
/// It is the lambda-weighted sum of every claim's weight over the stack:
///
/// - each ring-switched claim's terms, each over its own slice;
/// - each point claim's terms' equality weights, each over its own support.
///
/// It is never stored whole: the opening's first pass and its first fold each refill the chunks they read.
pub(super) struct StackWeight<'a> {
    /// Each point claim term's weight, its high equality table built once.
    weights: Vec<PointWeight<'a>>,
    /// For each lane block, the point terms whose support meets it.
    by_lane: Vec<Vec<usize>>,
    /// For each lane block, the ring-switched claims one of whose terms meets it.
    rings_by_lane: Vec<Vec<usize>>,
    rs_outputs: &'a [DeferredRingSwitchOutput],
    /// Words per lane block.
    lane_block: usize,
}

impl<'a> StackWeight<'a> {
    /// The weight of `claims` batched by `lambdas`, plus the ring-switched claims' `rs_outputs`.
    pub(super) fn new(
        stack_len: usize,
        lane_block: usize,
        claims: &'a [StackClaim],
        lambdas: &[F192],
        rs_outputs: &'a [DeferredRingSwitchOutput],
    ) -> Self {
        assert_eq!(claims.len(), lambdas.len());
        // A fill writes one chunk, or one whole lane block when blocks are smaller.
        let chunk_log = lane_block.min(INITIAL_BASIS_CHUNK).ilog2() as usize;
        let weights: Vec<_> = claims
            .iter()
            .zip(lambdas)
            .flat_map(|(claim, &lambda)| {
                claim
                    .terms
                    .iter()
                    .map(move |term| PointWeight::new(claim, term, lambda, chunk_log))
            })
            .collect();

        // Index the terms by the lane blocks they touch, so a fill visits only those.
        let n_lanes = stack_len / lane_block;
        let mut by_lane = vec![Vec::new(); n_lanes];
        for (index, weight) in weights.iter().enumerate() {
            for lane in &mut by_lane[weight.offset / lane_block..weight.end.div_ceil(lane_block)] {
                lane.push(index);
            }
        }
        let mut rings_by_lane: Vec<Vec<usize>> = vec![Vec::new(); n_lanes];
        for (index, output) in rs_outputs.iter().enumerate() {
            for (start, end) in output.ranges() {
                for lane in &mut rings_by_lane[start / lane_block..end.div_ceil(lane_block)] {
                    if lane.last() != Some(&index) {
                        lane.push(index);
                    }
                }
            }
        }

        Self {
            weights,
            by_lane,
            rings_by_lane,
            rs_outputs,
            lane_block,
        }
    }

    /// Writes the weight of words `start..start + dst.len()`, one aligned fill chunk.
    pub(super) fn fill(&self, start: usize, dst: &mut [F192]) {
        dst.fill(F192::ZERO);
        let lane = start / self.lane_block;

        // The ring-switched claims this chunk's lane block meets.
        for &index in &self.rings_by_lane[lane] {
            combine_deferred_chunk(std::slice::from_ref(&self.rs_outputs[index]), start, dst);
        }

        // The point terms of this chunk's lane block.
        let mut scratch = [MaybeUninit::uninit(); INITIAL_BASIS_CHUNK];
        for &index in &self.by_lane[lane] {
            self.weights[index].add(start, dst, &mut scratch);
        }
    }
}
