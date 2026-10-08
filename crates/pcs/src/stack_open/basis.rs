use std::mem::MaybeUninit;

use primitives::field::F192;
use primitives::multilinear::{eq_table_seeded, fill_eq_table_uninit};

use super::StackClaim;
use crate::ring_switch::RingSwitch;
use crate::ring_switch::{DeferredWeight, combine_deferred_chunk};
use crate::whir::INITIAL_BASIS_CHUNK;

struct PointWeight<'a> {
    offset: usize,
    end: usize,
    slot: usize,
    stride: usize,
    low: &'a [F192],
    high: Vec<F192>,
}

impl<'a> PointWeight<'a> {
    fn new(claim: &'a StackClaim, lambda: F192, chunk_log: usize) -> Self {
        let (offset, slot, stride_log, point) = match claim {
            StackClaim::Point { offset, low_point, .. } => (*offset, 0, 0, low_point.as_slice()),
            StackClaim::Strided {
                offset,
                slot,
                stride_log,
                point,
                ..
            } => (*offset, *slot, *stride_log, point.as_slice()),
        };
        let len = 1usize << (stride_log + point.len());
        let stride = 1usize << stride_log;
        assert!(offset.is_multiple_of(len), "claim must be aligned to its support");
        assert!(slot < stride, "claim slot must fit the stride");
        let low_vars = point.len().min(chunk_log.saturating_sub(stride_log));
        let (low, high_point) = point.split_at(low_vars);
        let high = eq_table_seeded(high_point, lambda);
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
/// - each ring-switched region's combined weight, over that region;
/// - each point claim's equality weight, over its own support.
///
/// It is filled one chunk at a time, as the opening reads it.
pub(super) struct StackWeight<'a> {
    /// Each point claim's weight, its high equality table built once.
    weights: Vec<PointWeight<'a>>,
    /// For each lane block, the point claims whose support meets it.
    by_lane: Vec<Vec<usize>>,
    /// Each ring-switched region: its first word, its end, and its claims' weights.
    regions: Vec<(usize, usize, &'a [DeferredWeight])>,
    /// Words per lane block.
    lane_block: usize,
}

impl<'a> StackWeight<'a> {
    /// The weight of `claims` batched by `lambdas`, plus the ring-switched regions `rings`.
    pub(super) fn new(
        stack_len: usize,
        lane_block: usize,
        claims: &'a [StackClaim],
        lambdas: &[F192],
        rings: &[RingSwitch],
        rs_outputs: &'a [DeferredWeight],
    ) -> Self {
        assert_eq!(claims.len(), lambdas.len());
        // A fill writes one chunk, or one whole lane block when blocks are smaller.
        let chunk_log = lane_block.min(INITIAL_BASIS_CHUNK).ilog2() as usize;
        let span = tracing::info_span!("Point high eq tables", claims = claims.len(), chunk_log).entered();
        let weights: Vec<_> = claims
            .iter()
            .zip(lambdas)
            .map(|(claim, &lambda)| PointWeight::new(claim, lambda, chunk_log))
            .collect();
        drop(span);

        // Index the claims by the lane blocks they touch, so a fill visits only those.
        let span = tracing::info_span!("Point lane index", lanes = stack_len / lane_block).entered();
        let mut by_lane = vec![Vec::new(); stack_len / lane_block];
        for (index, weight) in weights.iter().enumerate() {
            for lane in &mut by_lane[weight.offset / lane_block..weight.end.div_ceil(lane_block)] {
                lane.push(index);
            }
        }
        drop(span);

        // Each ring's outputs are its own run of the outputs, in ring order.
        let mut first = 0;
        let regions = rings
            .iter()
            .map(|ring| {
                let outputs = &rs_outputs[first..first + ring.claims.len()];
                first += ring.claims.len();
                (ring.offset, ring.offset + (1usize << ring.qflock_vars), outputs)
            })
            .collect();
        assert_eq!(first, rs_outputs.len());
        tracing::info!(
            point_claims = weights.len(),
            point_high_bytes = weights.iter().map(|weight| weight.high.len() * size_of::<F192>()).sum::<usize>(),
            point_claim_elements = weights.iter().map(|weight| (weight.end - weight.offset) / weight.stride).sum::<usize>(),
            lane_index_entries = by_lane.iter().map(Vec::len).sum::<usize>(),
            ring_claim_elements = rings.iter().map(|ring| (1usize << ring.qflock_vars) * ring.claims.len()).sum::<usize>(),
            "Basis weight shape"
        );

        Self {
            weights,
            by_lane,
            regions,
            lane_block,
        }
    }

    /// Writes the weight of words `start..start + dst.len()`, one aligned fill chunk.
    #[inline]
    pub(super) fn fill(&self, start: usize, dst: &mut [F192]) {
        dst.fill(F192::ZERO);
        self.fill_ring(start, dst);
        self.fill_points(start, dst);
    }

    #[inline]
    fn fill_ring(&self, start: usize, dst: &mut [F192]) {
        // The ring-switched regions this chunk meets.
        for &(offset, end, outputs) in &self.regions {
            let lo = start.max(offset);
            let hi = (start + dst.len()).min(end);
            if lo < hi {
                combine_deferred_chunk(outputs, lo - offset, &mut dst[lo - start..hi - start]);
            }
        }
    }

    #[inline]
    fn fill_points(&self, start: usize, dst: &mut [F192]) {
        // The point claims of this chunk's lane block.
        let mut scratch = [MaybeUninit::uninit(); INITIAL_BASIS_CHUNK];
        for &index in &self.by_lane[start / self.lane_block] {
            self.weights[index].add(start, dst, &mut scratch);
        }
    }

    /// Attribution-only schedule: identical weights, but whole-vector phases rather than hot chunks.
    #[cfg(leanvm_basis_staged)]
    pub(super) fn materialize(&self, stack_len: usize) -> Vec<F192> {
        let chunk = self.lane_block.min(INITIAL_BASIS_CHUNK);
        let mut dense = tracing::info_span!(
            "Basis staged allocation zero",
            output_bytes = stack_len * size_of::<F192>(),
        ).in_scope(|| vec![F192::ZERO; stack_len]);
        tracing::info_span!(
            "Basis staged Phi application",
            regions = self.regions.len(),
            claim_elements = self.regions.iter().map(|(start, end, claims)| (end - start) * claims.len()).sum::<usize>(),
        ).in_scope(|| {
            parallel::chunks_mut(&mut dense, chunk, |index, dst| self.fill_ring(index * chunk, dst));
        });
        tracing::info_span!(
            "Basis staged point eq",
            claims = self.weights.len(),
            claim_elements = self.weights.iter().map(|weight| (weight.end - weight.offset) / weight.stride).sum::<usize>(),
        ).in_scope(|| {
            parallel::chunks_mut(&mut dense, chunk, |index, dst| self.fill_points(index * chunk, dst));
        });
        dense
    }
}
