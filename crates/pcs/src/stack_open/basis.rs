use std::mem::MaybeUninit;

use primitives::field::{F64, F192};
use primitives::multilinear::fill_eq_table_uninit;

use super::{RingSwitchOpen, StackClaim};
use crate::ring_switch::{DeferredRingSwitchOutput, combine_deferred_chunk};
use crate::whir::{INITIAL_BASIS_CHUNK, SumcheckMessage, build_initial_basis};

struct PointWeight<'a> {
    offset: usize,
    end: usize,
    low: &'a [F192],
    high: Vec<F192>,
}

impl<'a> PointWeight<'a> {
    fn new(claim: &'a StackClaim, lambda: F192, chunk_log: usize) -> Self {
        let StackClaim::Point { offset, low_point, .. } = claim;
        let (offset, len) = (*offset, 1usize << low_point.len());
        assert!(offset.is_multiple_of(len), "claim must be aligned to its support");
        let (low, high_point) = low_point.split_at(low_point.len().min(chunk_log));
        let mut high = Box::new_uninit_slice(1 << high_point.len()).into_vec();
        fill_eq_table_uninit(high_point, lambda, &mut high);
        // SAFETY: the seeded equality build initializes the whole table.
        let high = unsafe { high.into_boxed_slice().assume_init() }.into_vec();
        Self {
            offset,
            end: offset + len,
            low,
            high,
        }
    }

    fn add(&self, start: usize, dst: &mut [F192], scratch: &mut [MaybeUninit<F192>]) {
        let lo = start.max(self.offset);
        let hi = (start + dst.len()).min(self.end);
        if lo >= hi {
            return;
        }
        let first = lo - self.offset;
        let len = 1usize << self.low.len();
        assert!(first.is_multiple_of(len) && hi - lo == len);
        fill_eq_table_uninit(self.low, self.high[first / len], &mut scratch[..len]);
        // SAFETY: the build above initializes this prefix before the scatter reads it.
        let eq = unsafe { std::slice::from_raw_parts(scratch.as_ptr().cast::<F192>(), len) };
        for (dst, &value) in dst[lo - start..hi - start].iter_mut().zip(eq) {
            *dst += value;
        }
    }
}

pub(super) fn build(
    stack: &[F64],
    lane_block: usize,
    claims: &[StackClaim],
    lambdas: &[F192],
    ring: &RingSwitchOpen,
    rs_outputs: &[DeferredRingSwitchOutput],
) -> (Vec<F192>, SumcheckMessage) {
    assert_eq!(claims.len(), lambdas.len());
    let chunk_log = lane_block.min(INITIAL_BASIS_CHUNK).ilog2() as usize;
    let weights: Vec<_> = claims
        .iter()
        .zip(lambdas)
        .map(|(claim, &lambda)| PointWeight::new(claim, lambda, chunk_log))
        .collect();
    let mut by_lane = vec![Vec::new(); stack.len() / lane_block];
    for (index, weight) in weights.iter().enumerate() {
        for lane in &mut by_lane[weight.offset / lane_block..weight.end.div_ceil(lane_block)] {
            lane.push(index);
        }
    }
    let ring_end = ring.offset + (1 << ring.qkeccak_vars());
    build_initial_basis(stack, lane_block, |start, dst| {
        dst.fill(F192::ZERO);
        let lo = start.max(ring.offset);
        let hi = (start + dst.len()).min(ring_end);
        if lo < hi {
            combine_deferred_chunk(rs_outputs, lo - ring.offset, &mut dst[lo - start..hi - start]);
        }
        let mut scratch = [MaybeUninit::uninit(); INITIAL_BASIS_CHUNK];
        for &index in &by_lane[start / lane_block] {
            weights[index].add(start, dst, &mut scratch);
        }
    })
}
