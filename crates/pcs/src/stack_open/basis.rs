use std::mem::MaybeUninit;

use primitives::field::{F64, F192};
use zk_alloc::ArenaVec;

use super::{RingSwitchOpen, StackClaim};
use crate::ring_switch::{DeferredRingSwitchOutput, combine_deferred_chunk};
use crate::whir::{INITIAL_BASIS_CHUNK, SumcheckMessage, build_eq_table_ext_seeded, build_initial_basis};

struct PointWeight<'a> {
    offset: usize,
    end: usize,
    slot: usize,
    stride: usize,
    low: &'a [F192],
    high: ArenaVec<F192>,
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
        let mut high = zk_alloc::alloc_uninit(1 << high_point.len());
        build_eq_table_ext_seeded(high_point, lambda, &mut high);
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
        build_eq_table_ext_seeded(self.low, self.high[first / len], &mut scratch[..len]);
        // SAFETY: the build above initializes this prefix before the scatter reads it.
        let eq = unsafe { std::slice::from_raw_parts(scratch.as_ptr().cast::<F192>(), len) };
        let dst_offset = base + first * self.stride - start;
        for (i, &value) in eq.iter().enumerate() {
            dst[dst_offset + i * self.stride] += value;
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
) -> (ArenaVec<F192>, SumcheckMessage) {
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
    let ring_end = ring.offset + (1 << ring.qflock_vars);
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
