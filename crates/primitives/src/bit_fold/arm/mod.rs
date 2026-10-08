//! AArch64 byte tables with NEON EOR3 accumulation.
//!
//! Entries retain the portable backend's compact three-limb layout. Pairs of
//! lookups feed two EOR3 accumulators. The high limb uses an eight-byte load,
//! never an overread of the final table entry.

use super::{BLOCK, F192};
use core::arch::aarch64::{
    vcombine_u64, vdup_n_u64, vdupq_n_u64, veor3q_u64, veorq_u64, vgetq_lane_u64, vld1_u64, vld1q_u64,
};

type Entry = [u64; 3];

#[inline(always)]
fn fold_row<const CHUNKS: usize>(tables: &[[Entry; 256]], row: &[u8; CHUNKS]) -> F192 {
    let tables: &[[Entry; 256]; CHUNKS] = tables.try_into().expect("one table per byte");
    // SAFETY: This module requires aarch64 SHA3. The low two limbs use a
    // 16-byte load and the high limb an 8-byte load, both within the entry.
    unsafe {
        let mut lo = vdupq_n_u64(0);
        let mut hi = vdupq_n_u64(0);
        for j in 0..CHUNKS / 2 {
            let a = tables[2 * j][usize::from(row[2 * j])].as_ptr();
            let b = tables[2 * j + 1][usize::from(row[2 * j + 1])].as_ptr();
            lo = veor3q_u64(lo, vld1q_u64(a), vld1q_u64(b));
            hi = veor3q_u64(
                hi,
                vcombine_u64(vld1_u64(a.add(2)), vdup_n_u64(0)),
                vcombine_u64(vld1_u64(b.add(2)), vdup_n_u64(0)),
            );
        }
        if !CHUNKS.is_multiple_of(2) {
            let a = tables[CHUNKS - 1][usize::from(row[CHUNKS - 1])].as_ptr();
            lo = veorq_u64(lo, vld1q_u64(a));
            hi = veorq_u64(hi, vcombine_u64(vld1_u64(a.add(2)), vdup_n_u64(0)));
        }
        F192 {
            c0: vgetq_lane_u64::<0>(lo),
            c1: vgetq_lane_u64::<1>(lo),
            c2: vgetq_lane_u64::<0>(hi),
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct Imp {
    tables: Vec<[Entry; 256]>,
}

impl Imp {
    pub(super) fn new(weights: &[F192]) -> Self {
        let tables = weights
            .as_chunks::<8>()
            .0
            .iter()
            .map(|weights| {
                let mut sums = [[0; 3]; 256];
                for v in 1..256usize {
                    let low = v.isolate_lowest_one();
                    let w = weights[low.trailing_zeros() as usize];
                    let prev = sums[v ^ low];
                    sums[v] = [prev[0] ^ w.c0, prev[1] ^ w.c1, prev[2] ^ w.c2];
                }
                sums
            })
            .collect();
        Self { tables }
    }

    pub(super) fn new_f192(weights: &[F192]) -> Self {
        Self::new(weights)
    }

    #[inline]
    pub(super) fn fold_block<const CHUNKS: usize>(&self, rows: &[[u8; CHUNKS]], out: &mut [F192; BLOCK]) {
        for (o, row) in out.iter_mut().zip(rows) {
            *o = fold_row(&self.tables, row);
        }
    }

    pub(super) const fn slice(xs: &[F192; BLOCK]) -> Sliced {
        *xs
    }

    #[inline]
    pub(super) fn apply_sliced_add(&self, xs: &Sliced, out: &mut [F192]) {
        self.apply_add_f192(xs, out);
    }

    #[inline]
    pub(super) fn apply_add_f192(&self, xs: &[F192; BLOCK], out: &mut [F192]) {
        for (o, x) in out.iter_mut().zip(xs) {
            let mut row = [0u8; 24];
            row[..8].copy_from_slice(&x.c0.to_le_bytes());
            row[8..16].copy_from_slice(&x.c1.to_le_bytes());
            row[16..].copy_from_slice(&x.c2.to_le_bytes());
            *o += fold_row(&self.tables, &row);
        }
    }
}

pub(super) type Sliced = [F192; BLOCK];
