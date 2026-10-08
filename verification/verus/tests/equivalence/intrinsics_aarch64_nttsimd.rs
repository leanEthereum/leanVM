//! The memory helpers of the NEON NTT butterfly kernels (`intrinsics::aarch64_nttsimd`) against their
//! specifications: the load returns the two words at its offset, read through `transmute` as `u64x2` is, and
//! the store writes exactly those two words and leaves the rest of the row as it was.
use core::arch::aarch64::*;
use core::mem::transmute;
use leanvm_verus::gf2_64::F64;
use leanvm_verus::intrinsics::aarch64_nttsimd as helpers;
use primitives::test_util::Rng;

const N: usize = 2_000;

#[test]
fn neon_row_loads_and_stores() {
    let mut rng = Rng::new(0x1D1);
    for _ in 0..N {
        let row: Vec<F64> = (0..9).map(|_| F64(rng.next_u64())).collect();
        for at in 0..=7 {
            let got = unsafe { transmute::<uint64x2_t, [u64; 2]>(helpers::vld1q_u64_at(&row, at)) };
            assert_eq!(got, [row[at].0, row[at + 1].0], "vld1q_u64_at at {at}");
            let words = [rng.next_u64(), rng.next_u64()];
            let mut stored = row.clone();
            unsafe { helpers::vst1q_u64_at(&mut stored, at, transmute::<[u64; 2], uint64x2_t>(words)) };
            for j in 0..row.len() {
                let want = if (at..at + 2).contains(&j) {
                    words[j - at]
                } else {
                    row[j].0
                };
                assert_eq!(stored[j].0, want, "vst1q_u64_at at {at} word {j}");
            }
        }
    }
}
