//! The memory helpers of the NEON NTT butterfly kernels (`ntt_simd`): their loads and stores, with trusted
//! specifications.
//!
//! Production's kernels load and store through raw pointers into the two rows. Verus cannot tie a pointer to
//! the slice it came from, so the verified copies take the rows as slices and an offset, and call these helpers,
//! whose bodies are production's `vld1q_u64` / `vst1q_u64` at that offset.
//! `tests/equivalence/intrinsics_aarch64_nttsimd.rs` checks each against the memory it reads or writes. They are
//! `unsafe fn`, as the loads and stores they wrap; their `requires` is their safety condition.
#[cfg(verus_keep_ghost)]
use super::aarch64::u64x2;
use crate::gf2_64::F64;
use core::arch::aarch64::*;
use vstd::prelude::*;

verus! {

/// `vld1q_u64` of the two words of `row` from `at`.
#[verifier::external_body]
#[inline(always)]
pub unsafe fn vld1q_u64_at(row: &[F64], at: usize) -> (r: uint64x2_t)
    requires
        at + 2 <= row.len(),
    ensures
        u64x2(r)[0] == row@[at as int].0,
        u64x2(r)[1] == row@[at + 1].0,
{
    // SAFETY: `at + 2 <= row.len()`, `F64` is a transparent `u64`, and NEON is part of the aarch64 baseline.
    unsafe { vld1q_u64(row.as_ptr().add(at).cast()) }
}

/// `vst1q_u64` of `v` to the two words of `row` from `at`.
#[verifier::external_body]
#[inline(always)]
pub unsafe fn vst1q_u64_at(row: &mut [F64], at: usize, v: uint64x2_t)
    requires
        at + 2 <= old(row).len(),
    ensures
        final(row).len() == old(row).len(),
        forall|j: int|
            0 <= j < old(row).len() ==> #[trigger] final(row)@[j] == if at <= j < at + 2 {
                F64(u64x2(v)[j - at])
            } else {
                old(row)@[j]
            },
{
    // SAFETY: `at + 2 <= row.len()`, `F64` is a transparent `u64`, and NEON is part of the aarch64 baseline.
    unsafe { vst1q_u64(row.as_mut_ptr().add(at).cast(), v) }
}

} // verus!
