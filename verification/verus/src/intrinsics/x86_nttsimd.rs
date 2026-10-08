//! The memory helpers of the x86-64 NTT butterfly kernels (`ntt_simd`): their loads and stores, with trusted
//! specifications.
//!
//! Production's kernels load and store through raw pointers into the two rows. Verus cannot tie a pointer to
//! the slice it came from, so the verified copies take the rows as slices and an offset, and call these helpers,
//! whose bodies are production's load or store at that offset. `tests/equivalence/intrinsics_x86_nttsimd.rs`
//! checks each against the memory it reads or writes. They are `unsafe fn`, as the loads and stores they wrap; their
//! `requires` is their safety condition.
#[cfg(verus_keep_ghost)]
use super::x86::{m128_bytes, m256, m512};
use crate::gf2_64::F64;
use core::arch::x86_64::*;
use vstd::prelude::*;

verus! {

/// `_mm512_loadu_si512` of the eight words of `row` from `at`.
#[cfg(target_feature = "avx512f")]
#[verifier::external_body]
#[inline(always)]
pub unsafe fn loadu512_at(row: &[F64], at: usize) -> (r: __m512i)
    requires
        at + 8 <= row.len(),
    ensures
        forall|j: int| 0 <= j < 8 ==> #[trigger] m512(r)[j] == row@[at + j].0,
{
    // SAFETY: `at + 8 <= row.len()`, and `F64` is a transparent `u64`.
    unsafe { _mm512_loadu_si512(row.as_ptr().add(at).cast()) }
}

/// `_mm512_storeu_si512` of `v` to the eight words of `row` from `at`.
#[cfg(target_feature = "avx512f")]
#[verifier::external_body]
#[inline(always)]
pub unsafe fn storeu512_at(row: &mut [F64], at: usize, v: __m512i)
    requires
        at + 8 <= old(row).len(),
    ensures
        final(row).len() == old(row).len(),
        forall|j: int|
            0 <= j < old(row).len() ==> #[trigger] final(row)@[j] == if at <= j < at + 8 {
                F64(m512(v)[j - at])
            } else {
                old(row)@[j]
            },
{
    // SAFETY: `at + 8 <= row.len()`, and `F64` is a transparent `u64`.
    unsafe { _mm512_storeu_si512(row.as_mut_ptr().add(at).cast(), v) }
}

/// `_mm256_loadu_si256` of the four words of `row` from `at`.
#[cfg(target_feature = "avx")]
#[verifier::external_body]
#[inline(always)]
pub unsafe fn loadu256_at(row: &[F64], at: usize) -> (r: __m256i)
    requires
        at + 4 <= row.len(),
    ensures
        forall|j: int| 0 <= j < 4 ==> #[trigger] m256(r)[j] == row@[at + j].0,
{
    // SAFETY: `at + 4 <= row.len()`, and `F64` is a transparent `u64`.
    unsafe { _mm256_loadu_si256(row.as_ptr().add(at).cast()) }
}

/// `_mm256_storeu_si256` of `v` to the four words of `row` from `at`.
#[cfg(target_feature = "avx")]
#[verifier::external_body]
#[inline(always)]
pub unsafe fn storeu256_at(row: &mut [F64], at: usize, v: __m256i)
    requires
        at + 4 <= old(row).len(),
    ensures
        final(row).len() == old(row).len(),
        forall|j: int|
            0 <= j < old(row).len() ==> #[trigger] final(row)@[j] == if at <= j < at + 4 {
                F64(m256(v)[j - at])
            } else {
                old(row)@[j]
            },
{
    // SAFETY: `at + 4 <= row.len()`, and `F64` is a transparent `u64`.
    unsafe { _mm256_storeu_si256(row.as_mut_ptr().add(at).cast(), v) }
}

/// `_mm_loadu_si128` of 16 bytes.
#[verifier::external_body]
#[inline(always)]
pub unsafe fn loadu128_bytes(x: &[u8; 16]) -> (r: __m128i)
    ensures
        m128_bytes(r) == *x,
{
    // SAFETY: `x` is 16 readable bytes; SSE2 is part of the x86-64 baseline.
    unsafe { _mm_loadu_si128(x.as_ptr().cast()) }
}

} // verus!
