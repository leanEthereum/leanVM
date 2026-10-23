//! The carry-less products of the AVX2 kernels, at the width of the multiplier: a register of
//! 128-bit lanes, one with PCLMULQDQ alone and two with VPCLMULQDQ. Every operation is lane by
//! lane, as the AVX-512 kernels' are, so a kernel written once serves both widths.
//!
//! The intrinsics are safe to call: the module is compiled only where its features are.

use core::arch::x86_64::*;

#[cfg(target_feature = "vpclmulqdq")]
pub type V = __m256i;
#[cfg(not(target_feature = "vpclmulqdq"))]
pub type V = __m128i;

pub trait Vector: Copy {
    /// 128-bit lanes.
    const N: usize;
    /// # Safety
    /// `p` is valid for reading `2 * N` words.
    unsafe fn load(p: *const u64) -> Self;
    /// # Safety
    /// `p` is valid for writing `2 * N` words.
    unsafe fn store(p: *mut u64, v: Self);
    /// `2 * N` packs, a word each.
    ///
    /// # Safety
    /// `p` is valid for reading `2 * N` packs.
    unsafe fn load_packs(p: *const u32) -> Self;
    fn zero() -> Self;
    fn splat(x: u64) -> Self;
    fn xor(self, other: Self) -> Self;
    /// In each lane, the product of the words `IMM` picks, as `_mm_clmulepi64_si128` does.
    fn clmul<const IMM: i32>(self, other: Self) -> Self;
    /// In each lane, the high word moved to the low one.
    fn high(self) -> Self;
    /// In each lane, the low word of each.
    fn unpacklo(self, other: Self) -> Self;
    /// The sum of the lanes.
    fn sum(self) -> u128;
}

impl Vector for __m128i {
    const N: usize = 1;
    #[inline(always)]
    unsafe fn load(p: *const u64) -> Self {
        unsafe { _mm_loadu_si128(p.cast()) }
    }
    #[inline(always)]
    unsafe fn store(p: *mut u64, v: Self) {
        unsafe { _mm_storeu_si128(p.cast(), v) }
    }
    #[inline(always)]
    unsafe fn load_packs(p: *const u32) -> Self {
        unsafe { _mm_cvtepu32_epi64(_mm_loadl_epi64(p.cast())) }
    }
    #[inline(always)]
    fn zero() -> Self {
        unsafe { _mm_setzero_si128() }
    }
    #[inline(always)]
    fn splat(x: u64) -> Self {
        unsafe { _mm_set1_epi64x(x as i64) }
    }
    #[inline(always)]
    fn xor(self, other: Self) -> Self {
        unsafe { _mm_xor_si128(self, other) }
    }
    #[inline(always)]
    fn clmul<const IMM: i32>(self, other: Self) -> Self {
        unsafe { _mm_clmulepi64_si128::<IMM>(self, other) }
    }
    #[inline(always)]
    fn high(self) -> Self {
        unsafe { _mm_srli_si128::<8>(self) }
    }
    #[inline(always)]
    fn unpacklo(self, other: Self) -> Self {
        unsafe { _mm_unpacklo_epi64(self, other) }
    }
    #[inline(always)]
    fn sum(self) -> u128 {
        // SAFETY: both are 128 bits with no invalid patterns.
        unsafe { core::mem::transmute::<Self, u128>(self) }
    }
}

#[cfg(target_feature = "vpclmulqdq")]
impl Vector for __m256i {
    const N: usize = 2;
    #[inline(always)]
    unsafe fn load(p: *const u64) -> Self {
        unsafe { _mm256_loadu_si256(p.cast()) }
    }
    #[inline(always)]
    unsafe fn store(p: *mut u64, v: Self) {
        unsafe { _mm256_storeu_si256(p.cast(), v) }
    }
    #[inline(always)]
    unsafe fn load_packs(p: *const u32) -> Self {
        unsafe { _mm256_cvtepu32_epi64(_mm_loadu_si128(p.cast())) }
    }
    #[inline(always)]
    fn zero() -> Self {
        unsafe { _mm256_setzero_si256() }
    }
    #[inline(always)]
    fn splat(x: u64) -> Self {
        unsafe { _mm256_set1_epi64x(x as i64) }
    }
    #[inline(always)]
    fn xor(self, other: Self) -> Self {
        unsafe { _mm256_xor_si256(self, other) }
    }
    #[inline(always)]
    fn clmul<const IMM: i32>(self, other: Self) -> Self {
        unsafe { _mm256_clmulepi64_epi128::<IMM>(self, other) }
    }
    #[inline(always)]
    fn high(self) -> Self {
        unsafe { _mm256_bsrli_epi128::<8>(self) }
    }
    #[inline(always)]
    fn unpacklo(self, other: Self) -> Self {
        unsafe { _mm256_unpacklo_epi64(self, other) }
    }
    #[inline(always)]
    fn sum(self) -> u128 {
        unsafe { _mm256_castsi256_si128(self).sum() ^ _mm256_extracti128_si256::<1>(self).sum() }
    }
}
