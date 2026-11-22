//! Carry-less products at the width of the multiplier: a register of 128-bit lanes, one with
//! PCLMULQDQ or NEON PMULL alone, two with VPCLMULQDQ and four with AVX-512 as well. Every
//! operation is lane by lane, so a kernel written once serves every width and architecture.
//!
//! The intrinsics are safe to call: the module is compiled only where its features are.

#[cfg(target_arch = "aarch64")]
use core::arch::aarch64::*;
#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;

cfg_select! {
    all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq") => {
        pub type V = __m512i;
    }
    all(target_arch = "x86_64", target_feature = "vpclmulqdq") => {
        pub type V = __m256i;
    }
    target_arch = "x86_64" => {
        pub type V = __m128i;
    }
    all(target_arch = "aarch64", target_feature = "aes") => {
        pub type V = uint64x2_t;
    }
}

pub trait Vector: Copy {
    /// 128-bit lanes.
    const N: usize;
    /// # Safety
    /// `p` is valid for reading `2 * N` words.
    unsafe fn load(p: *const u64) -> Self;
    /// # Safety
    /// `p` is valid for writing `2 * N` words.
    #[cfg_attr(target_arch = "aarch64", allow(dead_code))]
    unsafe fn store(p: *mut u64, v: Self);
    /// `2 * N` packs, a word each.
    ///
    /// # Safety
    /// `p` is valid for reading `2 * N` packs.
    unsafe fn load_packs(p: *const u32) -> Self;
    fn zero() -> Self;
    #[cfg_attr(target_arch = "aarch64", allow(dead_code))]
    fn splat(x: u64) -> Self;
    fn xor(self, other: Self) -> Self;
    /// Three-way XOR: `self ^ b ^ c`.
    #[cfg_attr(all(target_arch = "x86_64", target_feature = "gfni"), allow(dead_code))]
    #[inline(always)]
    fn xor3(self, b: Self, c: Self) -> Self {
        self.xor(b).xor(c)
    }
    /// In each lane, the product of the words `IMM` picks, as `_mm_clmulepi64_si128` does.
    fn clmul<const IMM: i32>(self, other: Self) -> Self;
    /// In each lane, the high word moved to the low one.
    #[cfg_attr(target_arch = "aarch64", allow(dead_code))]
    fn high(self) -> Self;
    /// In each lane, the low word of each.
    fn unpacklo(self, other: Self) -> Self;
    /// In each lane, the high word of each.
    #[cfg_attr(all(target_arch = "x86_64", target_feature = "gfni"), allow(dead_code))]
    fn unpackhi(self, other: Self) -> Self;
    /// The sum of the lanes.
    fn sum(self) -> u128;
}

#[cfg(target_arch = "x86_64")]
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
    fn unpackhi(self, other: Self) -> Self {
        unsafe { _mm_unpackhi_epi64(self, other) }
    }
    #[inline(always)]
    fn sum(self) -> u128 {
        // SAFETY: both are 128 bits with no invalid patterns.
        unsafe { core::mem::transmute::<Self, u128>(self) }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq"))]
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
    fn unpackhi(self, other: Self) -> Self {
        unsafe { _mm256_unpackhi_epi64(self, other) }
    }
    #[inline(always)]
    fn sum(self) -> u128 {
        unsafe { _mm256_castsi256_si128(self).sum() ^ _mm256_extracti128_si256::<1>(self).sum() }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
impl Vector for __m512i {
    const N: usize = 4;
    #[inline(always)]
    unsafe fn load(p: *const u64) -> Self {
        unsafe { _mm512_loadu_si512(p.cast()) }
    }
    #[inline(always)]
    unsafe fn store(p: *mut u64, v: Self) {
        unsafe { _mm512_storeu_si512(p.cast(), v) }
    }
    #[inline(always)]
    unsafe fn load_packs(p: *const u32) -> Self {
        unsafe { _mm512_cvtepu32_epi64(_mm256_loadu_si256(p.cast())) }
    }
    #[inline(always)]
    fn zero() -> Self {
        unsafe { _mm512_setzero_si512() }
    }
    #[inline(always)]
    fn splat(x: u64) -> Self {
        unsafe { _mm512_set1_epi64(x as i64) }
    }
    #[inline(always)]
    fn xor(self, other: Self) -> Self {
        unsafe { _mm512_xor_si512(self, other) }
    }
    #[inline(always)]
    fn xor3(self, b: Self, c: Self) -> Self {
        unsafe { _mm512_ternarylogic_epi64::<0x96>(self, b, c) }
    }
    #[inline(always)]
    fn clmul<const IMM: i32>(self, other: Self) -> Self {
        unsafe { _mm512_clmulepi64_epi128::<IMM>(self, other) }
    }
    #[inline(always)]
    fn high(self) -> Self {
        unsafe { _mm512_bsrli_epi128::<8>(self) }
    }
    #[inline(always)]
    fn unpacklo(self, other: Self) -> Self {
        unsafe { _mm512_unpacklo_epi64(self, other) }
    }
    #[inline(always)]
    fn unpackhi(self, other: Self) -> Self {
        unsafe { _mm512_unpackhi_epi64(self, other) }
    }
    #[inline(always)]
    fn sum(self) -> u128 {
        unsafe { _mm512_castsi512_si256(self).sum() ^ _mm512_extracti64x4_epi64::<1>(self).sum() }
    }
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
impl Vector for uint64x2_t {
    const N: usize = 1;
    #[inline(always)]
    unsafe fn load(p: *const u64) -> Self {
        unsafe { vld1q_u64(p) }
    }
    #[inline(always)]
    unsafe fn store(p: *mut u64, v: Self) {
        unsafe { vst1q_u64(p, v) }
    }
    #[inline(always)]
    unsafe fn load_packs(p: *const u32) -> Self {
        unsafe { vmovl_u32(vld1_u32(p)) }
    }
    #[inline(always)]
    fn zero() -> Self {
        unsafe { vdupq_n_u64(0) }
    }
    #[inline(always)]
    fn splat(x: u64) -> Self {
        unsafe { vdupq_n_u64(x) }
    }
    #[inline(always)]
    fn xor(self, other: Self) -> Self {
        unsafe { veorq_u64(self, other) }
    }
    #[inline(always)]
    fn xor3(self, b: Self, c: Self) -> Self {
        #[cfg(target_feature = "sha3")]
        // SAFETY: sha3 is enabled at compile time.
        unsafe {
            veor3q_u64(self, b, c)
        }
        #[cfg(not(target_feature = "sha3"))]
        unsafe {
            veorq_u64(veorq_u64(self, b), c)
        }
    }
    #[inline(always)]
    fn clmul<const IMM: i32>(self, other: Self) -> Self {
        use primitives::field::gf2_64::aarch64::{pmull_hi_asm, pmull_lo_asm};
        const { assert!(IMM == 0x00 || IMM == 0x11, "NEON clmul supports 0x00 and 0x11 only") };
        // SAFETY: aes is enabled at compile time (module cfg).
        unsafe {
            if IMM == 0x00 {
                pmull_lo_asm(self, other)
            } else {
                pmull_hi_asm(self, other)
            }
        }
    }
    #[inline(always)]
    fn high(self) -> Self {
        unsafe { vextq_u64::<1>(self, vdupq_n_u64(0)) }
    }
    #[inline(always)]
    fn unpacklo(self, other: Self) -> Self {
        unsafe { vzip1q_u64(self, other) }
    }
    #[inline(always)]
    fn unpackhi(self, other: Self) -> Self {
        unsafe { vzip2q_u64(self, other) }
    }
    #[inline(always)]
    fn sum(self) -> u128 {
        // SAFETY: both are 128 bits with no invalid patterns.
        unsafe { core::mem::transmute::<Self, u128>(self) }
    }
}
