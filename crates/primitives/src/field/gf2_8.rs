// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// CREDIT: https://github.com/binius-zk/binius64 (`packed_aes_16x8b_multiply`), Apache-2.0.
// Copyright 2025 The Binius Developers
// Copyright 2025 Irreducible, Inc.
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// The NEON 16-wide multiplier (`gf8_mul_vec16` / `gf8_reduce_vec16`) is a
// port of `packed_aes_16x8b_multiply` from binius64
// (https://github.com/binius-zk/binius64,
// `crates/field/src/arch/aarch64/simd_arithmetic.rs`).

//! `GF(2)[x]/(x^8 + x^4 + x^3 + x + 1)`.
//!
//! Reduction: x^8 ≡ x^4 + x^3 + x + 1, so the upper byte h folds back as
//!   h ^ (h<<1) ^ (h<<3) ^ (h<<4).

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
use core::arch::aarch64::*;
use core::ops::{Add, AddAssign, Mul, MulAssign};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct F8(pub u8);

impl F8 {
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);

    /// Multiplicative inverse via Fermat: x^254 = x^{-1} in F_{2^8}.
    /// Exponent bit pattern 0xFE = 0b11111110: 7 squarings + 6 multiplies.
    pub fn inv(self) -> Self {
        let mut result = Self::ONE;
        let mut sq = self;
        for i in 0..8 {
            if (0xFEu8 >> i) & 1 != 0 {
                result *= sq;
            }
            sq *= sq;
        }
        result
    }
}

// In GF(2⁸), addition is bitwise XOR by definition. The `^` is correct, not a
// typo for `+` (which is what these Clippy lints guard against).
#[allow(clippy::suspicious_arithmetic_impl)]
impl Add for F8 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0)
    }
}

#[allow(clippy::suspicious_op_assign_impl)]
impl AddAssign for F8 {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.0 ^= rhs.0;
    }
}

impl Mul for F8 {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        Self(gf8_reduce(clmul8(self.0, rhs.0)))
    }
}

impl MulAssign for F8 {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

/// Carry-less product of two bytes; result fits in 15 bits.
#[cfg_attr(
    not(all(target_arch = "aarch64", target_feature = "aes")),
    expect(
        clippy::missing_const_for_fn,
        reason = "The NEON implementation requires runtime intrinsics."
    )
)]
#[inline]
fn clmul8(a: u8, b: u8) -> u16 {
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    {
        // SAFETY: `aes` target feature is enabled at compile time.
        unsafe { clmul8_neon(a, b) }
    }
    #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
    {
        clmul8_software(a, b)
    }
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[target_feature(enable = "aes")]
#[inline]
unsafe fn clmul8_neon(a: u8, b: u8) -> u16 {
    let va = vdup_n_p8(a);
    let vb = vdup_n_p8(b);
    let prod = vmull_p8(va, vb);
    vgetq_lane_u16::<0>(vreinterpretq_u16_p16(prod))
}

/// Software fallback / test oracle. Used when `aes` is off, and as the
/// cross-check oracle inside the `software_matches_neon` unit test.
#[allow(dead_code)]
#[inline]
const fn clmul8_software(a: u8, b: u8) -> u16 {
    let b16 = b as u16;
    let mut acc: u16 = 0;
    let mut i = 0;
    while i < 8 {
        if (a >> i) & 1 != 0 {
            acc ^= b16 << i;
        }
        i += 1;
    }
    acc
}

/// Reduce a polynomial of degree ≤ 14 modulo x^8 + x^4 + x^3 + x + 1.
/// Two-step fold: first turns 15-bit input into ≤12-bit, second into ≤8-bit.
///
/// Exposed `pub` so flock's URM shift_reduce inner kernel can reuse it.
#[inline]
pub const fn gf8_reduce(p: u16) -> u8 {
    let h: u16 = p >> 8;
    let t: u16 = (p & 0xff) ^ h ^ (h << 1) ^ (h << 3) ^ (h << 4);
    let h2: u16 = t >> 8;
    ((t & 0xff) ^ h2 ^ (h2 << 1) ^ (h2 << 3) ^ (h2 << 4)) as u8
}

// aarch64 NEON helpers: 16-lane GF(2^8) mul and reduce.
//
// These are the building blocks for the round-1 URM shift_reduce inner kernel.
//
// `vmull_p8` is a baseline NEON instruction (no aes feature needed), so the
// only cfg gate is `target_arch = "aarch64"`.

#[cfg(target_arch = "aarch64")]
pub mod neon {
    use core::arch::aarch64::*;
    use core::mem::transmute;

    /// Reduce 16 polynomial products (in interleaved layout `[lo0,hi0, lo1,hi1, ...]`,
    /// passed as `(c0, c1)`) modulo `x^8 + x^4 + x^3 + x + 1`, returning 16 reduced
    /// GF(2^8) values.
    ///
    /// Two-stage reduction:
    ///   Stage 1: ch · QPLUS_RSH1 then ·2 (corrects for /x in QPLUS_RSH1)
    ///   Stage 2: high bytes of stage-1 · QSTAR; take low bytes only.
    ///
    /// Constants:
    ///   QPLUS_RSH1 = (x^8+x^4+x^3+x)/x = 0x8d
    ///   QSTAR      = x^4+x^3+x+1       = 0x1b
    ///
    /// # Safety
    /// Uses `core::arch::aarch64` NEON intrinsics; only call on `aarch64`.
    #[inline]
    pub unsafe fn gf8_reduce_vec16(c0: uint8x16_t, c1: uint8x16_t) -> uint8x16_t {
        // SAFETY: NEON, PMULL's `vmull_p8` included, is part of the aarch64 baseline, and nothing here touches
        // memory; the transmutes are between same-size vector and integer types.
        unsafe {
            let q_plus_rsh1: poly8x8_t = transmute::<u64, poly8x8_t>(0x8d8d8d8d8d8d8d8d_u64);
            let q_star: poly8x8_t = transmute::<u64, poly8x8_t>(0x1b1b1b1b1b1b1b1b_u64);

            let cl = vuzp1q_u8(c0, c1); // low bytes of all 16 products
            let ch = vuzp2q_u8(c0, c1); // high bytes of all 16 products

            // Stage 1.
            let t0 = vreinterpretq_u8_u16(vshlq_n_u16::<1>(vreinterpretq_u16_p16(vmull_p8(
                transmute::<uint8x8_t, poly8x8_t>(vget_low_u8(ch)),
                q_plus_rsh1,
            ))));
            let t1 = vreinterpretq_u8_u16(vshlq_n_u16::<1>(vreinterpretq_u16_p16(vmull_p8(
                transmute::<uint8x8_t, poly8x8_t>(vget_high_u8(ch)),
                q_plus_rsh1,
            ))));

            // Stage 2.
            let tmp_hi = vuzp2q_u8(t0, t1);
            let r0 = vreinterpretq_u8_u16(vreinterpretq_u16_p16(vmull_p8(
                transmute::<uint8x8_t, poly8x8_t>(vget_low_u8(tmp_hi)),
                q_star,
            )));
            let r1 = vreinterpretq_u8_u16(vreinterpretq_u16_p16(vmull_p8(
                transmute::<uint8x8_t, poly8x8_t>(vget_high_u8(tmp_hi)),
                q_star,
            )));

            veorq_u8(cl, vuzp1q_u8(r0, r1))
        }
    }

    /// Element-wise multiply 16 pairs of GF(2^8) values (binius64 13-op NEON kernel).
    ///
    /// # Safety
    /// Uses `core::arch::aarch64` NEON intrinsics (PMULL); only call on `aarch64`.
    #[inline]
    pub unsafe fn gf8_mul_vec16(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        // SAFETY: as in the reduction above: baseline NEON on registers only.
        unsafe {
            let c0 = vreinterpretq_u8_u16(vreinterpretq_u16_p16(vmull_p8(
                transmute::<uint8x8_t, poly8x8_t>(vget_low_u8(a)),
                transmute::<uint8x8_t, poly8x8_t>(vget_low_u8(b)),
            )));
            let c1 = vreinterpretq_u8_u16(vreinterpretq_u16_p16(vmull_p8(
                transmute::<uint8x8_t, poly8x8_t>(vget_high_u8(a)),
                transmute::<uint8x8_t, poly8x8_t>(vget_high_u8(b)),
            )));
            gf8_reduce_vec16(c0, c1)
        }
    }
}

/// The AVX2 counterpart of the NEON helpers, for x86 without GFNI (whose `gf2p8mulb` is the field product itself).
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
pub mod avx2 {
    use core::arch::x86_64::*;

    /// Element-wise product of 32 pairs of GF(2^8) values, a bit of `b` at a time from the top (Horner).
    ///
    /// Each step doubles the running product (`xtime`, folding `x^8` back as `0x1B`) and adds `a` where the bit is set.
    ///
    /// # Safety
    /// Requires the `avx2` target feature.
    #[inline]
    #[target_feature(enable = "avx2")]
    pub unsafe fn gf8_mul_vec32(a: __m256i, b: __m256i) -> __m256i {
        let zero = _mm256_setzero_si256();
        let poly = _mm256_set1_epi8(0x1B);
        // A byte's top bit is its sign, so a signed compare against zero spreads it over the byte.
        let top = |x: __m256i| _mm256_cmpgt_epi8(zero, x);
        let (mut r, mut b) = (_mm256_and_si256(a, top(b)), _mm256_add_epi8(b, b));
        for _ in 1..8 {
            let doubled = _mm256_xor_si256(_mm256_add_epi8(r, r), _mm256_and_si256(poly, top(r)));
            r = _mm256_xor_si256(doubled, _mm256_and_si256(a, top(b)));
            b = _mm256_add_epi8(b, b);
        }
        r
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(target_arch = "aarch64")]
    use crate::test_util::Rng;
    #[cfg(target_arch = "aarch64")]
    use core::arch::aarch64::uint8x16_t;
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    use core::arch::x86_64::*;
    #[cfg(target_arch = "aarch64")]
    use core::mem::transmute;

    #[test]
    fn inv_roundtrip() {
        for v in 1u8..=255 {
            let a = F8(v);
            assert_eq!(a * a.inv(), F8::ONE, "v={}", v);
        }
    }

    /// Only meaningful where `clmul8` dispatches to PMULL; elsewhere it *is*
    /// `clmul8_software`.
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    #[test]
    fn software_matches_neon() {
        let mut rng = Rng::new(0xDEADBEEF);
        for _ in 0..1024 {
            let a = rng.next_u8();
            let b = rng.next_u8();
            assert_eq!(clmul8(a, b), clmul8_software(a, b));
        }
    }

    #[test]
    fn fips_197_test_vectors() {
        // FIPS 197 § 4.2 (AES specification) publishes these products
        // for the GF(2^8) multiplication used by AES.
        assert_eq!(F8(0x57) * F8(0x13), F8(0xfe), "FIPS-197: 57·13");
        assert_eq!(F8(0x57) * F8(0x83), F8(0xc1), "FIPS-197: 57·83");
        // xtime: a · 0x02 (used by MixColumns), exhaustively cross-check
        // against the spec'd formula: xtime(a) = (a << 1) ^ (0x1B if a high bit).
        for a in 0u8..=255 {
            let expected = if a & 0x80 != 0 { (a << 1) ^ 0x1b } else { a << 1 };
            assert_eq!((F8(a) * F8(0x02)).0, expected, "xtime mismatch at a=0x{a:02x}");
        }
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn neon_gf8_mul_vec16_matches_scalar() {
        let mut rng = Rng::new(0xBADC0FFEE);
        for _ in 0..256 {
            let mut a_arr = [0u8; 16];
            let mut b_arr = [0u8; 16];
            for i in 0..16 {
                a_arr[i] = rng.next_u8();
                b_arr[i] = rng.next_u8();
            }
            // Scalar reference: lane-wise F8 mul.
            let mut expected = [0u8; 16];
            for i in 0..16 {
                expected[i] = (F8(a_arr[i]) * F8(b_arr[i])).0;
            }
            // NEON result.
            // SAFETY: baseline NEON; each load reads one 16-byte array.
            let result_vec = unsafe {
                let a_v = vld1q_u8(a_arr.as_ptr());
                let b_v = vld1q_u8(b_arr.as_ptr());
                neon::gf8_mul_vec16(a_v, b_v)
            };
            // SAFETY: a `uint8x16_t` is 16 plain bytes.
            let result: [u8; 16] = unsafe { transmute(result_vec) };
            assert_eq!(result, expected, "a={:02x?}, b={:02x?}", a_arr, b_arr);
        }
    }

    /// The 16-lane reduction alone, on every 16-bit polynomial: callers reduce sums of shifted
    /// products, which are not all products of two bytes.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn neon_gf8_reduce_vec16_matches_scalar() {
        for first in (0..=u16::MAX).step_by(16) {
            let p: [u16; 16] = std::array::from_fn(|i| first + i as u16);
            let (lo, hi): ([u16; 8], [u16; 8]) = (p[..8].try_into().unwrap(), p[8..].try_into().unwrap());
            // SAFETY: baseline NEON on registers; eight `u16`s are sixteen plain bytes, each low byte first,
            // which is the interleaved layout the reduction reads.
            let got: [u8; 16] = unsafe {
                transmute(neon::gf8_reduce_vec16(
                    transmute::<[u16; 8], uint8x16_t>(lo),
                    transmute::<[u16; 8], uint8x16_t>(hi),
                ))
            };
            assert_eq!(got, p.map(gf8_reduce), "first={first:#06x}");
        }
    }

    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    #[test]
    fn avx2_gf8_mul_vec32_matches_scalar() {
        // Every pair: `a` sweeps 0..256 for each `b`, 32 lanes at a time.
        for b in 0u8..=255 {
            for a0 in (0..256).step_by(32) {
                let a: [u8; 32] = std::array::from_fn(|i| (a0 + i) as u8);
                let expected: [u8; 32] = std::array::from_fn(|i| (F8(a[i]) * F8(b)).0);
                let mut got = [0u8; 32];
                // SAFETY: the crate is built with AVX2; each load and store is one 32-byte array.
                unsafe {
                    let r = avx2::gf8_mul_vec32(_mm256_loadu_si256(a.as_ptr().cast()), _mm256_set1_epi8(b as i8));
                    _mm256_storeu_si256(got.as_mut_ptr().cast(), r);
                }
                assert_eq!(got, expected, "b={b:02x}");
            }
        }
    }
}
