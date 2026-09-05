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
    use core::arch::aarch64::*;
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
#[inline]
pub const fn gf8_reduce(p: u16) -> u8 {
    let h: u16 = p >> 8;
    let t: u16 = (p & 0xff) ^ h ^ (h << 1) ^ (h << 3) ^ (h << 4);
    let h2: u16 = t >> 8;
    ((t & 0xff) ^ h2 ^ (h2 << 1) ^ (h2 << 3) ^ (h2 << 4)) as u8
}

// ---------------------------------------------------------------------------
// aarch64 NEON helpers: 16-lane GF(2^8) mul and reduce.
//
// These are the building blocks for flock's round-1 lane products.
//
// `vmull_p8` is a baseline NEON instruction (no aes feature needed), so the
// only cfg gate is `target_arch = "aarch64"`.
// ---------------------------------------------------------------------------

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

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(target_arch = "aarch64")]
    use crate::test_rng::Rng;

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
        use core::arch::aarch64::*;
        use core::mem::transmute;

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
            let result_vec = unsafe {
                let a_v = vld1q_u8(a_arr.as_ptr());
                let b_v = vld1q_u8(b_arr.as_ptr());
                neon::gf8_mul_vec16(a_v, b_v)
            };
            let result: [u8; 16] = unsafe { transmute(result_vec) };
            assert_eq!(result, expected, "a={:02x?}, b={:02x?}", a_arr, b_arr);
        }
    }
}
