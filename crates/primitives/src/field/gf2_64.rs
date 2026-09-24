// CREDIT: https://github.com/binius-zk/binius64, Apache-2.0.
//! The base field `K = GF(2)[x] / (x^64 + x^4 + x^3 + x + 1)`, in which `x` has order `2^64 - 1`.
//!
//! A product is one carry-less 64x64 multiplication followed by a reduction.
//! The reduction folds the high word back with shifts and XORs, off the carry-less multiplier.

use core::ops::{Add, AddAssign, Mul, MulAssign};

use serde::{Deserialize, Serialize};

/// Reduction constant of the base field: `x^64 = x^4 + x^3 + x + 1 = 0x1B`.
pub const R64: u64 = 0x1B;

/// A GF(2^64) element; bit i = coefficient of x^i.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(transparent)]
pub struct F64(pub u64);

impl F64 {
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);
    /// `x`, with `ord(x) = 2^64 - 1`.
    pub const G: Self = Self(2);

    #[inline]
    pub const fn is_zero(self) -> bool {
        self.0 == 0
    }

    /// Squaring, as a bit spread followed by one reduction.
    ///
    /// Cross terms vanish in characteristic 2, so the square moves bit `i` to bit `2i`.
    #[inline]
    pub fn square(self) -> Self {
        Self(reduce(square_wide(self.0)))
    }

    /// Multiplicative inverse `x^(2^64 - 2)`, mapping zero to zero.
    ///
    /// Itoh-Tsujii: with `t_k = x^(2^k - 1)`, the inverse is `t_63^2`.
    /// Step `t_(a+b) = t_a^(2^b) * t_b` costs `b` squarings and one multiply.
    /// The addition chain 1, 2, 3, 6, 12, 24, 48, 60, 63 spends 63 squarings and 8 multiplies.
    pub fn inv(self) -> Self {
        // Square `v` a total of `n` times.
        let sq = |mut v: Self, n: u32| {
            for _ in 0..n {
                v = v.square();
            }
            v
        };
        // Each step reads t_k = x^(2^k - 1).
        let t1 = self;
        let t2 = sq(t1, 1) * t1;
        let t3 = sq(t2, 1) * t1;
        let t6 = sq(t3, 3) * t3;
        let t12 = sq(t6, 6) * t6;
        let t24 = sq(t12, 12) * t12;
        let t48 = sq(t24, 24) * t24;
        let t60 = sq(t48, 12) * t12;
        let t63 = sq(t60, 3) * t3;
        // (x^(2^63 - 1))^2 = x^(2^64 - 2).
        sq(t63, 1)
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl Add for F64 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0)
    }
}

#[allow(clippy::suspicious_op_assign_impl)]
impl AddAssign for F64 {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.0 ^= rhs.0;
    }
}

impl Mul for F64 {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            // SAFETY: aes target feature is enabled at compile time.
            unsafe { aarch64::mul_shift_tail(self, rhs) }
        }
        #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
        {
            Self(reduce(mul_wide(self.0, rhs.0)))
        }
    }
}

impl MulAssign for F64 {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

/// The carry-less product of two 64-bit polynomials, as a 128-bit polynomial.
#[inline]
pub fn mul_wide(a: u64, b: u64) -> u128 {
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    {
        // SAFETY: aes is enabled at compile time; the reinterpret is between 128-bit values.
        unsafe { core::mem::transmute::<core::arch::aarch64::uint64x2_t, u128>(aarch64::pmull(a, b)) }
    }
    #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
    {
        // SAFETY: pclmulqdq is enabled at compile time.
        unsafe { x86_64::clmul(a, b) }
    }
    #[cfg(not(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(target_arch = "x86_64", target_feature = "pclmulqdq")
    )))]
    {
        software::clmul(a, b)
    }
}

/// The carry-less square of a 64-bit polynomial: bit `i` moves to bit `2i`.
#[inline]
pub fn square_wide(a: u64) -> u128 {
    #[cfg(all(target_arch = "x86_64", target_feature = "bmi2"))]
    {
        // SAFETY: bmi2 is enabled at compile time.
        unsafe { x86_64::spread(a) }
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "bmi2")))]
    {
        mul_wide(a, a)
    }
}

/// Reduce a 128-bit carry-less product modulo `x^64 + x^4 + x^3 + x + 1`.
///
/// Write the product as `lo + hi * x^64` and substitute `x^64 = x^4 + x^3 + x + 1`:
///
/// ```text
///     hi * x^64  =  hi ^ hi<<1 ^ hi<<3 ^ hi<<4        (a 68-bit value)
///     spill      =  hi>>63 ^ hi>>61 ^ hi>>60          (its 4 bits past x^63)
///     spill * x^64 fits in 8 bits, so a second fold is exact and final.
///
///     result = lo ^ f(hi ^ spill),   f(v) = v ^ v<<1 ^ v<<3 ^ v<<4  (mod 2^64)
/// ```
///
/// The two folds merge into one because the truncated map `f` is GF(2)-linear.
#[inline]
pub const fn reduce(p: u128) -> u64 {
    // Split the product into its low and high words.
    let (lo, hi) = (p as u64, (p >> 64) as u64);
    // The bits of `hi * 0x1B` shifted past x^63, which wrap around as `spill * 0x1B`.
    let spill = (hi >> 63) ^ (hi >> 61) ^ (hi >> 60);
    // Fold `hi` and `spill` together: both are multiplied by the same constant.
    let v = hi ^ spill;
    lo ^ v ^ (v << 1) ^ (v << 3) ^ (v << 4)
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
pub mod aarch64 {
    use super::{F64, R64};
    use core::arch::aarch64::*;
    use core::mem::transmute;

    /// 64x64 carry-less product as a 128-bit NEON vector.
    ///
    /// # Safety
    /// Requires the `aes` target feature (compiles to PMULL); only call where
    /// `aes` is statically enabled or has been runtime-detected.
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn pmull(a: u64, b: u64) -> uint64x2_t {
        // SAFETY: u128 and uint64x2_t are both 128-bit values.
        unsafe { transmute::<u128, uint64x2_t>(vmull_p64(a, b)) }
    }

    /// Carry-less product of the two *high* lanes: PMULL2 on the register
    /// pair, no lane extraction (the lane-crossing-free way to fold a
    /// product's high half).
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`pmull`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn pmull_hi(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
        // SAFETY: bit-level reinterprets between 128-bit vector types.
        unsafe {
            transmute::<u128, uint64x2_t>(vmull_high_p64(
                transmute::<uint64x2_t, poly64x2_t>(a),
                transmute::<uint64x2_t, poly64x2_t>(b),
            ))
        }
    }

    /// Reduce two 128-bit carry-less products into GF(2^64) as a lane pair:
    /// returns `{reduce(p0), reduce(p1)}`. One PMULL-by-0x1B per product folds
    /// the high half, and a second PMULL folds that fold's ≤4-bit second-order
    /// overflow (4 PMULL total, minimal non-PMULL op count). Fastest pair
    /// reduction in memory-resident loops (the NTT butterfly shape) on
    /// M-series, where PMULL throughput is plentiful.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`pmull`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn reduce_pair_pmull4(p0: uint64x2_t, p1: uint64x2_t) -> uint64x2_t {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let r = vdupq_n_u64(R64);
            let t0 = pmull_hi(p0, r);
            let t1 = pmull_hi(p1, r);
            // clmul(t.hi, 0x1B) fits in 8 bits (high lane 0): the exact fold
            // of the ≤4-bit overflow, ready to XOR into lane 0.
            let u0 = pmull_hi(t0, r);
            let u1 = pmull_hi(t1, r);
            vtrn1q_u64(veorq_u64(veorq_u64(p0, t0), u0), veorq_u64(veorq_u64(p1, t1), u1))
        }
    }

    /// The default `Mul` kernel on aarch64. 3-PMULL multiply: product, then two
    /// PMULL-by-0x1B folds, the second taking the first's ≤4-bit overflow
    /// exactly (`ov·0x1B` fits in 8 bits). The shift-XOR tail this replaced was
    /// chosen on the premise that the vector pipes were PMULL-saturated and the
    /// scalar ports free; PMULL retires at about the rate `eor` does here, so
    /// the extra product costs less than the lane extraction it removes.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`pmull`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_shift_tail(a: F64, b: F64) -> F64 {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let r = vdupq_n_u64(R64);
            let p = pmull(a.0, b.0);
            let t = pmull_hi(p, r);
            let u = pmull_hi(t, r);
            F64(vgetq_lane_u64::<0>(veorq_u64(veorq_u64(p, t), u)))
        }
    }
}

/// The x86-64 widening products.
///
/// Only the carry-less product runs on the vector unit.
/// The carry-less multiplier is the scarce execution unit, while shifts and XORs issue on several ports.
/// The reduction therefore stays on the integer side.
#[cfg(target_arch = "x86_64")]
pub mod x86_64 {
    use core::arch::x86_64::*;

    /// 64x64 carry-less product.
    ///
    /// # Safety
    ///
    /// Requires the `pclmulqdq` target feature.
    #[inline]
    #[target_feature(enable = "pclmulqdq")]
    pub unsafe fn clmul(a: u64, b: u64) -> u128 {
        // Move both operands into the low qword of a vector register.
        let (a, b) = (_mm_cvtsi64_si128(a as i64), _mm_cvtsi64_si128(b as i64));
        // SAFETY: both types are 128 bits wide with no invalid bit patterns.
        unsafe { core::mem::transmute::<__m128i, u128>(_mm_clmulepi64_si128::<0x00>(a, b)) }
    }

    /// Carry-less square by bit deposit: `pdep` spreads each 32-bit half onto the even bits of one word.
    ///
    /// Zen 1 and Zen 2 microcode `pdep`, so there this is slower than a carry-less multiply.
    ///
    /// # Safety
    ///
    /// Requires the `bmi2` target feature.
    #[inline]
    #[target_feature(enable = "bmi2")]
    pub unsafe fn spread(a: u64) -> u128 {
        // Bits 0, 2, 4, ...: where a square puts the input bits.
        const EVEN: u64 = 0x5555_5555_5555_5555;
        // Low half of `a` into the low word, high half into the high word.
        let lo = _pdep_u64(a, EVEN);
        let hi = _pdep_u64(a >> 32, EVEN);
        lo as u128 | (hi as u128) << 64
    }
}

pub mod software {
    /// Portable 64x64 carry-less product, used by fallback paths and as the reference.
    pub const fn clmul(a: u64, b: u64) -> u128 {
        let mut acc = 0u128;
        let mut i = 0;
        // Schoolbook: XOR in `b * x^i` for every set bit `i` of `a`.
        while i < 64 {
            if (a >> i) & 1 != 0 {
                acc ^= (b as u128) << i;
            }
            i += 1;
        }
        acc
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_rng::Rng;

    /// Independent Python reference vectors: (a, b, a * b).
    const VECTORS: [(u64, u64, u64); 3] = [
        (0x01090913877ed8ed, 0x66ab35ac2768468f, 0x50c4519dc383744a),
        (0xa7715ae18f12a3b5, 0x05743059f43fa4f5, 0xeb64cd9cd9cda6df),
        (0xbd3efb4705e79ddd, 0x3aff618604de4ae0, 0xc3d7a95fa9cb59bb),
    ];

    /// Operands that exercise the reduction's spill: the top bits set, all bits set, and the identities.
    const CORNERS: [u64; 6] = [0, 1, u64::MAX, 1 << 63, 0xF000_0000_0000_0000, R64];

    /// Reference product: schoolbook multiply, then bit-by-bit long division by the modulus.
    fn reference_mul(a: u64, b: u64) -> u64 {
        let mut p = software::clmul(a, b);
        // Clear bits 127..64 from the top, each with one shifted copy of x^64 + 0x1B.
        for bit in (64..128).rev() {
            if (p >> bit) & 1 != 0 {
                p ^= ((1u128 << 64) | R64 as u128) << (bit - 64);
            }
        }
        p as u64
    }

    #[test]
    fn python_vectors() {
        for (a, b, c) in VECTORS {
            assert_eq!(F64(a) * F64(b), F64(c));
            assert_eq!(reference_mul(a, b), c);
        }
    }

    #[test]
    fn mul_and_square_match_the_reference() {
        let mut rng = Rng::new(1);
        // Random operands, then every pair of corners.
        let random = (0..10_000).map(|_| (rng.next_u64(), rng.next_u64()));
        let corners = CORNERS.iter().flat_map(|&a| CORNERS.iter().map(move |&b| (a, b)));
        for (a, b) in random.chain(corners) {
            let want = reference_mul(a, b);
            // The dispatched product and the portable composition agree with the reference.
            assert_eq!((F64(a) * F64(b)).0, want);
            assert_eq!(reduce(software::clmul(a, b)), want);
            // The widening product is the carry-less product on every backend.
            assert_eq!(mul_wide(a, b), software::clmul(a, b));
            // The bit spread is the carry-less square, and squaring is the self-product.
            assert_eq!(square_wide(a), software::clmul(a, a));
            assert_eq!(F64(a).square(), F64(reference_mul(a, a)));
        }
    }

    /// Every NEON mul variant agrees with the software reference.
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    #[test]
    fn neon_variants_match_software() {
        let mut rng = Rng::new(5);
        for _ in 0..10_000 {
            let (a, b) = (rng.next_u64(), rng.next_u64());
            // SAFETY: aes target feature is enabled at compile time.
            unsafe {
                assert_eq!(aarch64::mul_shift_tail(F64(a), F64(b)).0, reference_mul(a, b));
            }
        }
    }

    #[test]
    fn inverses() {
        let mut rng = Rng::new(2);
        // Random elements, then the nonzero corners.
        let elements = (0..200).map(|_| rng.next_u64()).chain(CORNERS.into_iter().skip(1));
        for a in elements.map(F64) {
            assert_eq!(a * a.inv(), F64::ONE);
        }
        // Zero has no inverse and maps to zero by convention.
        assert_eq!(F64::ZERO.inv(), F64::ZERO);
    }

    /// x is primitive: x^((2^64−1)/q) ≠ 1 for every prime q | 2^64 − 1.
    #[test]
    fn x_is_primitive() {
        fn pow(mut base: F64, mut e: u128) -> F64 {
            let mut r = F64::ONE;
            while e > 0 {
                if e & 1 == 1 {
                    r *= base;
                }
                base = base.square();
                e >>= 1;
            }
            r
        }
        let n: u128 = (1 << 64) - 1;
        for q in [3u128, 5, 17, 257, 641, 65537, 6700417] {
            assert_ne!(pow(F64::G, n / q), F64::ONE, "x^((2^64-1)/{q}) == 1");
        }
    }
}
