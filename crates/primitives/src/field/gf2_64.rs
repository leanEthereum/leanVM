// CREDIT: https://github.com/binius-zk/binius64, Apache-2.0.
//! The base field `K = GF(2)[x] / (x^64 + x^4 + x^3 + x + 1)`, in which `x` has order `2^64 - 1`.
//!
//! A product is one carry-less 64x64 multiplication followed by a reduction.
//! The reduction folds the high word back with shifts and XORs ([`reduce`]), except in the scalar products
//! (`x86_64::mul`, `aarch64::mul_shift_tail`), which fold it with two more carry-less multiplications by `0x1B`
//! and so never leave the vector register.

use core::ops::{Add, AddAssign, Mul, MulAssign};
use serde::{Deserialize, Serialize};

/// Reduction constant of the base field: `x^64 = x^4 + x^3 + x + 1 = 0x1B`.
pub const R64: u64 = 0x1B;

/// A GF(2^64) element; bit i = coefficient of x^i.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(transparent)]
pub struct F64(pub u64);

/// `$v` squared `$n` times by `$square`: a macro, so that it is `const` when the square is.
macro_rules! squarings {
    ($square:expr, $v:expr, $n:expr) => {{
        let mut v = $v;
        let mut i = 0;
        while i < $n {
            v = $square(v);
            i += 1;
        }
        v
    }};
}

/// `$x^(2^64 - 2)` by Itoh-Tsujii, with the product `$mul` and the square `$square`: a macro, so that it is `const`
/// when they are.
///
/// With `t_k = x^(2^k - 1)`, the inverse is `t_63^2`.
/// Step `t_(a+b) = t_a^(2^b) * t_b` costs `b` squarings and one multiply.
/// The addition chain 1, 2, 3, 6, 12, 24, 48, 60, 63 spends 63 squarings and 8 multiplies.
macro_rules! itoh_tsujii {
    ($x:expr, $mul:expr, $square:expr) => {{
        // Each step reads t_k = x^(2^k - 1).
        let t1 = $x;
        let t2 = $mul(squarings!($square, t1, 1), t1);
        let t3 = $mul(squarings!($square, t2, 1), t1);
        let t6 = $mul(squarings!($square, t3, 3), t3);
        let t12 = $mul(squarings!($square, t6, 6), t6);
        let t24 = $mul(squarings!($square, t12, 12), t12);
        let t48 = $mul(squarings!($square, t24, 24), t24);
        let t60 = $mul(squarings!($square, t48, 12), t12);
        let t63 = $mul(squarings!($square, t60, 3), t3);
        // (x^(2^63 - 1))^2 = x^(2^64 - 2).
        squarings!($square, t63, 1)
    }};
}

impl F64 {
    /// Degree over GF(2), the number of binary coefficients in one element.
    pub const DEGREE: usize = 64;

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
    /// On aarch64 it is the product with itself instead: its PMULL folds stay in the vector register,
    /// where [`reduce`] would cross to integer registers and back.
    #[inline]
    pub fn square(self) -> Self {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            self * self
        }
        #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
        {
            Self(reduce(square_wide(self.0)))
        }
    }

    /// Multiplicative inverse `x^(2^64 - 2)`, mapping zero to zero.
    pub fn inv(self) -> Self {
        itoh_tsujii!(self, Mul::mul, Self::square)
    }

    /// The product, with no SIMD intrinsic or assembly: the verifier's (see [`crate::portable`]).
    #[inline]
    pub const fn mul_portable(self, rhs: Self) -> Self {
        Self(reduce(portable::clmul(self.0, rhs.0)))
    }

    /// The square, with no SIMD intrinsic or assembly.
    #[inline]
    pub const fn square_portable(self) -> Self {
        Self(reduce(portable::spread(self.0)))
    }

    /// The inverse, zero for zero, with no SIMD intrinsic or assembly.
    pub const fn inv_portable(self) -> Self {
        itoh_tsujii!(self, Self::mul_portable, Self::square_portable)
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
            crate::portable::kernel();
            // SAFETY: aes target feature is enabled at compile time.
            unsafe { aarch64::mul_shift_tail(self, rhs) }
        }
        #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
        {
            crate::portable::kernel();
            // SAFETY: pclmulqdq is enabled at compile time.
            unsafe { Self(x86_64::mul(self.0, rhs.0)) }
        }
        #[cfg(not(any(
            all(target_arch = "aarch64", target_feature = "aes"),
            all(target_arch = "x86_64", target_feature = "pclmulqdq")
        )))]
        {
            self.mul_portable(rhs)
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
#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(target_arch = "x86_64", target_feature = "pclmulqdq")
    )),
    expect(
        clippy::missing_const_for_fn,
        reason = "The SIMD implementations require runtime intrinsics."
    )
)]
#[inline]
pub fn mul_wide(a: u64, b: u64) -> u128 {
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    {
        crate::portable::kernel();
        // SAFETY: aes is enabled at compile time; the reinterpret is between 128-bit values.
        unsafe { core::mem::transmute::<core::arch::aarch64::uint64x2_t, u128>(aarch64::pmull(a, b)) }
    }
    #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
    {
        crate::portable::kernel();
        // SAFETY: pclmulqdq is enabled at compile time.
        unsafe { x86_64::clmul(a, b) }
    }
    #[cfg(not(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(target_arch = "x86_64", target_feature = "pclmulqdq")
    )))]
    {
        portable::clmul(a, b)
    }
}

/// The carry-less square of a 64-bit polynomial: bit `i` moves to bit `2i`.
#[inline]
pub fn square_wide(a: u64) -> u128 {
    #[cfg(all(target_arch = "x86_64", target_feature = "bmi2"))]
    {
        crate::portable::kernel();
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
    use crate::field::neon::xor3_u64;
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

    /// Reduce two 128-bit carry-less products into one lane pair: `[reduce(p0), reduce(p1)]`.
    ///
    /// Each product reduces in place, then one zip pairs the two low lanes:
    ///
    /// ```text
    ///     t = hi * 0x1B       one high-lane multiply
    ///     u = t.hi * 0x1B     one more: t.hi has at most 4 bits, so u fits in lane 0
    ///     e = p ^ t ^ u       one three-way XOR, lane 0 is the result
    /// ```
    ///
    /// Seven instructions for the pair.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`pmull`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn reduce_pair_pmull4(p0: uint64x2_t, p1: uint64x2_t) -> uint64x2_t {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let r = vdupq_n_u64(R64);
            let (t0, t1) = (pmull_hi(p0, r), pmull_hi(p1, r));
            let (u0, u1) = (pmull_hi(t0, r), pmull_hi(t1, r));
            let (mut e0, mut e1) = (xor3_u64(p0, t0, u0), xor3_u64(p1, t1, u1));
            // Why: only lane 0 of each sum survives the zip.
            // LLVM would gather the six low lanes with three inserts and XOR once: one instruction more.
            // An empty asm block hides the lanes from it, and emits nothing.
            core::arch::asm!(
                "/* {0:v} {1:v} */",
                inout(vreg) e0,
                inout(vreg) e1,
                options(pure, nomem, nostack, preserves_flags)
            );
            vzip1q_u64(e0, e1)
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

/// The x86-64 products.
#[cfg(target_arch = "x86_64")]
pub mod x86_64 {
    use super::R64;
    use core::arch::x86_64::*;

    /// One field product: the carry-less product, then two carry-less folds of its high word by `0x1B`.
    ///
    /// The whole product stays in one vector register. [`super::reduce`] would move both words to integer
    /// registers and back, and on Zen 4 that round trip and its shift chain cost more than the two folds.
    ///
    /// Credit: binius64 <https://github.com/binius-zk/binius64>
    /// (`crates/arith-bench/src/monbijou/clmul.rs::reduce`).
    ///
    /// # Safety
    ///
    /// Requires the `pclmulqdq` target feature.
    #[inline]
    #[target_feature(enable = "pclmulqdq")]
    pub unsafe fn mul(a: u64, b: u64) -> u64 {
        let r = _mm_cvtsi64_si128(R64 as i64);
        let p = _mm_clmulepi64_si128::<0x00>(_mm_cvtsi64_si128(a as i64), _mm_cvtsi64_si128(b as i64));
        // hi * 0x1B, at most 68 bits.
        let t = _mm_clmulepi64_si128::<0x01>(p, r);
        // Its spill past x^63, times 0x1B: at most 8 bits.
        let u = _mm_clmulepi64_si128::<0x01>(t, r);
        _mm_cvtsi128_si64(_mm_xor_si128(_mm_xor_si128(p, t), u)) as u64
    }

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

/// The portable products: integer code with no SIMD intrinsic or assembly, the same on every target.
pub mod portable {
    /// The bits `i < 128` with `i % 5 == class`.
    const fn class(class: u32) -> u128 {
        let (mut mask, mut bit) = (0, class);
        while bit < 128 {
            mask |= 1 << bit;
            bit += 5;
        }
        mask
    }

    const CLASSES: [u128; 5] = [class(0), class(1), class(2), class(3), class(4)];

    /// The 64x64 carry-less product, by integer products of operands with holes.
    ///
    /// Each operand splits into five parts, part `i` its bits at positions `i` modulo 5, at most 13 of them.
    /// A column of the integer product of two parts then sums at most 13 ones, so its carries stay in the four columns
    /// above it and never reach the next column of its class: that column's low bit is the XOR of its terms, the
    /// carry-less product's bit. The products of parts whose classes add to `k` modulo 5 give class `k`.
    #[inline]
    pub const fn clmul(a: u64, b: u64) -> u128 {
        let mut product = 0;
        let mut k = 0;
        while k < 5 {
            let mut sum = 0;
            let mut i = 0;
            while i < 5 {
                sum ^= (a as u128 & CLASSES[i]) * (b as u128 & CLASSES[(k + 5 - i) % 5]);
                i += 1;
            }
            product |= sum & CLASSES[k];
            k += 1;
        }
        product
    }

    /// The carry-less square: bit `i` moves to bit `2i`.
    pub const fn spread(a: u64) -> u128 {
        // A 32-bit half's bits onto the even bits of a word, by halving shifts.
        const fn half(x: u32) -> u64 {
            let mut x = x as u64;
            x = (x | x << 16) & 0x0000_FFFF_0000_FFFF;
            x = (x | x << 8) & 0x00FF_00FF_00FF_00FF;
            x = (x | x << 4) & 0x0F0F_0F0F_0F0F_0F0F;
            x = (x | x << 2) & 0x3333_3333_3333_3333;
            (x | x << 1) & 0x5555_5555_5555_5555
        }
        half(a as u32) as u128 | (half((a >> 32) as u32) as u128) << 64
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::Rng;
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    use core::arch::aarch64::vgetq_lane_u64;

    /// Independent Python reference vectors: (a, b, a * b).
    const VECTORS: [(u64, u64, u64); 3] = [
        (0x01090913877ed8ed, 0x66ab35ac2768468f, 0x50c4519dc383744a),
        (0xa7715ae18f12a3b5, 0x05743059f43fa4f5, 0xeb64cd9cd9cda6df),
        (0xbd3efb4705e79ddd, 0x3aff618604de4ae0, 0xc3d7a95fa9cb59bb),
    ];

    /// Operands that exercise the reduction's spill: the top bits set, all bits set, and the identities.
    const CORNERS: [u64; 6] = [0, 1, u64::MAX, 1 << 63, 0xF000_0000_0000_0000, R64];

    /// The carry-less product bit by bit, the reference every other is checked against.
    fn schoolbook(a: u64, b: u64) -> u128 {
        (0..64).filter(|i| a >> i & 1 == 1).fold(0, |p, i| p ^ (b as u128) << i)
    }

    /// Reference product: schoolbook multiply, then bit-by-bit long division by the modulus.
    fn reference_mul(a: u64, b: u64) -> u64 {
        let mut p = schoolbook(a, b);
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
            assert_eq!(F64(a).mul_portable(F64(b)), F64(c));
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
            // The dispatched and the portable products agree with the reference.
            assert_eq!((F64(a) * F64(b)).0, want);
            assert_eq!(F64(a).mul_portable(F64(b)).0, want);
            // The widening products are the carry-less product on every backend.
            assert_eq!(portable::clmul(a, b), schoolbook(a, b));
            assert_eq!(mul_wide(a, b), schoolbook(a, b));
            // The bit spreads are the carry-less square, and squaring is the self-product.
            assert_eq!(portable::spread(a), schoolbook(a, a));
            assert_eq!(square_wide(a), schoolbook(a, a));
            assert_eq!(F64(a).square(), F64(reference_mul(a, a)));
            assert_eq!(F64(a).square_portable(), F64(reference_mul(a, a)));
        }
    }

    /// Every NEON mul variant agrees with the reference.
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    #[test]
    fn neon_variants_match_software() {
        let mut rng = Rng::new(5);
        // Random pairs, then every pair of corners.
        let random = (0..10_000).map(|_| (rng.next_u64(), rng.next_u64()));
        let corners = CORNERS.iter().flat_map(|&a| CORNERS.iter().map(move |&b| (a, b)));
        for (a, b) in random.chain(corners) {
            // SAFETY: aes target feature is enabled at compile time.
            unsafe {
                assert_eq!(aarch64::mul_shift_tail(F64(a), F64(b)).0, reference_mul(a, b));
                // The pair reduction takes two wide products and returns both reduced, in lane order:
                //
                //     [a * b, b * b]  ->  lane 0 = a * b,  lane 1 = b * b
                let (p0, p1) = (aarch64::pmull(a, b), aarch64::pmull(b, b));
                let pair = aarch64::reduce_pair_pmull4(p0, p1);
                assert_eq!(vgetq_lane_u64::<0>(pair), reference_mul(a, b));
                assert_eq!(vgetq_lane_u64::<1>(pair), reference_mul(b, b));
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
            assert_eq!(a.inv_portable(), a.inv());
        }
        // Zero has no inverse and maps to zero by convention.
        assert_eq!(F64::ZERO.inv(), F64::ZERO);
        assert_eq!(F64::ZERO.inv_portable(), F64::ZERO);
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
