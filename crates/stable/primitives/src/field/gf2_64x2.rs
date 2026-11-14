//! The extension field `F128 = K[y] / (y^2 + x*y + 1)` over the base field `K = GF(2^64)`.
//!
//! An element is `c0 + c1*y`, each coefficient a base-field element. The modulus is irreducible
//! because `Tr_K(1/x^2) = Tr_K(1/x) = 1`. A product runs in three stages:
//!
//! ```text
//!     products    carry-less 64x64 products    ->  3 coefficients of y^0..y^2, 128 bits each
//!     y-fold      y^2 = x*y + 1                ->  2 coefficients of y^0..y^1, 128 bits each
//!     reduce      x^64 = x^4 + x^3 + x + 1     ->  2 coefficients of y^0..y^1,  64 bits each
//! ```
//!
//! The y-fold multiplies the `y^2` coefficient by `x`, a one-bit shift that stays within 128 bits:
//! a 64x64 product has degree at most 126.
//!
//! Both folds are GF(2)-linear, so they commute with XOR.
//! A sum of products therefore accumulates after the y-fold and reduces once.

use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, BitXor, BitXorAssign, Mul, MulAssign};

use super::gf2_64::{F64, mul_wide, reduce};
use super::mul_by_g;

/// An element `c0 + c1*y`; bit `i` of each coefficient is its coefficient of `x^i`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[repr(C)]
pub struct F128 {
    /// The coefficient of `y^0`.
    pub c0: u64,
    /// The coefficient of `y^1`.
    pub c1: u64,
}

impl F128 {
    pub const ZERO: Self = Self { c0: 0, c1: 0 };
    pub const ONE: Self = Self { c0: 1, c1: 0 };
    /// The element `y` (root of y^2 + x*y + 1 over the base field).
    pub const Y: Self = Self { c0: 0, c1: 1 };

    #[inline]
    pub const fn new(c0: u64, c1: u64) -> Self {
        Self { c0, c1 }
    }

    /// The coefficients of `y^0` and `y^1`, in that order.
    #[inline]
    pub const fn to_limbs(self) -> [u64; 2] {
        [self.c0, self.c1]
    }

    /// The element whose coefficients of `y^0` and `y^1` are `limbs`, in that order.
    #[inline]
    pub const fn from_limbs(limbs: [u64; 2]) -> Self {
        let [c0, c1] = limbs;
        Self { c0, c1 }
    }

    #[inline]
    pub const fn is_zero(self) -> bool {
        self.c0 == 0 && self.c1 == 0
    }

    /// The base-field element this is, or `None` when the `y` coefficient is nonzero.
    #[inline]
    #[must_use]
    pub const fn as_base(self) -> Option<F64> {
        if self.c1 == 0 { Some(F64(self.c0)) } else { None }
    }

    /// Product without the base-field reduction, for XOR accumulation.
    ///
    /// Schoolbook: four base products into the coefficients of `y^0..y^2`, then the y-fold.
    #[inline]
    pub fn mul_unreduced(self, rhs: Self) -> F128Unreduced {
        let (a, b) = (self.to_limbs(), rhs.to_limbs());
        let e0 = mul_wide(a[0], b[0]);
        let e1 = mul_wide(a[0], b[1]) ^ mul_wide(a[1], b[0]);
        let e2 = mul_wide(a[1], b[1]);
        F128Unreduced([e0 ^ e2, e1 ^ (e2 << 1)])
    }

    /// Mixed product by a base-field scalar.
    #[inline]
    pub fn mul_base(self, k: F64) -> Self {
        self.mul_base_unreduced(k).reduce()
    }

    /// Mixed product by a base-field scalar without the reduction, for XOR accumulation.
    ///
    /// The scalar has no `y` component, so the two coefficients multiply independently in `K`.
    #[inline]
    pub fn mul_base_unreduced(self, k: F64) -> F128Unreduced {
        F128Unreduced(self.to_limbs().map(|c| mul_wide(c, k.0)))
    }

    /// Squaring. The cross term vanishes in characteristic 2:
    ///
    /// ```text
    ///     (c0 + c1*y)^2 = c0^2 + c1^2*y^2 = (c0^2 + c1^2) + x*c1^2*y     (y^2 = x*y + 1)
    /// ```
    #[inline]
    pub fn square(self) -> Self {
        let [s0, s1] = self.to_limbs().map(|c| mul_wide(c, c));
        F128Unreduced([s0 ^ s1, s1 << 1]).reduce()
    }

    /// The Frobenius `self^(2^64)`, the conjugation of `F128/K`. The roots of `y^2 + x*y + 1` are
    /// `y` and `y + x`, so `c0 + c1·y ↦ (c0 + x·c1) + c1·y`: one shift-and-reduce and one XOR.
    #[inline]
    pub const fn frobenius(self) -> Self {
        Self {
            c0: self.c0 ^ mul_by_g(F64(self.c1)).0,
            c1: self.c1,
        }
    }

    /// Multiplicative inverse: `self^(2^128 − 2)`. `ZERO.inv() == ZERO`.
    ///
    /// Via the norm to the base field: `self·φ(self)` is the norm `N(self) ∈ K`, so
    /// `self⁻¹ = φ(self)·N(self)⁻¹` needs one extension multiply, one base-field inverse and one
    /// base-field scaling.
    pub fn inv(self) -> Self {
        let conjugate = self.frobenius();
        let norm = self * conjugate;
        debug_assert!(norm.as_base().is_some(), "the norm of an F128 element must lie in K");
        conjugate.mul_base(F64(norm.c0).inv())
    }
}

impl Add for F128 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self {
            c0: self.c0 ^ rhs.c0,
            c1: self.c1 ^ rhs.c1,
        }
    }
}

impl AddAssign for F128 {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.c0 ^= rhs.c0;
        self.c1 ^= rhs.c1;
    }
}

impl From<F64> for F128 {
    #[inline]
    fn from(k: F64) -> Self {
        Self { c0: k.0, c1: 0 }
    }
}

/// The word whose bits are `n`'s: `c0` its low 64 bits, `c1` its high.
impl From<u128> for F128 {
    #[inline]
    fn from(n: u128) -> Self {
        Self::new(n as u64, (n >> 64) as u64)
    }
}

/// The integer whose bits spell a word's coefficients, `c0` low: the inverse of `From<u128>`.
impl From<F128> for u128 {
    #[inline]
    fn from(v: F128) -> Self {
        v.c0 as u128 | (v.c1 as u128) << 64
    }
}

impl Mul for F128 {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        self.mul_unreduced(rhs).reduce()
    }
}

impl MulAssign for F128 {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl Sum for F128 {
    #[inline]
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |acc, x| acc + x)
    }
}

impl<'a> Sum<&'a F128> for F128 {
    #[inline]
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.copied().sum()
    }
}

impl Product for F128 {
    #[inline]
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ONE, |acc, x| acc * x)
    }
}

impl<'a> Product<&'a F128> for F128 {
    #[inline]
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.copied().product()
    }
}

/// Two independent products.
#[inline]
pub fn mul2(a: [F128; 2], b: [F128; 2]) -> [F128; 2] {
    [a[0] * b[0], a[1] * b[1]]
}

/// Four independent products.
#[inline]
pub fn mul4(a: [F128; 4], b: [F128; 4]) -> [F128; 4] {
    std::array::from_fn(|i| a[i] * b[i])
}

/// Four independent products without the reduction.
#[inline]
pub fn mul_unreduced4(a: [F128; 4], b: [F128; 4]) -> [F128Unreduced; 4] {
    std::array::from_fn(|i| a[i].mul_unreduced(b[i]))
}

/// Eight `E` weights for [`dot_base`].
#[derive(Clone, Copy, Debug, Default)]
#[repr(transparent)]
pub struct Weights8([F128; 8]);

// SAFETY: `repr(transparent)` over an array of plain elements.
unsafe impl crate::Plain for Weights8 {}

impl Weights8 {
    pub fn new(w: &[F128; 8]) -> Self {
        Self(*w)
    }

    #[inline]
    pub fn get(&self, i: usize) -> F128 {
        self.0[i]
    }
}

/// The mixed inner product `sum_i w_i * k_i`, unreduced.
///
/// `k.len()` must be `8 * w.len()`.
#[inline]
pub fn dot_base(w: &[Weights8], k: &[F64]) -> F128Unreduced {
    assert_eq!(k.len(), 8 * w.len());
    let w = w.iter().flat_map(|w| w.0);
    w.zip(k)
        .fold(F128Unreduced::ZERO, |acc, (w, &k)| acc ^ w.mul_base_unreduced(k))
}

/// An F128 value whose coefficients are not yet reduced modulo the base polynomial.
///
/// Coefficient `k` is the 128-bit carry-less polynomial multiplying `y^k`, for `k < 2`.
/// Products land here already folded by `y^2 = x*y + 1`, so a sum of them is a plain XOR.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct F128Unreduced([u128; 2]);

impl F128Unreduced {
    pub const ZERO: Self = Self([0; 2]);

    /// Build from two 128-bit coefficients given as `[low, high]` words.
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx2",
        target_feature = "vpclmulqdq",
        not(target_feature = "avx512f")
    ))]
    #[inline]
    pub(crate) const fn from_coeffs(coeffs: [[u64; 2]; 2]) -> Self {
        let [[l0, h0], [l1, h1]] = coeffs;
        Self([(h0 as u128) << 64 | l0 as u128, (h1 as u128) << 64 | l1 as u128])
    }

    /// Reduce each coefficient modulo the base polynomial.
    #[inline]
    pub fn reduce(self) -> F128 {
        F128::from_limbs(self.0.map(reduce))
    }
}

impl From<F128> for F128Unreduced {
    /// Embed a reduced element: each coefficient is its own 128-bit polynomial.
    #[inline]
    fn from(e: F128) -> Self {
        Self(e.to_limbs().map(u128::from))
    }
}

impl BitXor for F128Unreduced {
    type Output = Self;
    #[inline]
    fn bitxor(mut self, rhs: Self) -> Self {
        self ^= rhs;
        self
    }
}

impl BitXorAssign for F128Unreduced {
    #[inline]
    fn bitxor_assign(&mut self, rhs: Self) {
        self.0[0] ^= rhs.0[0];
        self.0[1] ^= rhs.0[1];
    }
}

/// x86-64 vector helpers for other crates' AVX kernels.
#[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
pub mod x86_64 {
    use core::arch::x86_64::*;

    /// Karatsuba recombination and y-fold in one step, for any register width.
    ///
    /// With `p0 = a0 b0`, `p1 = a1 b1`, `p01 = (a0 + a1)(b0 + b1)` and `y^2 = x y + 1`:
    ///
    /// ```text
    ///     d0 = p0 ^ p1
    ///     d1 = p01 ^ p0 ^ p1 ^ x*p1
    /// ```
    #[cfg(target_feature = "vpclmulqdq")]
    #[inline(always)]
    pub(crate) fn fold<V: Copy>(p0: V, p1: V, p01: V, xor: impl Fn(V, V) -> V, times_x: impl Fn(V) -> V) -> [V; 2] {
        let d0 = xor(p0, p1);
        [d0, xor(xor(p01, d0), times_x(p1))]
    }

    /// `g(spill)` per top nibble `n` of a high word, in each 128-bit lane (see `G_SPILL`'s 512-bit
    /// form): `spill = n ^ n>>1 ^ n>>3` are the bits that `g(hi)` pushes past x^63.
    #[cfg(target_feature = "avx2")]
    static G_SPILL_256: [u8; 32] = {
        let mut t = [0u8; 32];
        let mut i = 0;
        while i < 32 {
            let n = (i % 16) as u8;
            let spill = n ^ (n >> 1) ^ (n >> 3);
            t[i] = spill ^ (spill << 1) ^ (spill << 3) ^ (spill << 4);
            i += 1;
        }
        t
    };

    /// Lane-wise base reduction: qword `i` of the result is the reduction of `hi[i] * x^64 + lo[i]`.
    ///
    /// `lo ^ g(hi) ^ g(spill)`, with `g(y) = y ^ y<<1 ^ y<<3 ^ y<<4 = z ^ z<<3` for `z = y ^ y<<1`, and
    /// `g(spill)` one in-lane byte lookup on the top nibble of `hi`: three shifts and a shuffle instead
    /// of the shift network's six shifts.
    ///
    /// # Safety
    ///
    /// Requires the `avx2` target feature.
    #[cfg(target_feature = "avx2")]
    #[inline]
    #[target_feature(enable = "avx2")]
    pub fn reduce_lanes256(lo: __m256i, hi: __m256i) -> __m256i {
        // SAFETY: a 32-byte read of a 32-byte static.
        let table = unsafe { _mm256_loadu_si256(G_SPILL_256.as_ptr().cast()) };
        let g_spill = _mm256_shuffle_epi8(table, _mm256_srli_epi64::<60>(hi));
        let z = _mm256_xor_si256(hi, _mm256_slli_epi64::<1>(hi));
        _mm256_xor_si256(
            _mm256_xor_si256(lo, z),
            _mm256_xor_si256(g_spill, _mm256_slli_epi64::<3>(z)),
        )
    }

    /// Qword `i` is the reduction of lane `i`'s 128-bit product, `even` holding those of the even
    /// lanes and `odd` those of the odd ones, one per 128-bit lane.
    ///
    /// # Safety
    ///
    /// Requires the `avx2` target feature.
    #[cfg(target_feature = "avx2")]
    #[inline]
    #[target_feature(enable = "avx2")]
    pub fn reduce_halves256(even: __m256i, odd: __m256i) -> __m256i {
        reduce_lanes256(_mm256_unpacklo_epi64(even, odd), _mm256_unpackhi_epi64(even, odd))
    }

    /// `x * p` for each 128-bit lane of a YMM register.
    ///
    /// # Safety
    ///
    /// Requires the `avx2` target feature.
    #[cfg(target_feature = "avx2")]
    #[inline]
    #[target_feature(enable = "avx2")]
    pub fn times_x256(p: __m256i) -> __m256i {
        _mm256_or_si256(
            _mm256_slli_epi64::<1>(p),
            _mm256_bslli_epi128::<8>(_mm256_srli_epi64::<63>(p)),
        )
    }

    /// `g(spill)` per top nibble `n` of a high word: `spill = n ^ n>>1 ^ n>>3` are the bits that
    /// `g(hi) = hi * (x^4 + x^3 + x + 1)` pushes past x^63, and `g(spill)` fits a byte.
    #[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    const G_SPILL: __m512i = {
        let mut words = [0u64; 8];
        let mut n = 0;
        while n < 16 {
            let spill = n ^ (n >> 1) ^ (n >> 3);
            let g = (spill ^ (spill << 1) ^ (spill << 3) ^ (spill << 4)) as u8 as u64;
            // The table fills each 128-bit lane, as the in-lane byte shuffle reads it.
            let mut lane = 0;
            while lane < 4 {
                words[2 * lane + n / 8] |= g << (8 * (n % 8));
                lane += 1;
            }
            n += 1;
        }
        crate::simd::from_words(words)
    };

    /// Lane-wise base reduction on eight qwords:
    /// `lo ^ g(hi) ^ g(spill)`, with `g(y) = y ^ y<<1 ^ y<<3 ^ y<<4 = z ^ z<<3` for `z = y ^ y<<1`, and
    /// `g(spill)` one in-lane byte lookup on the top nibble of `hi`.
    #[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    #[inline]
    #[target_feature(enable = "avx512f", enable = "avx512bw")]
    pub(crate) fn reduce_lanes512(lo: __m512i, hi: __m512i) -> __m512i {
        let g_spill = _mm512_shuffle_epi8(G_SPILL, _mm512_srli_epi64::<60>(hi));
        let z = _mm512_xor_si512(hi, _mm512_slli_epi64::<1>(hi));
        _mm512_xor_si512(
            _mm512_ternarylogic_epi64::<0x96>(lo, z, g_spill),
            _mm512_slli_epi64::<3>(z),
        )
    }

    /// [`reduce_halves256`] on eight qwords.
    ///
    /// # Safety
    ///
    /// Requires the `avx512f` and `avx512bw` target features.
    #[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    #[inline]
    #[target_feature(enable = "avx512f", enable = "avx512bw")]
    pub fn reduce_halves512(even: __m512i, odd: __m512i) -> __m512i {
        reduce_lanes512(_mm512_unpacklo_epi64(even, odd), _mm512_unpackhi_epi64(even, odd))
    }

    /// `x * p` for each 128-bit lane of a ZMM register.
    ///
    /// # Safety
    ///
    /// Requires the `avx512f` and `avx512bw` target features.
    #[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    #[inline]
    #[target_feature(enable = "avx512f", enable = "avx512bw")]
    pub fn times_x512(p: __m512i) -> __m512i {
        _mm512_or_si512(
            _mm512_slli_epi64::<1>(p),
            _mm512_bslli_epi128::<8>(_mm512_srli_epi64::<63>(p)),
        )
    }
}

// Tests: products against a portable reference, independent Python vectors, field axioms,
// and computational irreducibility proofs for both moduli.

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::gf2_64::{R64, clmul_portable};
    use crate::test_rng::Rng;

    /// Schoolbook on the portable carry-less product, then the y-fold and the reduction.
    fn reference_mul(a: F128, b: F128) -> F128 {
        let (a, b) = (a.to_limbs(), b.to_limbs());
        let mut e = [0u128; 3];
        for i in 0..2 {
            for j in 0..2 {
                e[i + j] ^= clmul_portable(a[i], b[j]);
            }
        }
        F128::from_limbs([e[0] ^ e[2], e[1] ^ (e[2] << 1)].map(reduce))
    }

    /// Vectors generated by an independent Python implementation: (a, b, a·b, a·a, a⁻¹).
    type ReferenceVector = ([u64; 2], [u64; 2], [u64; 2], [u64; 2], [u64; 2]);
    const VECTORS: [ReferenceVector; 4] = [
        (
            [0x8a1d921ca352a3c3, 0xa10d04b240699a83],
            [0x936d4747ab0e6d1c, 0xe46ab5adb68f9c7d],
            [0xfbbffa3000b331c0, 0xbf494d14ce4eadf8],
            [0x3eb21e43df9bbb1c, 0x7836265481e5ee7d],
            [0x4dbcb8833d2c881c, 0x01d5fd8ef4de46b1],
        ),
        (
            [0x4ced30628e0cd071, 0xc694494e11044370],
            [0x079184601cbc456d, 0xc2b90e2d4a7acb31],
            [0x1df92a5bbf394f60, 0x4f9871091371b5d2],
            [0x87f8c19a80de6b2b, 0xe1b7b5434dbf44ba],
            [0xe5886c008822ac39, 0x5014981d45105c3b],
        ),
        (
            [0x1f7678795f345ff4, 0xd584a285e92195e8],
            [0xa4fab233b7895f8e, 0xe8c4546870efc3e0],
            [0x39944740fab79b32, 0x677a979829fc8fea],
            [0x33bf067a3def0161, 0x7dd98b6fdaf72b54],
            [0x126bd1f8da56668e, 0xf1e4a54eaa0dc2d0],
        ),
        (
            [0xf8a7e4e12a61d563, 0x852495966643d5c8],
            [0x5b2495d1eb090346, 0x786d6f68d7273a2f],
            [0x6617b862c301fca8, 0x1edae1e051362791],
            [0xd03dc472c71a8299, 0xab7efb6717791597],
            [0x36a2e97ec7233d69, 0xb5f24753a7ede4d1],
        ),
    ];

    /// Elements whose products drive every reduction spill: all-ones, top bits only, identities.
    const CORNERS: [F128; 6] = [
        F128::ZERO,
        F128::ONE,
        F128::Y,
        F128::new(u64::MAX, u64::MAX),
        F128::new(1 << 63, 1 << 63),
        F128::new(0, u64::MAX),
    ];

    /// Random pairs followed by every pair of corners.
    fn operand_pairs(seed: u64) -> Vec<(F128, F128)> {
        let mut rng = Rng::new(seed);
        let random = (0..10_000).map(|_| (rng.ext(), rng.ext()));
        let corners = CORNERS.iter().flat_map(|&a| CORNERS.iter().map(move |&b| (a, b)));
        random.chain(corners).collect()
    }

    #[test]
    fn python_vectors_and_modulus() {
        for (a, b, c, s, i) in VECTORS {
            let (a, b) = (F128::from_limbs(a), F128::from_limbs(b));
            assert_eq!(a * b, F128::from_limbs(c));
            assert_eq!(a.square(), F128::from_limbs(s));
            assert_eq!(a.inv(), F128::from_limbs(i));
            assert_eq!(reference_mul(a, b), F128::from_limbs(c));
        }
        // y^2 = x*y + 1.
        assert_eq!(F128::Y * F128::Y, F128::new(1, 2));
    }

    #[test]
    fn products_match_reference() {
        for (a, b) in operand_pairs(2) {
            let want = reference_mul(a, b);
            // The product, its unreduced form, and squaring.
            assert_eq!(a * b, want);
            assert_eq!(a.mul_unreduced(b).reduce(), want);
            assert_eq!(a.square(), reference_mul(a, a));
            // A mixed product is a full product by an element with no y part.
            let k = F64(b.c1);
            let want = reference_mul(a, F128::from(k));
            assert_eq!(a.mul_base(k), want);
            assert_eq!(a.mul_base_unreduced(k).reduce(), want);
        }
    }

    #[test]
    fn batched_products_match_reference() {
        // Four consecutive pairs per batch.
        let pairs = operand_pairs(6);
        for batch in pairs.as_chunks::<4>().0 {
            let a = batch.map(|(a, _)| a);
            let b = batch.map(|(_, b)| b);
            let want: [F128; 4] = std::array::from_fn(|i| reference_mul(a[i], b[i]));
            assert_eq!(mul4(a, b), want);
            assert_eq!(mul_unreduced4(a, b).map(F128Unreduced::reduce), want);
            assert_eq!(mul2([a[0], a[1]], [b[0], b[1]]), [want[0], want[1]]);
        }
    }

    #[test]
    fn square_and_inv() {
        let mut rng = Rng::new(4);
        for _ in 0..1000 {
            let a = rng.ext();
            assert_eq!(a.square(), a * a);
            if !a.is_zero() {
                assert_eq!(a * a.inv(), F128::ONE);
            }
            // K-valued elements are the cases `inv`'s norm path is most likely to get wrong, and the
            // interpreter's MUL back-solve inverts K-valued words exclusively.
            let k = F128::new(rng.ext().c0, 0);
            if !k.is_zero() {
                assert_eq!(k * k.inv(), F128::ONE);
                assert_eq!(k.inv(), F128::from(F64(k.c0).inv()));
            }
        }
        assert_eq!(F128::ZERO.inv(), F128::ZERO);
    }

    #[test]
    fn batched_mixed_products_match_scalar() {
        let mut rng = Rng::new(9);
        for _ in 0..200 {
            let w: [F128; 16] = std::array::from_fn(|_| rng.ext());
            let packed = [
                Weights8::new(w[..8].try_into().unwrap()),
                Weights8::new(w[8..].try_into().unwrap()),
            ];
            assert!((0..16).all(|i| packed[i / 8].get(i % 8) == w[i]));
            let k: [F64; 16] = std::array::from_fn(|_| F64(rng.ext().c0));
            let want = (0..16).map(|i| w[i].mul_base(k[i])).sum();
            assert_eq!(dot_base(&packed, &k).reduce(), want);
        }
    }

    /// `frobenius` is the shuffle form of `self^(2^64)`, which `inv` relies on.
    #[test]
    fn frobenius_is_the_64th_squaring() {
        let mut rng = Rng::new(7);
        for _ in 0..200 {
            let a = rng.ext();
            let mut want = a;
            for _ in 0..64 {
                want = want.square();
            }
            assert_eq!(a.frobenius(), want);
            // Two applications return the element (Gal(F128/K) has order 2), and the norm
            // a·φ(a) lands in K.
            assert_eq!(a.frobenius().frobenius(), a);
            assert_eq!((a * a.frobenius()).c1, 0);
        }
    }

    #[test]
    fn unreduced_accumulation_matches_reduced_sum() {
        let mut rng = Rng::new(5);
        for _ in 0..100 {
            // Start from an embedded element: its unreduced form reduces to itself.
            let start = rng.ext();
            let mut acc = F128Unreduced::from(start);
            let mut want = start;
            // Sixteen full products and sixteen mixed products, summed both ways.
            for _ in 0..16 {
                let (a, b, k) = (rng.ext(), rng.ext(), F64(rng.next_u64()));
                acc ^= a.mul_unreduced(b) ^ a.mul_base_unreduced(k);
                want += a * b + a.mul_base(k);
            }
            assert_eq!(acc.reduce(), want);
        }
    }

    // GF(2)[x] helpers on u128 for the base-polynomial irreducibility test.

    fn gf2_mod(mut a: u128, m: u128) -> u128 {
        let dm = 127 - m.leading_zeros();
        while a != 0 {
            let da = 127 - a.leading_zeros();
            if da < dm {
                break;
            }
            a ^= m << (da - dm);
        }
        a
    }

    fn gf2_gcd(mut a: u128, mut b: u128) -> u128 {
        while b != 0 {
            let r = gf2_mod(a, b);
            a = b;
            b = r;
        }
        a
    }

    /// Rabin: p64 (degree 64 = 2^6) is irreducible iff x^(2^64) ≡ x mod p64
    /// and gcd(x^(2^32) − x, p64) = 1.
    #[test]
    fn base_poly_irreducible() {
        const P64: u128 = (1u128 << 64) | (R64 as u128);
        let mut t = F64::G;
        for _ in 0..32 {
            t = t.square();
        }
        assert_eq!(gf2_gcd((t.0 as u128) ^ 2, P64), 1, "factor of degree | 32");
        for _ in 0..32 {
            t = t.square();
        }
        assert_eq!(t, F64::G, "x^(2^64) != x mod p64");
    }

    /// A quadratic over `K` is irreducible iff it has no root in `K`, iff `y^|K| ≠ y`
    /// modulo it: `y^(2^64)` by 64 squarings must not be `y`.
    #[test]
    fn extension_poly_irreducible_over_base() {
        let mut t = F128::Y;
        for _ in 0..64 {
            t = t.square();
        }
        assert_ne!(t, F128::Y, "y^2 + x*y + 1 has a root in GF(2^64)");
        // The other root is y + x.
        assert_eq!(t, F128::new(2, 1));
    }
}
