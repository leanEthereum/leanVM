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
//! x86 spends 3 products on Karatsuba.
//! aarch64 spends 4 on the schoolbook, since there a product costs no more than an XOR.
//!
//! Both folds are GF(2)-linear, so they commute with XOR.
//! A sum of products therefore accumulates after the y-fold and reduces once.

use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, BitXor, BitXorAssign, Mul, MulAssign};

use super::gf2_64::F64;
#[cfg(not(any(
    all(target_arch = "aarch64", target_feature = "aes"),
    all(target_arch = "x86_64", target_feature = "pclmulqdq")
)))]
use super::gf2_64::mul_wide;
#[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
use super::gf2_64::{reduce, square_wide};
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
    #[inline]
    pub fn mul_unreduced(self, rhs: Self) -> F128Unreduced {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            aarch64::mul_unreduced(self, rhs)
        }
        #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
        {
            // SAFETY: pclmulqdq is enabled at compile time.
            unsafe { x86_64::mul_unreduced(self, rhs) }
        }
        #[cfg(not(any(
            all(target_arch = "aarch64", target_feature = "aes"),
            all(target_arch = "x86_64", target_feature = "pclmulqdq")
        )))]
        {
            software::mul_unreduced(self, rhs)
        }
    }

    /// Mixed product by a base-field scalar.
    ///
    /// The scalar has no `y` component, so the two coefficients multiply independently in `K`.
    #[inline]
    pub fn mul_base(self, k: F64) -> Self {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            aarch64::mul_base(self, k)
        }
        #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
        {
            self.mul_base_unreduced(k).reduce()
        }
    }

    /// Mixed product by a base-field scalar without the reduction, for XOR accumulation.
    #[inline]
    pub fn mul_base_unreduced(self, k: F64) -> F128Unreduced {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            aarch64::mul_base_unreduced(self, k)
        }
        #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
        {
            // SAFETY: pclmulqdq is enabled at compile time.
            unsafe { x86_64::mul_base_unreduced(self, k) }
        }
        #[cfg(not(any(
            all(target_arch = "aarch64", target_feature = "aes"),
            all(target_arch = "x86_64", target_feature = "pclmulqdq")
        )))]
        {
            F128Unreduced::from_wide(self.to_limbs().map(|c| mul_wide(c, k.0)))
        }
    }

    /// Squaring, with 2 base-field squarings instead of 3 products.
    ///
    /// The cross term vanishes in characteristic 2:
    ///
    /// ```text
    ///     (c0 + c1*y)^2 = c0^2 + c1^2*y^2 = (c0^2 + c1^2) + x*c1^2*y     (y^2 = x*y + 1)
    /// ```
    #[inline]
    pub fn square(self) -> Self {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            aarch64::square(self)
        }
        #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
        {
            let [s0, s1] = self.to_limbs().map(square_wide);
            F128Unreduced::from_wide([s0 ^ s1, s1 << 1]).reduce()
        }
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
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            aarch64::mul(self, rhs)
        }
        #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
        {
            self.mul_unreduced(rhs).reduce()
        }
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

// Batched products fill the independent lanes exposed by x86 vector instructions.

/// Two independent products.
#[inline(always)]
pub fn mul2(a: [F128; 2], b: [F128; 2]) -> [F128; 2] {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
    // SAFETY: both features are enabled at compile time.
    return unsafe { x86_64::mul_vec2(a, b) };
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2")))]
    [a[0] * b[0], a[1] * b[1]]
}

/// Four independent products.
#[inline(always)]
pub fn mul4(a: [F128; 4], b: [F128; 4]) -> [F128; 4] {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    // SAFETY: both features are enabled at compile time, and `f128x8` fails the build without avx512bw.
    return unsafe { x86_64::mul_vec4(a, b) };
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
    {
        let lo = mul2([a[0], a[1]], [b[0], b[1]]);
        let hi = mul2([a[2], a[3]], [b[2], b[3]]);
        [lo[0], lo[1], hi[0], hi[1]]
    }
}

/// Four independent products without the reduction, for a caller XOR-accumulating many products.
#[inline(always)]
pub fn mul_unreduced4(a: [F128; 4], b: [F128; 4]) -> [F128Unreduced; 4] {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    // SAFETY: both features are enabled at compile time.
    return unsafe { x86_64::mul_unreduced_vec4(a, b) };
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "vpclmulqdq",
        target_feature = "avx2",
        not(target_feature = "avx512f")
    ))]
    // SAFETY: both features are enabled at compile time.
    return unsafe {
        let lo = x86_64::mul_unreduced_vec2([a[0], a[1]], [b[0], b[1]]);
        let hi = x86_64::mul_unreduced_vec2([a[2], a[3]], [b[2], b[3]]);
        [lo[0], lo[1], hi[0], hi[1]]
    };
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2")))]
    std::array::from_fn(|i| a[i].mul_unreduced(b[i]))
}

/// Eight `E` weights, laid out once for [`dot_base`].
///
/// Pairs share a 128-bit lane, so the kernel loads them with no shuffle:
///
/// ```text
///     lo  lane j = [w_2j.c0,   w_2j.c1  ]
///     hi  lane j = [w_2j+1.c0, w_2j+1.c1]
/// ```
#[derive(Clone, Copy, Debug, Default)]
#[repr(C, align(64))]
pub struct Weights8 {
    lo: [u64; 8],
    hi: [u64; 8],
}

// SAFETY: `repr(C)` over arrays of `u64` that fill its alignment, so there is no padding.
unsafe impl crate::Plain for Weights8 {}

impl Weights8 {
    /// Pack eight weights.
    pub fn new(w: &[F128; 8]) -> Self {
        let mut out = Self::default();
        for j in 0..4 {
            let (e, o) = (w[2 * j], w[2 * j + 1]);
            out.lo[2 * j..2 * j + 2].copy_from_slice(&[e.c0, e.c1]);
            out.hi[2 * j..2 * j + 2].copy_from_slice(&[o.c0, o.c1]);
        }
        out
    }

    /// Weight `i`, unpacked.
    #[inline]
    pub fn get(&self, i: usize) -> F128 {
        let j = i / 2;
        let pair = if i.is_multiple_of(2) { &self.lo } else { &self.hi };
        F128::new(pair[2 * j], pair[2 * j + 1])
    }
}

/// The mixed inner product `sum_i w_i * k_i`, unreduced.
///
/// `k.len()` must be `8 * w.len()`.
///
/// On AVX-512 the sums stay in two registers for the whole slice: four CLMULs per eight terms.
#[inline]
pub fn dot_base(w: &[Weights8], k: &[F64]) -> F128Unreduced {
    assert_eq!(k.len(), 8 * w.len());
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    // SAFETY: both features are enabled at compile time; the lengths match.
    return unsafe { x86_64::dot_base(w, k) };
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "vpclmulqdq",
        target_feature = "avx2",
        not(target_feature = "avx512f")
    ))]
    // SAFETY: both features are enabled at compile time; the lengths match.
    return unsafe { x86_64::dot_base_ymm(w, k) };
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2")))]
    w.iter()
        .zip(k.as_chunks::<8>().0)
        .fold(F128Unreduced::ZERO, |acc, (w, k)| {
            (0..8).fold(acc, |acc, i| acc ^ w.get(i).mul_base_unreduced(k[i]))
        })
}

/// An F128 value whose coefficients are not yet reduced modulo the base polynomial.
///
/// Coefficient `k` is the 128-bit carry-less polynomial multiplying `y^k`, for `k < 2`.
/// Products land here already folded by `y^2 = x*y + 1`, so a sum of them is a plain XOR.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct F128Unreduced {
    /// The 128-bit coefficients of `y^0` and `y^1`, each as its `[low, high]` words.
    ///
    /// Words rather than `u128`, so that accumulation compiles to vector XORs.
    coeffs: [[u64; 2]; 2],
}

impl F128Unreduced {
    pub const ZERO: Self = Self { coeffs: [[0; 2]; 2] };

    /// The two 128-bit coefficients as `[low, high]` words.
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    #[inline]
    pub(crate) const fn coeffs(self) -> [[u64; 2]; 2] {
        self.coeffs
    }

    /// Build from two 128-bit coefficients given as `[low, high]` words.
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
    #[inline]
    pub(crate) const fn from_coeffs(coeffs: [[u64; 2]; 2]) -> Self {
        Self { coeffs }
    }

    /// Build from two 128-bit coefficients.
    #[inline]
    fn from_wide(coeffs: [u128; 2]) -> Self {
        Self {
            coeffs: coeffs.map(|c| [c as u64, (c >> 64) as u64]),
        }
    }

    /// Reduce each coefficient modulo the base polynomial.
    #[inline]
    pub fn reduce(self) -> F128 {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            aarch64::reduce(self)
        }
        #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
        {
            let [c0, c1] = self
                .coeffs
                .map(|[lo, hi]| reduce(u128::from(hi) << 64 | u128::from(lo)));
            F128 { c0, c1 }
        }
    }
}

impl From<F128> for F128Unreduced {
    /// Embed a reduced element: each coefficient is its own 128-bit polynomial.
    #[inline]
    fn from(e: F128) -> Self {
        Self {
            coeffs: e.to_limbs().map(|c| [c, 0]),
        }
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
        for (acc, x) in self.coeffs.as_flattened_mut().iter_mut().zip(rhs.coeffs.as_flattened()) {
            *acc ^= x;
        }
    }
}

/// aarch64 kernels.
///
/// On Apple cores a carry-less multiply issues as fast as an XOR.
/// So these kernels trade shuffles for products, and reduce with two more products.
///
/// Moving a word between the integer and SIMD register files is slower than a product.
/// So every operand stays in SIMD registers from load to store.
///
/// An element sits in one register, `c0` in the low qword and `c1` in the high one.
/// A product then reads any coefficient pair with the low-lane or high-lane multiply.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
pub mod aarch64 {
    use super::{F128, F128Unreduced};
    use crate::field::gf2_64::{F64, R64};
    use crate::field::neon::xor3_u64;
    use core::arch::aarch64::*;
    use core::mem::transmute;

    /// Carry-less product of the low qwords.
    #[inline(always)]
    fn lo(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
        // SAFETY: the module's cfg enables aes, and both sides of the reinterpret are 128 bits.
        unsafe { transmute::<u128, uint64x2_t>(vmull_p64(vgetq_lane_u64::<0>(a), vgetq_lane_u64::<0>(b))) }
    }

    /// Carry-less product of the high qwords.
    #[inline(always)]
    fn hi(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
        // SAFETY: the module's cfg enables aes, and both sides of the reinterpret are 128 bits.
        unsafe { transmute::<u128, uint64x2_t>(vmull_high_p64(vreinterpretq_p64_u64(a), vreinterpretq_p64_u64(b))) }
    }

    /// Three-way XOR.
    #[inline(always)]
    fn xor3(a: uint64x2_t, b: uint64x2_t, c: uint64x2_t) -> uint64x2_t {
        // SAFETY: the helper issues `EOR3` only where the cfg enables it.
        unsafe { xor3_u64(a, b, c) }
    }

    /// `x * p` for a 128-bit polynomial `p` of degree at most 126: a one-bit shift across the qwords.
    #[inline(always)]
    fn times_x(p: uint64x2_t) -> uint64x2_t {
        // SAFETY: NEON is part of the aarch64 baseline.
        unsafe {
            let carry = vextq_u64::<1>(vdupq_n_u64(0), vshrq_n_u64::<63>(p));
            vorrq_u64(vshlq_n_u64::<1>(p), carry)
        }
    }

    /// An element as its register.
    #[inline(always)]
    fn split(e: F128) -> uint64x2_t {
        // SAFETY: NEON is part of the aarch64 baseline.
        unsafe { vcombine_u64(vcreate_u64(e.c0), vcreate_u64(e.c1)) }
    }

    /// The element whose coefficients are the low qwords of `c0` and `c1`.
    #[inline(always)]
    fn join(c0: uint64x2_t, c1: uint64x2_t) -> F128 {
        // SAFETY: NEON is part of the aarch64 baseline; a register and a `[u64; 2]` hold the same bits.
        unsafe { F128::from_limbs(transmute::<uint64x2_t, [u64; 2]>(vzip1q_u64(c0, c1))) }
    }

    /// Reduce one 128-bit coefficient into its low qword.
    ///
    /// Write the coefficient as `lo + hi * x^64`, with `x^64 = 0x1B`:
    ///
    /// ```text
    ///     hi * 0x1B     = [a, s]      s has at most 4 bits
    ///     s  * 0x1B     = [b, 0]      at most 8 bits, so the fold ends here
    ///     result        = lo ^ a ^ b
    /// ```
    ///
    /// Two high-lane products and one three-way XOR.
    #[inline(always)]
    fn reduce_lane(d: uint64x2_t, r: uint64x2_t) -> uint64x2_t {
        let t = hi(d, r);
        xor3(d, t, hi(t, r))
    }

    /// Reduce the two coefficients of an unreduced element.
    #[inline(always)]
    fn reduce2([d0, d1]: [uint64x2_t; 2]) -> F128 {
        // SAFETY: NEON is part of the aarch64 baseline.
        let r = unsafe { vdupq_n_u64(R64) };
        join(reduce_lane(d0, r), reduce_lane(d1, r))
    }

    /// The y-folded schoolbook product: four base products, each read straight from the operand registers.
    ///
    /// ```text
    ///     y^0:  a0 b0 + a1 b1                     (y^2 = x y + 1)
    ///     y^1:  a0 b1 + a1 b0 + x a1 b1
    /// ```
    #[inline(always)]
    fn schoolbook(a: F128, b: F128) -> [uint64x2_t; 2] {
        let (a01, b01) = (split(a), split(b));
        // SAFETY: NEON is part of the aarch64 baseline.
        let a10 = unsafe { vextq_u64::<1>(a01, a01) };
        let (m00, m11) = (lo(a01, b01), hi(a01, b01));
        let (m10, m01) = (lo(a10, b01), hi(a10, b01));
        // SAFETY: NEON is part of the aarch64 baseline.
        [unsafe { veorq_u64(m00, m11) }, xor3(m01, m10, times_x(m11))]
    }

    /// The product, reduced.
    #[inline(always)]
    pub fn mul(a: F128, b: F128) -> F128 {
        reduce2(schoolbook(a, b))
    }

    /// Two 128-bit coefficients as an unreduced element.
    #[inline(always)]
    fn unreduced(d: [uint64x2_t; 2]) -> F128Unreduced {
        // SAFETY: a 128-bit register and a `[u64; 2]` hold the same bits.
        F128Unreduced {
            coeffs: d.map(|d| unsafe { transmute::<uint64x2_t, [u64; 2]>(d) }),
        }
    }

    /// The product without the base-field reduction.
    #[inline(always)]
    pub fn mul_unreduced(a: F128, b: F128) -> F128Unreduced {
        unreduced(schoolbook(a, b))
    }

    /// The mixed product by a base-field scalar, without the reduction: two base products.
    #[inline(always)]
    fn mul_base_lanes(a: F128, k: F64) -> [uint64x2_t; 2] {
        let a01 = split(a);
        // SAFETY: NEON is part of the aarch64 baseline.
        let kk = unsafe { vdupq_n_u64(k.0) };
        [lo(a01, kk), hi(a01, kk)]
    }

    /// The mixed product by a base-field scalar, reduced.
    #[inline(always)]
    pub fn mul_base(a: F128, k: F64) -> F128 {
        reduce2(mul_base_lanes(a, k))
    }

    /// The mixed product by a base-field scalar, without the reduction.
    #[inline(always)]
    pub fn mul_base_unreduced(a: F128, k: F64) -> F128Unreduced {
        unreduced(mul_base_lanes(a, k))
    }

    /// The square: two base squares, then the y-fold `y^2 = x y + 1`.
    #[inline(always)]
    pub fn square(a: F128) -> F128 {
        let a01 = split(a);
        let (s0, s1) = (lo(a01, a01), hi(a01, a01));
        // SAFETY: NEON is part of the aarch64 baseline.
        reduce2([unsafe { veorq_u64(s0, s1) }, times_x(s1)])
    }

    /// Reduce an unreduced element.
    #[inline(always)]
    pub fn reduce(u: F128Unreduced) -> F128 {
        // SAFETY: a `[u64; 2]` and a 128-bit register hold the same bits.
        reduce2(u.coeffs.map(|c| unsafe { transmute::<[u64; 2], uint64x2_t>(c) }))
    }
}

/// x86-64 kernels.
///
/// The carry-less multiplier is the scarce execution unit, so every kernel spends it only on products.
/// Reductions run as shifts and XORs.
/// A single product packs both operand coefficients in one register and picks one with the CLMUL immediate:
///
/// ```text
///     register     lo qword     hi qword       imm 0x00    imm 0x11
///     r01          c0           c1             p0          p1
///     s            c0 ^ c1      c0 ^ c1        p01         p01
/// ```
///
/// The batched kernels instead place one product per 128-bit lane and reduce every lane at once.
#[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
pub mod x86_64 {
    use super::{F128, F128Unreduced};
    use crate::Plain;
    use crate::field::gf2_64::F64;
    use core::arch::x86_64::*;

    /// The bits of a vector as plain words of the same size.
    #[inline(always)]
    fn bits<V: Plain, W: Plain>(v: V) -> W {
        const { assert!(size_of::<V>() == size_of::<W>()) };
        // SAFETY: both types are plain and of one size, so every bit pattern is valid in each.
        unsafe { core::mem::transmute_copy(&v) }
    }

    /// Two 64-bit words as one register, `lo` in the low qword.
    #[inline(always)]
    pub(crate) fn pair(lo: u64, hi: u64) -> __m128i {
        bits::<[u64; 2], __m128i>([lo, hi])
    }

    /// `x * p` for each 128-bit lane `p` of degree at most 126: a one-bit shift across the qwords.
    #[inline]
    #[target_feature(enable = "sse2")]
    fn times_x(p: __m128i) -> __m128i {
        _mm_or_si128(_mm_slli_epi64::<1>(p), _mm_slli_si128::<8>(_mm_srli_epi64::<63>(p)))
    }

    /// Karatsuba recombination and y-fold in one step, for any register width.
    ///
    /// With `p0 = a0 b0`, `p1 = a1 b1`, `p01 = (a0 + a1)(b0 + b1)` and `y^2 = x y + 1`:
    ///
    /// ```text
    ///     d0 = p0 ^ p1
    ///     d1 = p01 ^ p0 ^ p1 ^ x*p1
    /// ```
    #[inline(always)]
    pub(crate) fn fold<V: Copy>(p0: V, p1: V, p01: V, xor: impl Fn(V, V) -> V, times_x: impl Fn(V) -> V) -> [V; 2] {
        let d0 = xor(p0, p1);
        [d0, xor(xor(p01, d0), times_x(p1))]
    }

    /// The y-folded Karatsuba product of one pair.
    #[inline]
    #[target_feature(enable = "pclmulqdq")]
    fn karatsuba(a: F128, b: F128) -> [__m128i; 2] {
        let (a01, b01) = (pair(a.c0, a.c1), pair(b.c0, b.c1));
        let (a_s, b_s) = (pair(a.c0 ^ a.c1, 0), pair(b.c0 ^ b.c1, 0));
        let p0 = _mm_clmulepi64_si128::<0x00>(a01, b01);
        let p1 = _mm_clmulepi64_si128::<0x11>(a01, b01);
        let p01 = _mm_clmulepi64_si128::<0x00>(a_s, b_s);
        fold(p0, p1, p01, |x, y| _mm_xor_si128(x, y), |p| times_x(p))
    }

    /// One unreduced product.
    ///
    /// # Safety
    ///
    /// Callable only where pclmulqdq is enabled.
    #[inline]
    #[target_feature(enable = "pclmulqdq")]
    pub fn mul_unreduced(a: F128, b: F128) -> F128Unreduced {
        F128Unreduced {
            coeffs: karatsuba(a, b).map(bits::<__m128i, [u64; 2]>),
        }
    }

    /// One unreduced mixed product: two base products from one operand register.
    ///
    /// # Safety
    ///
    /// Callable only where pclmulqdq is enabled.
    #[inline]
    #[target_feature(enable = "pclmulqdq")]
    pub fn mul_base_unreduced(a: F128, k: F64) -> F128Unreduced {
        let a01 = pair(a.c0, a.c1);
        let k = _mm_cvtsi64_si128(k.0 as i64);
        // Immediate 0x01 multiplies the high qword of the first operand by the low qword of the second.
        let products = [
            _mm_clmulepi64_si128::<0x00>(a01, k),
            _mm_clmulepi64_si128::<0x01>(a01, k),
        ];
        F128Unreduced {
            coeffs: products.map(bits::<__m128i, [u64; 2]>),
        }
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

    /// The y-folded Karatsuba products of two pairs, one pair per 128-bit lane.
    #[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx2"))]
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx2")]
    fn karatsuba_vec2(a: [F128; 2], b: [F128; 2]) -> [__m256i; 2] {
        // One coefficient of both elements, in the low qword of each lane.
        let pack = |c: [u64; 2]| _mm256_set_epi64x(0, c[1] as i64, 0, c[0] as i64);
        let (a0, a1) = (pack(a.map(|e| e.c0)), pack(a.map(|e| e.c1)));
        let (b0, b1) = (pack(b.map(|e| e.c0)), pack(b.map(|e| e.c1)));
        // One instruction per base product covers both lanes.
        let mul = |x, y| _mm256_clmulepi64_epi128::<0x00>(x, y);
        let xor = |x, y| _mm256_xor_si256(x, y);
        fold(mul(a0, b0), mul(a1, b1), mul(xor(a0, a1), xor(b0, b1)), xor, |p| {
            times_x256(p)
        })
    }

    /// Two independent products in the two 128-bit lanes of a YMM register.
    ///
    /// # Safety
    ///
    /// Callable only where vpclmulqdq and avx2 are enabled.
    #[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx2"))]
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx2")]
    pub fn mul_vec2(a: [F128; 2], b: [F128; 2]) -> [F128; 2] {
        let [d0, d1] = karatsuba_vec2(a, b);
        // Lane i of c01 is [c0_i, c1_i].
        let w = bits::<__m256i, [u64; 4]>(reduce_halves256(d0, d1));
        std::array::from_fn(|i| F128::new(w[2 * i], w[2 * i + 1]))
    }

    /// Two independent unreduced products, packed as for the reduced version.
    ///
    /// # Safety
    ///
    /// Callable only where vpclmulqdq and avx2 are enabled.
    #[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx2"))]
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx2")]
    pub fn mul_unreduced_vec2(a: [F128; 2], b: [F128; 2]) -> [F128Unreduced; 2] {
        let d = karatsuba_vec2(a, b).map(bits::<__m256i, [[u64; 2]; 2]>);
        std::array::from_fn(|i| F128Unreduced {
            coeffs: [d[0][i], d[1][i]],
        })
    }

    /// The y-folded Karatsuba products of four pairs, one pair per 128-bit lane.
    #[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx512bw")]
    fn karatsuba_vec4(a: [F128; 4], b: [F128; 4]) -> [__m512i; 2] {
        // One coefficient of all four elements, in the low qword of each lane.
        let pack = |c: [u64; 4]| _mm512_set_epi64(0, c[3] as i64, 0, c[2] as i64, 0, c[1] as i64, 0, c[0] as i64);
        let (a0, a1) = (pack(a.map(|e| e.c0)), pack(a.map(|e| e.c1)));
        let (b0, b1) = (pack(b.map(|e| e.c0)), pack(b.map(|e| e.c1)));
        // One instruction per base product covers all four lanes.
        let mul = |x, y| _mm512_clmulepi64_epi128::<0x00>(x, y);
        let xor = |x, y| _mm512_xor_si512(x, y);
        fold(mul(a0, b0), mul(a1, b1), mul(xor(a0, a1), xor(b0, b1)), xor, |p| {
            times_x512(p)
        })
    }

    /// Four independent products in the four 128-bit lanes of a ZMM register.
    ///
    /// # Safety
    ///
    /// Callable only where vpclmulqdq, avx512f and avx512bw are enabled.
    #[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx512bw")]
    pub fn mul_vec4(a: [F128; 4], b: [F128; 4]) -> [F128; 4] {
        let [d0, d1] = karatsuba_vec4(a, b);
        // Lane i of c01 is [c0_i, c1_i].
        let w = bits::<__m512i, [u64; 8]>(reduce_halves512(d0, d1));
        std::array::from_fn(|i| F128::new(w[2 * i], w[2 * i + 1]))
    }

    /// Four independent unreduced products, packed as for the reduced version.
    ///
    /// # Safety
    ///
    /// Callable only where vpclmulqdq, avx512f and avx512bw are enabled.
    #[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx512bw")]
    pub fn mul_unreduced_vec4(a: [F128; 4], b: [F128; 4]) -> [F128Unreduced; 4] {
        let d = karatsuba_vec4(a, b).map(bits::<__m512i, [[u64; 2]; 4]>);
        std::array::from_fn(|i| F128Unreduced {
            coeffs: [d[0][i], d[1][i]],
        })
    }

    /// The four products of a shared pair of operand registers against eight packed scalars.
    ///
    /// `a` lane `j` meets `k_2j` through `lo` and `k_2j+1` through `hi`.
    /// Returns the products of `(c0, c1)` by `k_2j`, then by `k_2j+1`.
    ///
    /// # Safety
    ///
    /// Callable only where vpclmulqdq and avx512f are enabled.
    #[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
    pub(crate) fn mul_by_pairs(lo: __m512i, hi: __m512i, k: __m512i) -> [__m512i; 4] {
        // Immediate bit 0 picks the qword of the first operand, bit 4 that of the second.
        [
            _mm512_clmulepi64_epi128::<0x00>(lo, k),
            _mm512_clmulepi64_epi128::<0x01>(lo, k),
            _mm512_clmulepi64_epi128::<0x10>(hi, k),
            _mm512_clmulepi64_epi128::<0x11>(hi, k),
        ]
    }

    /// The mixed inner product over packed weights.
    ///
    /// # Safety
    ///
    /// Callable only where vpclmulqdq and avx512f are enabled.
    #[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
    pub fn dot_base(w: &[super::Weights8], k: &[F64]) -> F128Unreduced {
        let xor = |x, y| _mm512_xor_si512(x, y);
        let mut acc = [_mm512_setzero_si512(); 2];
        for (b, w) in w.iter().enumerate() {
            let kv = crate::simd::load(&k[8 * b..], 0);
            let (lo, hi) = (crate::simd::load(&w.lo, 0), crate::simd::load(&w.hi, 0));
            let [e0, e1, o0, o1] = mul_by_pairs(lo, hi, kv);
            acc = [xor(acc[0], xor(e0, o0)), xor(acc[1], xor(e1, o1))];
        }
        // Fold the four 128-bit lanes of each sum into one.
        let lanes = acc.map(|a| {
            let half = _mm256_xor_si256(_mm512_castsi512_si256(a), _mm512_extracti64x4_epi64::<1>(a));
            let q = _mm_xor_si128(_mm256_castsi256_si128(half), _mm256_extracti128_si256::<1>(half));
            bits::<__m128i, [u64; 2]>(q)
        });
        F128Unreduced { coeffs: lanes }
    }

    /// The four products of `mul_by_pairs` on two lanes, for a machine with VPCLMULQDQ but no AVX-512.
    #[cfg(all(
        target_feature = "vpclmulqdq",
        target_feature = "avx2",
        not(target_feature = "avx512f")
    ))]
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx2")]
    fn mul_by_pairs_ymm(lo: __m256i, hi: __m256i, k: __m256i) -> [__m256i; 4] {
        [
            _mm256_clmulepi64_epi128::<0x00>(lo, k),
            _mm256_clmulepi64_epi128::<0x01>(lo, k),
            _mm256_clmulepi64_epi128::<0x10>(hi, k),
            _mm256_clmulepi64_epi128::<0x11>(hi, k),
        ]
    }

    /// [`super::dot_base`] in two YMM halves.
    ///
    /// # Safety
    ///
    /// Callable only where vpclmulqdq and avx2 are enabled.
    #[cfg(all(
        target_feature = "vpclmulqdq",
        target_feature = "avx2",
        not(target_feature = "avx512f")
    ))]
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx2")]
    pub fn dot_base_ymm(w: &[super::Weights8], k: &[F64]) -> F128Unreduced {
        let xor = |x, y| _mm256_xor_si256(x, y);
        let mut acc = [_mm256_setzero_si256(); 2];
        for (w, k) in w.iter().zip(k.as_chunks::<8>().0) {
            for half in 0..2 {
                let kv = bits::<[F64; 4], __m256i>(k.as_chunks::<4>().0[half]);
                let [lo, hi] = [&w.lo, &w.hi].map(|c| bits::<[u64; 4], __m256i>(c.as_chunks::<4>().0[half]));
                let [e0, e1, o0, o1] = mul_by_pairs_ymm(lo, hi, kv);
                acc = [xor(acc[0], xor(e0, o0)), xor(acc[1], xor(e1, o1))];
            }
        }
        // Fold the two 128-bit lanes of each sum into one.
        let lanes = acc.map(|a| {
            let q = _mm_xor_si128(_mm256_castsi256_si128(a), _mm256_extracti128_si256::<1>(a));
            bits::<__m128i, [u64; 2]>(q)
        });
        F128Unreduced { coeffs: lanes }
    }
}

/// Portable fallback, and the reference every accelerated path is tested against.
pub mod software {
    use super::{F128, F128Unreduced};
    use crate::field::gf2_64::software::clmul;

    /// Schoolbook: four base products into the three coefficients of y^0..y^2, then the y-fold.
    pub fn mul_unreduced(a: F128, b: F128) -> F128Unreduced {
        let (a, b) = (a.to_limbs(), b.to_limbs());
        let mut e = [0u128; 3];
        // a_i * b_j lands on y^(i + j).
        for i in 0..2 {
            for j in 0..2 {
                e[i + j] ^= clmul(a[i], b[j]);
            }
        }
        // y^2 = x*y + 1; e[2] has degree at most 126, so the shift stays within 128 bits.
        F128Unreduced::from_wide([e[0] ^ e[2], e[1] ^ (e[2] << 1)])
    }

    pub fn mul(a: F128, b: F128) -> F128 {
        mul_unreduced(a, b).reduce()
    }
}

// Tests: every backend against the software reference, independent Python vectors, field axioms,
// and computational irreducibility proofs for both moduli.

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::gf2_64::R64;
    use crate::test_rng::Rng;

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
            assert_eq!(software::mul(a, b), F128::from_limbs(c));
        }
        // y^2 = x*y + 1.
        assert_eq!(F128::Y * F128::Y, F128::new(1, 2));
    }

    #[test]
    fn products_match_software() {
        for (a, b) in operand_pairs(2) {
            let want = software::mul(a, b);
            // Dispatched product, its unreduced form, and squaring.
            assert_eq!(a * b, want);
            assert_eq!(a.mul_unreduced(b).reduce(), want);
            assert_eq!(a.square(), software::mul(a, a));
            // A mixed product is a full product by an element with no y part.
            let k = F64(b.c1);
            let want = software::mul(a, F128::from(k));
            assert_eq!(a.mul_base(k), want);
            assert_eq!(a.mul_base_unreduced(k).reduce(), want);
        }
    }

    #[test]
    fn batched_products_match_software() {
        // Four consecutive pairs per batch.
        let pairs = operand_pairs(6);
        for batch in pairs.as_chunks::<4>().0 {
            let a = batch.map(|(a, _)| a);
            let b = batch.map(|(_, b)| b);
            let want: [F128; 4] = std::array::from_fn(|i| software::mul(a[i], b[i]));
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
