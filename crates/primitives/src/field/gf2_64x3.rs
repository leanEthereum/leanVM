//! The extension field `F192 = K[y] / (y^3 + y + 1)` over the base field `K = GF(2^64)`.
//!
//! An element is `c0 + c1*y + c2*y^2`, each coefficient a base-field element.
//! A product runs in three stages:
//!
//! ```text
//!     Karatsuba   6 carry-less 64x64 products  ->  5 coefficients of y^0..y^4, 128 bits each
//!     y-fold      y^3 = y + 1, y^4 = y^2 + y   ->  3 coefficients of y^0..y^2, 128 bits each
//!     reduce      x^64 = x^4 + x^3 + x + 1     ->  3 coefficients of y^0..y^2,  64 bits each
//! ```
//!
//! Both folds are GF(2)-linear, so they commute with XOR.
//! A sum of products therefore accumulates after the y-fold and reduces once.

use core::ops::{Add, AddAssign, BitXor, BitXorAssign, Mul, MulAssign};

use serde::{Deserialize, Serialize};

#[cfg(not(all(target_arch = "x86_64", target_feature = "pclmulqdq")))]
use super::gf2_64::mul_wide;
#[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
use super::gf2_64::square_wide;
use super::gf2_64::{F64, reduce};

/// An element `c0 + c1*y + c2*y^2`; bit `i` of each coefficient is its coefficient of `x^i`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(C)]
pub struct F192 {
    /// The coefficient of `y^0`.
    pub c0: u64,
    /// The coefficient of `y^1`.
    pub c1: u64,
    /// The coefficient of `y^2`.
    pub c2: u64,
}

impl F192 {
    pub const ZERO: Self = Self { c0: 0, c1: 0, c2: 0 };
    pub const ONE: Self = Self { c0: 1, c1: 0, c2: 0 };
    /// The element `y` (root of y^3 + y + 1 over the base field).
    pub const Y: Self = Self { c0: 0, c1: 1, c2: 0 };

    #[inline]
    pub const fn new(c0: u64, c1: u64, c2: u64) -> Self {
        Self { c0, c1, c2 }
    }

    #[inline]
    pub const fn is_zero(self) -> bool {
        self.c0 == 0 && self.c1 == 0 && self.c2 == 0
    }

    /// Product without the base-field reduction, for XOR accumulation.
    #[inline]
    pub fn mul_unreduced(self, rhs: Self) -> F192Unreduced {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            // SAFETY: aes target feature is enabled at compile time.
            unsafe { aarch64::mul_unreduced_neon(self, rhs) }
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
    /// The scalar has no `y` component, so the three coefficients multiply independently in `K`.
    #[inline]
    pub fn mul_base(self, k: F64) -> Self {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            // Each base product keeps its reduction on the NEON side.
            Self {
                c0: (F64(self.c0) * k).0,
                c1: (F64(self.c1) * k).0,
                c2: (F64(self.c2) * k).0,
            }
        }
        #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
        {
            self.mul_base_unreduced(k).reduce()
        }
    }

    /// Mixed product by a base-field scalar without the reduction, for XOR accumulation.
    #[inline]
    pub fn mul_base_unreduced(self, k: F64) -> F192Unreduced {
        #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
        {
            // SAFETY: pclmulqdq is enabled at compile time.
            unsafe { x86_64::mul_base_unreduced(self, k) }
        }
        #[cfg(not(all(target_arch = "x86_64", target_feature = "pclmulqdq")))]
        {
            F192Unreduced::from_wide([self.c0, self.c1, self.c2].map(|c| mul_wide(c, k.0)))
        }
    }

    /// Squaring, with 3 base-field squarings instead of 6 products.
    ///
    /// Cross terms vanish in characteristic 2:
    ///
    /// ```text
    ///     (c0 + c1*y + c2*y^2)^2 = c0^2 + c1^2*y^2 + c2^2*y^4
    ///                            = c0^2 + c2^2*y + (c1^2 + c2^2)*y^2     (y^4 = y^2 + y)
    /// ```
    #[inline]
    pub fn square(self) -> Self {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            // SAFETY: aes target feature is enabled at compile time.
            unsafe { aarch64::square_neon(self) }
        }
        #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
        {
            // Square each coefficient as a 128-bit polynomial.
            let [s0, s1, s2] = [self.c0, self.c1, self.c2].map(square_wide);
            // Fold y^4 back onto y^2 and y, then reduce each coefficient once.
            F192Unreduced::from_wide([s0, s2, s1 ^ s2]).reduce()
        }
    }

    /// The Frobenius `self^(2^64)`. Free: `K` is fixed elementwise, and
    /// `y^(2^64) = y²` (with `y⁴ = y² + y` from `y³ = y + 1`), so
    /// `c0 + c1·y + c2·y² ↦ c0 + c2·y + (c1 + c2)·y²` is a coefficient shuffle
    /// and one XOR.
    #[inline]
    pub const fn frobenius(self) -> Self {
        Self {
            c0: self.c0,
            c1: self.c2,
            c2: self.c1 ^ self.c2,
        }
    }

    /// Multiplicative inverse: `self^(2^192 − 2)`. `ZERO.inv() == ZERO`.
    ///
    /// Via the norm to the base field. With `φ` the Frobenius and
    /// `m = φ(self)·φ²(self)`, the product `self·m` is the norm `N(self) ∈ K`,
    /// so `self⁻¹ = m·N(self)⁻¹` needs two extension multiplies, one base-field
    /// inverse and one base-field scaling. The Fermat ladder it replaces spent
    /// 190 squarings and 190 multiplies, an order of magnitude more.
    pub fn inv(self) -> Self {
        let m = self.frobenius() * self.frobenius().frobenius();
        let norm = self * m;
        debug_assert!(
            (norm.c1, norm.c2) == (0, 0),
            "the norm of an F192 element must lie in K"
        );
        m.mul_base(F64(norm.c0).inv())
    }
}

impl Add for F192 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self {
            c0: self.c0 ^ rhs.c0,
            c1: self.c1 ^ rhs.c1,
            c2: self.c2 ^ rhs.c2,
        }
    }
}

impl AddAssign for F192 {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.c0 ^= rhs.c0;
        self.c1 ^= rhs.c1;
        self.c2 ^= rhs.c2;
    }
}

impl From<F64> for F192 {
    #[inline]
    fn from(k: F64) -> Self {
        Self { c0: k.0, c1: 0, c2: 0 }
    }
}

impl Mul for F192 {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            // SAFETY: aes target feature is enabled at compile time.
            unsafe { aarch64::mul_karatsuba(self, rhs) }
        }
        #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
        {
            self.mul_unreduced(rhs).reduce()
        }
    }
}

impl MulAssign for F192 {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

// Batched products fill the independent lanes exposed by x86 vector instructions.

/// Two independent products.
#[inline(always)]
pub fn mul2(a: [F192; 2], b: [F192; 2]) -> [F192; 2] {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
    // SAFETY: both features are enabled at compile time.
    return unsafe { x86_64::mul_vec2(a, b) };
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2")))]
    [a[0] * b[0], a[1] * b[1]]
}

/// Four independent products.
#[inline(always)]
pub fn mul4(a: [F192; 4], b: [F192; 4]) -> [F192; 4] {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    // SAFETY: both features are enabled at compile time.
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
pub fn mul_unreduced4(a: [F192; 4], b: [F192; 4]) -> [F192Unreduced; 4] {
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

/// An F192 value whose coefficients are not yet reduced modulo the base polynomial.
///
/// Coefficient `k` is the 128-bit carry-less polynomial multiplying `y^k`, for `k < 3`.
/// Products land here already folded by `y^3 = y + 1`, so a sum of them is a plain XOR.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct F192Unreduced {
    /// The 128-bit coefficients of `y^0`, `y^1`, `y^2`, each as its `[low, high]` words.
    ///
    /// Words rather than `u128`, so that accumulation compiles to vector XORs.
    coeffs: [[u64; 2]; 3],
}

impl F192Unreduced {
    pub const ZERO: Self = Self { coeffs: [[0; 2]; 3] };

    /// Build from three 128-bit coefficients.
    #[inline]
    fn from_wide(coeffs: [u128; 3]) -> Self {
        Self {
            coeffs: coeffs.map(|c| [c as u64, (c >> 64) as u64]),
        }
    }

    /// Reduce each coefficient modulo the base polynomial.
    #[inline]
    pub fn reduce(self) -> F192 {
        let [c0, c1, c2] = self
            .coeffs
            .map(|[lo, hi]| reduce(u128::from(hi) << 64 | u128::from(lo)));
        F192 { c0, c1, c2 }
    }
}

impl From<F192> for F192Unreduced {
    /// Embed a reduced element: each coefficient is its own 128-bit polynomial.
    #[inline]
    fn from(e: F192) -> Self {
        Self {
            coeffs: [e.c0, e.c1, e.c2].map(|c| [c, 0]),
        }
    }
}

impl BitXor for F192Unreduced {
    type Output = Self;
    #[inline]
    fn bitxor(mut self, rhs: Self) -> Self {
        self ^= rhs;
        self
    }
}

impl BitXorAssign for F192Unreduced {
    #[inline]
    fn bitxor_assign(&mut self, rhs: Self) {
        for (acc, x) in self.coeffs.as_flattened_mut().iter_mut().zip(rhs.coeffs.as_flattened()) {
            *acc ^= x;
        }
    }
}

// aarch64 + AES: PMULL-based multiplication variants.

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
pub mod aarch64 {
    use super::{F192, F192Unreduced};
    use crate::field::gf2_64::R64;
    use core::arch::aarch64::*;
    use core::mem::transmute;

    /// 64×64 carry-less product as a 128-bit vector.
    ///
    /// # Safety
    /// Requires the `aes` target feature (statically satisfied: every caller
    /// is itself `#[target_feature(enable = "aes")]`).
    #[inline]
    #[target_feature(enable = "aes")]
    unsafe fn pmull(a: u64, b: u64) -> uint64x2_t {
        let prod = vmull_p64(a, b);
        // SAFETY: u128 and uint64x2_t are both 128-bit values; bit-level
        // reinterpret with no UB.
        unsafe { transmute::<u128, uint64x2_t>(prod) }
    }

    /// Fold one 128-bit coefficient into GF(2^64): 2 PMULL by 0x1B, the second
    /// folding the first's ≤4-bit overflow exactly, since `ov·0x1B` fits in 8
    /// bits and lands in lane 0.
    ///
    /// PMULL retires at about the rate `eor` does here, so the second product
    /// is nearly free while the three lane extractions a scalar fold needs are not.
    /// The base field's NEON pair reduction uses the same fold.
    ///
    /// # Safety
    /// Requires the `aes` target feature.
    #[inline]
    #[target_feature(enable = "aes")]
    unsafe fn base_reduce(d: uint64x2_t) -> u64 {
        use crate::field::gf2_64::aarch64::pmull_hi;
        // SAFETY: function carries the aes target feature.
        unsafe {
            let r = vdupq_n_u64(R64);
            let t = pmull_hi(d, r);
            let u = pmull_hi(t, r);
            vgetq_lane_u64::<0>(veorq_u64(veorq_u64(d, t), u))
        }
    }

    /// Karatsuba-3: 6 PMULL products (optimal bilinear count for 3 terms)
    /// combined by NEON XORs into the 5 coefficients of the degree-4 product
    /// over `K`.
    ///
    /// # Safety
    /// Requires the `aes` target feature (compiles to PMULL); only call where
    /// `aes` is statically enabled or has been runtime-detected.
    #[inline]
    #[target_feature(enable = "aes")]
    unsafe fn karatsuba_coeffs(a: F192, b: F192) -> [uint64x2_t; 5] {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let p0 = pmull(a.c0, b.c0);
            let p1 = pmull(a.c1, b.c1);
            let p2 = pmull(a.c2, b.c2);
            let p01 = pmull(a.c0 ^ a.c1, b.c0 ^ b.c1);
            let p02 = pmull(a.c0 ^ a.c2, b.c0 ^ b.c2);
            let p12 = pmull(a.c1 ^ a.c2, b.c1 ^ b.c2);

            // c0 = p0                    c3 = p12 ^ p1 ^ p2
            // c1 = p01 ^ p0 ^ p1         c4 = p2
            // c2 = p02 ^ p0 ^ p1 ^ p2
            let t01 = veorq_u64(p0, p1);
            let t12 = veorq_u64(p1, p2);
            [
                p0,
                veorq_u64(p01, t01),
                veorq_u64(veorq_u64(p02, p0), t12),
                veorq_u64(p12, t12),
                p2,
            ]
        }
    }

    /// The y-fold of the five Karatsuba coefficients: `d0 = c0^c3, d1 = c1^c3^c4, d2 = c2^c4`.
    ///
    /// # Safety
    /// Requires the `aes` target feature.
    #[inline]
    #[target_feature(enable = "aes")]
    unsafe fn karatsuba_folded(a: F192, b: F192) -> [uint64x2_t; 3] {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let [c0, c1, c2, c3, c4] = karatsuba_coeffs(a, b);
            [veorq_u64(c0, c3), veorq_u64(veorq_u64(c1, c3), c4), veorq_u64(c2, c4)]
        }
    }

    /// Karatsuba products, y-fold, then 3 PMULL base reductions. 9 PMULL
    /// total. Default `Mul` implementation.
    ///
    /// # Safety
    /// Requires the `aes` target feature (compiles to PMULL); only call where
    /// `aes` is statically enabled or has been runtime-detected.
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_karatsuba(a: F192, b: F192) -> F192 {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let [d0, d1, d2] = karatsuba_folded(a, b);
            F192 {
                c0: base_reduce(d0),
                c1: base_reduce(d1),
                c2: base_reduce(d2),
            }
        }
    }

    /// Karatsuba products and the y-fold, 6 PMULL, no base reduction.
    /// The caller XOR-accumulates the raw coefficients (inner products, sumcheck-style).
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_karatsuba`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_unreduced_neon(a: F192, b: F192) -> F192Unreduced {
        // SAFETY: function carries the aes target feature; the reinterprets are between 128-bit values.
        unsafe {
            F192Unreduced {
                coeffs: karatsuba_folded(a, b).map(|d| transmute::<uint64x2_t, [u64; 2]>(d)),
            }
        }
    }

    /// Squaring: cross terms vanish, squares land on y^0, y^2, y^4.
    /// 3 PMULL squares + y-fold + 3 PMULL reductions.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_karatsuba`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn square_neon(a: F192) -> F192 {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let s0 = pmull(a.c0, a.c0);
            let s1 = pmull(a.c1, a.c1);
            let s2 = pmull(a.c2, a.c2);
            // (c0 + c1 y + c2 y²)² = s0 + s1 y² + s2 y⁴; y⁴ = y² + y:
            // d0 = s0, d1 = s2, d2 = s1 ^ s2.
            F192 {
                c0: base_reduce(s0),
                c1: base_reduce(s2),
                c2: base_reduce(veorq_u64(s1, s2)),
            }
        }
    }
}

/// x86-64 kernels.
///
/// The carry-less multiplier is the scarce execution unit, so every kernel spends it only on products.
/// Reductions run as shifts and XORs.
/// A single product packs two operand coefficients per register and picks one with the CLMUL immediate:
///
/// ```text
///     register     lo qword     hi qword       imm 0x00    imm 0x11
///     r01          c0           c1             p0          p1
///     s            c0 ^ c2      c1 ^ c2        p02         p12
///     t            c2           c0 ^ c1        p2          p01
/// ```
///
/// The batched kernels instead place one product per 128-bit lane and reduce every lane at once.
#[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
pub mod x86_64 {
    use super::{F192, F192Unreduced};
    use crate::field::gf2_64::F64;
    use core::arch::x86_64::*;
    use core::mem::transmute;

    /// Two 64-bit words as one register, `lo` in the low qword.
    #[inline(always)]
    fn pair(lo: u64, hi: u64) -> __m128i {
        // SAFETY: SSE2 is part of the x86-64 baseline.
        unsafe { _mm_set_epi64x(hi as i64, lo as i64) }
    }

    /// The y-folded Karatsuba product of one pair.
    ///
    /// # Safety
    ///
    /// Requires the `pclmulqdq` target feature.
    #[inline]
    #[target_feature(enable = "pclmulqdq")]
    unsafe fn karatsuba(a: F192, b: F192) -> [__m128i; 3] {
        // Operand registers, as in the module table.
        let (a01, b01) = (pair(a.c0, a.c1), pair(b.c0, b.c1));
        let (at, bt) = (pair(a.c2, a.c0 ^ a.c1), pair(b.c2, b.c0 ^ b.c1));
        // XOR the broadcast c2 into both qwords of r01.
        let a_s = _mm_xor_si128(a01, _mm_unpacklo_epi64(at, at));
        let b_s = _mm_xor_si128(b01, _mm_unpacklo_epi64(bt, bt));
        // The six base products, two per register pair.
        let p0 = _mm_clmulepi64_si128::<0x00>(a01, b01);
        let p1 = _mm_clmulepi64_si128::<0x11>(a01, b01);
        let p02 = _mm_clmulepi64_si128::<0x00>(a_s, b_s);
        let p12 = _mm_clmulepi64_si128::<0x11>(a_s, b_s);
        let p2 = _mm_clmulepi64_si128::<0x00>(at, bt);
        let p01 = _mm_clmulepi64_si128::<0x11>(at, bt);
        fold(p0, p1, p2, p01, p02, p12, |x, y| _mm_xor_si128(x, y))
    }

    /// Karatsuba recombination and y-fold in one step, for any register width.
    ///
    /// Composing the two linear maps leaves a short XOR network:
    ///
    /// ```text
    ///     d0 = p0 ^ p1 ^ p2 ^ p12
    ///     d1 = p0 ^ p01 ^ p12
    ///     d2 = p0 ^ p1 ^ p02
    /// ```
    #[inline(always)]
    fn fold<V: Copy>(p0: V, p1: V, p2: V, p01: V, p02: V, p12: V, xor: impl Fn(V, V) -> V) -> [V; 3] {
        // Shared by d0 and d1.
        let q = xor(p0, p12);
        [xor(xor(q, p1), p2), xor(q, p01), xor(xor(p0, p1), p02)]
    }

    /// One unreduced product.
    ///
    /// # Safety
    ///
    /// Requires the `pclmulqdq` target feature.
    #[inline]
    #[target_feature(enable = "pclmulqdq")]
    pub unsafe fn mul_unreduced(a: F192, b: F192) -> F192Unreduced {
        // SAFETY: the function carries pclmulqdq; the reinterprets are between 128-bit values.
        unsafe {
            F192Unreduced {
                coeffs: karatsuba(a, b).map(|d| transmute::<__m128i, [u64; 2]>(d)),
            }
        }
    }

    /// One unreduced mixed product: three base products from two operand registers.
    ///
    /// # Safety
    ///
    /// Requires the `pclmulqdq` target feature.
    #[inline]
    #[target_feature(enable = "pclmulqdq")]
    pub unsafe fn mul_base_unreduced(a: F192, k: F64) -> F192Unreduced {
        // [c0, c1] and [c2, 0] against [k, 0].
        let a01 = pair(a.c0, a.c1);
        let a2 = _mm_cvtsi64_si128(a.c2 as i64);
        let k = _mm_cvtsi64_si128(k.0 as i64);
        // Immediate 0x01 multiplies the high qword of the first operand by the low qword of the second.
        let products = [
            _mm_clmulepi64_si128::<0x00>(a01, k),
            _mm_clmulepi64_si128::<0x01>(a01, k),
            _mm_clmulepi64_si128::<0x00>(a2, k),
        ];
        // SAFETY: the reinterprets are between 128-bit values.
        unsafe {
            F192Unreduced {
                coeffs: products.map(|p| transmute::<__m128i, [u64; 2]>(p)),
            }
        }
    }

    /// Lane-wise base reduction: qword `i` of the result is the reduction of `hi[i] * x^64 + lo[i]`.
    ///
    /// The same shift network as the scalar reduction, applied to every qword at once.
    ///
    /// # Safety
    ///
    /// Requires the `avx2` target feature.
    #[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx2"))]
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn reduce_lanes256(lo: __m256i, hi: __m256i) -> __m256i {
        // The bits of `hi * 0x1B` shifted past x^63.
        let spill = _mm256_xor_si256(
            _mm256_xor_si256(_mm256_srli_epi64::<63>(hi), _mm256_srli_epi64::<61>(hi)),
            _mm256_srli_epi64::<60>(hi),
        );
        // lo ^ f(hi ^ spill), with f(v) = v ^ v<<1 ^ v<<3 ^ v<<4.
        let v = _mm256_xor_si256(hi, spill);
        let f = _mm256_xor_si256(
            _mm256_xor_si256(v, _mm256_slli_epi64::<1>(v)),
            _mm256_xor_si256(_mm256_slli_epi64::<3>(v), _mm256_slli_epi64::<4>(v)),
        );
        _mm256_xor_si256(lo, f)
    }

    /// Lane-wise base reduction on eight qwords; see the four-qword version.
    ///
    /// # Safety
    ///
    /// Requires the `avx512f` target feature.
    #[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    #[inline]
    #[target_feature(enable = "avx512f")]
    unsafe fn reduce_lanes512(lo: __m512i, hi: __m512i) -> __m512i {
        // The bits of `hi * 0x1B` shifted past x^63.
        let spill = _mm512_xor_si512(
            _mm512_xor_si512(_mm512_srli_epi64::<63>(hi), _mm512_srli_epi64::<61>(hi)),
            _mm512_srli_epi64::<60>(hi),
        );
        // lo ^ f(hi ^ spill), with f(v) = v ^ v<<1 ^ v<<3 ^ v<<4.
        let v = _mm512_xor_si512(hi, spill);
        let f = _mm512_xor_si512(
            _mm512_xor_si512(v, _mm512_slli_epi64::<1>(v)),
            _mm512_xor_si512(_mm512_slli_epi64::<3>(v), _mm512_slli_epi64::<4>(v)),
        );
        _mm512_xor_si512(lo, f)
    }

    /// The y-folded Karatsuba products of two pairs, one pair per 128-bit lane.
    ///
    /// # Safety
    ///
    /// Requires the `vpclmulqdq` and `avx2` target features.
    #[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx2"))]
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx2")]
    unsafe fn karatsuba_vec2(a: [F192; 2], b: [F192; 2]) -> [__m256i; 3] {
        // One coefficient of both elements, in the low qword of each lane.
        let pack = |c: [u64; 2]| _mm256_set_epi64x(0, c[1] as i64, 0, c[0] as i64);
        let (a0, a1, a2) = (pack(a.map(|e| e.c0)), pack(a.map(|e| e.c1)), pack(a.map(|e| e.c2)));
        let (b0, b1, b2) = (pack(b.map(|e| e.c0)), pack(b.map(|e| e.c1)), pack(b.map(|e| e.c2)));
        // One instruction per base product covers both lanes.
        let mul = |x, y| _mm256_clmulepi64_epi128::<0x00>(x, y);
        let xor = |x, y| _mm256_xor_si256(x, y);
        fold(
            mul(a0, b0),
            mul(a1, b1),
            mul(a2, b2),
            mul(xor(a0, a1), xor(b0, b1)),
            mul(xor(a0, a2), xor(b0, b2)),
            mul(xor(a1, a2), xor(b1, b2)),
            xor,
        )
    }

    /// Two independent products in the two 128-bit lanes of a YMM register.
    ///
    /// # Safety
    ///
    /// Requires the `vpclmulqdq` and `avx2` target features.
    #[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx2"))]
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx2")]
    pub unsafe fn mul_vec2(a: [F192; 2], b: [F192; 2]) -> [F192; 2] {
        // SAFETY: the function carries both features.
        unsafe {
            let [d0, d1, d2] = karatsuba_vec2(a, b);
            // Lane i of c01 is [c0_i, c1_i]; the low qword of lane i of c2 is c2_i.
            let c01 = reduce_lanes256(_mm256_unpacklo_epi64(d0, d1), _mm256_unpackhi_epi64(d0, d1));
            let c2 = reduce_lanes256(d2, _mm256_unpackhi_epi64(d2, d2));
            let (w01, w2) = (transmute::<__m256i, [u64; 4]>(c01), transmute::<__m256i, [u64; 4]>(c2));
            std::array::from_fn(|i| F192::new(w01[2 * i], w01[2 * i + 1], w2[2 * i]))
        }
    }

    /// Two independent unreduced products, packed as for the reduced version.
    ///
    /// # Safety
    ///
    /// Requires the `vpclmulqdq` and `avx2` target features.
    #[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx2"))]
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx2")]
    pub unsafe fn mul_unreduced_vec2(a: [F192; 2], b: [F192; 2]) -> [F192Unreduced; 2] {
        // SAFETY: the function carries both features; lane i of each register is one coefficient.
        unsafe {
            let d = karatsuba_vec2(a, b).map(|d| transmute::<__m256i, [[u64; 2]; 2]>(d));
            std::array::from_fn(|i| F192Unreduced {
                coeffs: [d[0][i], d[1][i], d[2][i]],
            })
        }
    }

    /// The y-folded Karatsuba products of four pairs, one pair per 128-bit lane.
    ///
    /// # Safety
    ///
    /// Requires the `vpclmulqdq` and `avx512f` target features.
    #[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
    unsafe fn karatsuba_vec4(a: [F192; 4], b: [F192; 4]) -> [__m512i; 3] {
        // One coefficient of all four elements, in the low qword of each lane.
        let pack = |c: [u64; 4]| _mm512_set_epi64(0, c[3] as i64, 0, c[2] as i64, 0, c[1] as i64, 0, c[0] as i64);
        let (a0, a1, a2) = (pack(a.map(|e| e.c0)), pack(a.map(|e| e.c1)), pack(a.map(|e| e.c2)));
        let (b0, b1, b2) = (pack(b.map(|e| e.c0)), pack(b.map(|e| e.c1)), pack(b.map(|e| e.c2)));
        // One instruction per base product covers all four lanes.
        let mul = |x, y| _mm512_clmulepi64_epi128::<0x00>(x, y);
        let xor = |x, y| _mm512_xor_si512(x, y);
        fold(
            mul(a0, b0),
            mul(a1, b1),
            mul(a2, b2),
            mul(xor(a0, a1), xor(b0, b1)),
            mul(xor(a0, a2), xor(b0, b2)),
            mul(xor(a1, a2), xor(b1, b2)),
            xor,
        )
    }

    /// Four independent products in the four 128-bit lanes of a ZMM register.
    ///
    /// # Safety
    ///
    /// Requires the `vpclmulqdq` and `avx512f` target features.
    #[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
    pub unsafe fn mul_vec4(a: [F192; 4], b: [F192; 4]) -> [F192; 4] {
        // SAFETY: the function carries both features.
        unsafe {
            let [d0, d1, d2] = karatsuba_vec4(a, b);
            // Lane i of c01 is [c0_i, c1_i]; the low qword of lane i of c2 is c2_i.
            let c01 = reduce_lanes512(_mm512_unpacklo_epi64(d0, d1), _mm512_unpackhi_epi64(d0, d1));
            let c2 = reduce_lanes512(d2, _mm512_unpackhi_epi64(d2, d2));
            let (w01, w2) = (transmute::<__m512i, [u64; 8]>(c01), transmute::<__m512i, [u64; 8]>(c2));
            std::array::from_fn(|i| F192::new(w01[2 * i], w01[2 * i + 1], w2[2 * i]))
        }
    }

    /// Four independent unreduced products, packed as for the reduced version.
    ///
    /// # Safety
    ///
    /// Requires the `vpclmulqdq` and `avx512f` target features.
    #[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
    pub unsafe fn mul_unreduced_vec4(a: [F192; 4], b: [F192; 4]) -> [F192Unreduced; 4] {
        // SAFETY: the function carries both features; lane i of each register is one coefficient.
        unsafe {
            let d = karatsuba_vec4(a, b).map(|d| transmute::<__m512i, [[u64; 2]; 4]>(d));
            std::array::from_fn(|i| F192Unreduced {
                coeffs: [d[0][i], d[1][i], d[2][i]],
            })
        }
    }
}

/// Portable fallback, and the reference every accelerated path is tested against.
pub mod software {
    use super::{F192, F192Unreduced};
    use crate::field::gf2_64::software::clmul;

    /// Schoolbook: nine base products into the five coefficients of y^0..y^4, then the y-fold.
    pub fn mul_unreduced(a: F192, b: F192) -> F192Unreduced {
        let (a, b) = ([a.c0, a.c1, a.c2], [b.c0, b.c1, b.c2]);
        let mut e = [0u128; 5];
        // a_i * b_j lands on y^(i + j).
        for i in 0..3 {
            for j in 0..3 {
                e[i + j] ^= clmul(a[i], b[j]);
            }
        }
        // y^3 = y + 1 and y^4 = y^2 + y.
        F192Unreduced::from_wide([e[0] ^ e[3], e[1] ^ e[3] ^ e[4], e[2] ^ e[4]])
    }

    pub fn mul(a: F192, b: F192) -> F192 {
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

    /// Vectors generated by an independent Python implementation
    /// (scratchpad/fieldref.py): (a, b, a·b, a·a).
    type ReferenceVector = ([u64; 3], [u64; 3], [u64; 3], [u64; 3]);
    const VECTORS: [ReferenceVector; 4] = [
        (
            [0x950e87d7f5606615, 0x2c61275c9e6b6cf8, 0x1f00bca0042db923],
            [0x6dbca290a9eab706, 0x4c10a4fe30cffdda, 0xf26fff4cc4fd394d],
            [0x888a0fc35abaf5f6, 0x68a84cbc132b0649, 0x9fdeaf613003cabe],
            [0x8fba131ad5d46b8c, 0x1c170457f537a805, 0x3632cc098ca15135],
        ),
        (
            [0x6814a2bc786a6d2d, 0xa26b351e6c8042c5, 0x54760e7fbc051c6c],
            [0xd4c08880a5a4666d, 0x29610ae0eed8f1e7, 0xc34bd8e2fe5213e5],
            [0x2ad322ebf2f9043b, 0x8ac800aa67154c80, 0x6d0f76651d3c4d0c],
            [0xcf800ef2b83bb43a, 0xefe1c6cd064dd44c, 0x57dc5c7a60e2981b],
        ),
        (
            [0x6c50afb6e9fb123d, 0x6f28d015a2aa0b9d, 0x4e385994ebac94af],
            [0x194f9545adba52ce, 0xc675ce05588f882f, 0x57de8c051d4b7ef2],
            [0xea6b9f9d23d4a1ff, 0xd82aa6058c431457, 0x5fd4d8fda2f1e74a],
            [0x8f30fe43aa05b396, 0xe3593591eccd9efe, 0x7c5a1b128788c51f],
        ),
        (
            [0xd998efd82733e933, 0x6df216c33f8f3201, 0x11dc6f3fcb57d5d8],
            [0x8860a84722025e05, 0x33176469aa6ef630, 0x607507ebc5b864d7],
            [0xfa3a0d66cdfbc1b3, 0xbd47bd3343aad307, 0xdaf50186477f6a77],
            [0x69c8d8c24f416884, 0x4b597d648a162147, 0x95603a5d95c9512a],
        ),
    ];

    /// Elements whose products drive every reduction spill: all-ones, top bits only, identities.
    const CORNERS: [F192; 5] = [
        F192::ZERO,
        F192::ONE,
        F192::Y,
        F192::new(u64::MAX, u64::MAX, u64::MAX),
        F192::new(1 << 63, 1 << 63, 1 << 63),
    ];

    /// Random pairs followed by every pair of corners.
    fn operand_pairs(seed: u64) -> Vec<(F192, F192)> {
        let mut rng = Rng::new(seed);
        let random = (0..10_000).map(|_| (rng.ext(), rng.ext()));
        let corners = CORNERS.iter().flat_map(|&a| CORNERS.iter().map(move |&b| (a, b)));
        random.chain(corners).collect()
    }

    #[test]
    fn python_vectors_and_modulus() {
        for (a, b, c, s) in VECTORS {
            let (a, b) = (F192::new(a[0], a[1], a[2]), F192::new(b[0], b[1], b[2]));
            assert_eq!(a * b, F192::new(c[0], c[1], c[2]));
            assert_eq!(a.square(), F192::new(s[0], s[1], s[2]));
            assert_eq!(software::mul(a, b), F192::new(c[0], c[1], c[2]));
        }
        assert_eq!(F192::Y * F192::Y * F192::Y, F192::Y + F192::ONE);
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
            let want = software::mul(a, F192::from(k));
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
            let want: [F192; 4] = std::array::from_fn(|i| software::mul(a[i], b[i]));
            assert_eq!(mul4(a, b), want);
            assert_eq!(mul_unreduced4(a, b).map(F192Unreduced::reduce), want);
            assert_eq!(mul2([a[0], a[1]], [b[0], b[1]]), [want[0], want[1]]);
        }
    }

    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    #[test]
    fn neon_variants_match_software() {
        for (a, b) in operand_pairs(3) {
            let want = software::mul(a, b);
            // SAFETY: cfg-gated on the aes target feature.
            unsafe {
                assert_eq!(aarch64::mul_karatsuba(a, b), want);
                assert_eq!(aarch64::mul_unreduced_neon(a, b).reduce(), want);
                assert_eq!(aarch64::square_neon(a), software::mul(a, a));
            }
        }
    }

    #[test]
    fn square_and_inv() {
        let mut rng = Rng::new(4);
        for _ in 0..1000 {
            let a = rng.ext();
            assert_eq!(a.square(), a * a);
            if !a.is_zero() {
                assert_eq!(a * a.inv(), F192::ONE);
            }
            // K-valued and y-free elements are the cases `inv`'s norm path is
            // most likely to get wrong, and the interpreter's MUL back-solve
            // inverts K-valued words exclusively.
            let k = F192::new(rng.ext().c0, 0, 0);
            if !k.is_zero() {
                assert_eq!(k * k.inv(), F192::ONE);
                assert_eq!(k.inv(), F192::from(F64(k.c0).inv()));
            }
        }
        assert_eq!(F192::ZERO.inv(), F192::ZERO);
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
            // Three applications return the element (Gal(F192/K) has order 3),
            // and the norm a·φ(a)·φ²(a) lands in K.
            assert_eq!(a.frobenius().frobenius().frobenius(), a);
            let n = a * a.frobenius() * a.frobenius().frobenius();
            assert_eq!((n.c1, n.c2), (0, 0));
        }
    }

    #[test]
    fn unreduced_accumulation_matches_reduced_sum() {
        let mut rng = Rng::new(5);
        for _ in 0..100 {
            // Start from an embedded element: its unreduced form reduces to itself.
            let start = rng.ext();
            let mut acc = F192Unreduced::from(start);
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

    // K[y] gcd for the extension-polynomial irreducibility test.

    fn pdeg(p: &[u64]) -> Option<usize> {
        p.iter().rposition(|&c| c != 0)
    }

    fn poly_mod(mut a: Vec<u64>, b: &[u64]) -> Vec<u64> {
        let db = pdeg(b).expect("mod by zero poly");
        let lead_inv = F64(b[db]).inv();
        while let Some(da) = pdeg(&a) {
            if da < db {
                break;
            }
            let q = F64(a[da]) * lead_inv;
            for i in 0..=db {
                a[da - db + i] ^= (q * F64(b[i])).0;
            }
        }
        a
    }

    fn poly_gcd(mut a: Vec<u64>, mut b: Vec<u64>) -> Vec<u64> {
        while pdeg(&b).is_some() {
            let r = poly_mod(a, &b);
            a = b;
            b = r;
        }
        a
    }

    /// Checks `gcd(y^|K| - y, y^3+y+1) = 1`; computes `y^(2^64)` by 64
    /// squarings.
    #[test]
    fn extension_poly_irreducible_over_base() {
        let mut t = F192::Y;
        for _ in 0..64 {
            t = t.square();
        }
        let d = t + F192::Y; // y^(2^64) − y as a deg ≤ 2 poly over K
        assert!(!d.is_zero());
        let f = vec![1u64, 1, 0, 1]; // y^3 + y + 1
        let g = poly_gcd(f, vec![d.c0, d.c1, d.c2]);
        assert_eq!(pdeg(&g), Some(0), "y^3+y+1 has a root in GF(2^64)");
    }
}
