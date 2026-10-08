//! The extension field `F192 = K[y] / (y^3 + y + 1)` over the base field `K = GF(2^64)`.
//!
//! An element is `c0 + c1*y + c2*y^2`, each coefficient a base-field element.
//! A product runs in three stages:
//!
//! ```text
//!     products    carry-less 64x64 products    ->  5 coefficients of y^0..y^4, 128 bits each
//!     y-fold      y^3 = y + 1, y^4 = y^2 + y   ->  3 coefficients of y^0..y^2, 128 bits each
//!     reduce      x^64 = x^4 + x^3 + x + 1     ->  3 coefficients of y^0..y^2,  64 bits each
//! ```
//!
//! x86 spends 6 products on Karatsuba.
//! aarch64 spends 9 on the schoolbook, since there a product costs no more than an XOR.
//!
//! Both folds are GF(2)-linear, so they commute with XOR.
//! A sum of products therefore accumulates after the y-fold and reduces once.

use super::gf2_64::F64;
#[cfg(not(any(
    all(target_arch = "aarch64", target_feature = "aes"),
    all(target_arch = "x86_64", target_feature = "pclmulqdq")
)))]
use super::gf2_64::mul_wide;
#[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
use super::gf2_64::{reduce, square_wide};
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
use core::mem::MaybeUninit;
use core::ops::{Add, AddAssign, BitXor, BitXorAssign, Mul, MulAssign};
use serde::{Deserialize, Serialize};

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
    /// The scalar has no `y` component, so the three coefficients multiply independently in `K`.
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
    pub fn mul_base_unreduced(self, k: F64) -> F192Unreduced {
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
            aarch64::square(self)
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
            aarch64::mul(self, rhs)
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

/// Eight mixed products `t * k[i]` by one shared `E` scalar.
///
/// On AVX-512 this is six CLMULs for all eight, against twenty-four one at a time.
#[inline(always)]
pub fn mul_base8(t: F192, k: [F64; 8]) -> [F192; 8] {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    // SAFETY: both features are enabled at compile time.
    return unsafe { x86_64::mul_base8(t, k) };
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
    k.map(|k| t.mul_base(k))
}

/// Eight sums of mixed products, `sum_t t_t * k_t[i]` for each `i < 8`, every `t_t` shared by the eight.
///
/// A term costs six CLMULs for all eight sums on AVX-512, twelve on AVX2 (two sums per 128-bit
/// lane either way), and the eight reduce together once. Only with VPCLMULQDQ: elsewhere a caller
/// sums each row's [`F192::mul_base_unreduced`] products itself.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
#[derive(Clone, Copy)]
pub struct MixedSums8 {
    acc: x86_64::MixedAcc8,
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
impl Default for MixedSums8 {
    #[inline(always)]
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
impl MixedSums8 {
    /// Eight empty sums.
    #[inline(always)]
    pub const fn new() -> Self {
        Self {
            // SAFETY: every register is plain bits, and all-zero ones are the empty sums.
            acc: unsafe { core::mem::zeroed() },
        }
    }

    /// Add `t * k[i]` to sum `i`.
    #[inline(always)]
    pub fn add(&mut self, t: F192, k: [F64; 8]) {
        // SAFETY: both features are enabled at compile time.
        unsafe { x86_64::mul_base8_add(&mut self.acc, t, k) }
    }

    /// The eight sums.
    #[inline(always)]
    pub fn reduce(self) -> [F192; 8] {
        // SAFETY: both features are enabled at compile time.
        unsafe { x86_64::mul_base8_reduce(self.acc) }
    }
}

/// Four independent elements with lane-wise arithmetic, for a computation run on four
/// inputs at once whose intermediate values stay in registers.
///
/// Element `i` is 128-bit lane `i` of two registers, `[c0, c1]` and `[c2, c2]` (on AVX2, of two
/// pairs of registers, elements 0 and 1 in the first): a product reads its operands where they
/// are and leaves its result in the same form, so nothing crosses a lane between products, where
/// [`mul4`] packs its operands from scalars and unpacks its results on every call. Only with
/// VPCLMULQDQ: elsewhere a caller batches its products with [`mul4`].
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
#[derive(Clone, Copy)]
pub struct F192x4 {
    lanes: x86_64::Lanes4,
}

/// Four unreduced products, lane-wise, for XOR accumulation.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
#[derive(Clone, Copy)]
pub struct F192x4Unreduced {
    lanes: x86_64::Wide4,
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
impl F192x4 {
    #[inline(always)]
    pub fn new(v: [F192; 4]) -> Self {
        Self {
            // SAFETY: both features are enabled at compile time.
            lanes: unsafe { x86_64::lanes4(v) },
        }
    }

    /// `v` in every lane.
    #[inline(always)]
    pub fn splat(v: F192) -> Self {
        Self::new([v; 4])
    }

    #[inline(always)]
    pub fn to_array(self) -> [F192; 4] {
        let mut out = [MaybeUninit::uninit(); 4];
        self.store(&mut out);
        // SAFETY: `store` wrote all four.
        out.map(|v| unsafe { v.assume_init() })
    }

    /// Four consecutive elements in memory, element `i` to lane `i`.
    ///
    /// From memory rather than by value: two loads and two permutes, where
    /// [`new`](Self::new) inserts twelve words one at a time.
    #[inline(always)]
    pub fn load(v: &[F192; 4]) -> Self {
        Self {
            // SAFETY: both features are enabled at compile time; `v` is twelve words.
            lanes: unsafe { x86_64::load_lanes4(v) },
        }
    }

    /// Lane `i` to `out[i]`, the inverse of [`load`](Self::load). The slots need not be
    /// initialized: a staging buffer is written here before it is read.
    #[inline(always)]
    pub fn store(self, out: &mut [MaybeUninit<F192>; 4]) {
        // SAFETY: both features are enabled at compile time; `out` is twelve words.
        unsafe { x86_64::store_lanes4(self.lanes, out) }
    }

    /// Lane `j` of `out[i]` is lane `i` of `rows[j]`.
    #[inline(always)]
    pub fn transpose(rows: [Self; 4]) -> [Self; 4] {
        // SAFETY: both features are enabled at compile time.
        unsafe { x86_64::transpose_lanes4(rows.map(|r| r.lanes)) }.map(|lanes| Self { lanes })
    }

    /// The lane-wise products without the reduction.
    #[inline(always)]
    pub fn mul_unreduced(self, rhs: Self) -> F192x4Unreduced {
        F192x4Unreduced {
            // SAFETY: both features are enabled at compile time.
            lanes: unsafe { x86_64::mul_lanes4(self.lanes, rhs.lanes) },
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
impl Add for F192x4 {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        Self {
            // SAFETY: both features are enabled at compile time.
            lanes: unsafe { x86_64::xor_lanes(self.lanes, rhs.lanes) },
        }
    }
}

/// The lane-wise products, reduced and in lanes again.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
impl Mul for F192x4 {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self {
        Self {
            // SAFETY: both features are enabled at compile time.
            lanes: unsafe { x86_64::reduce_lanes4(x86_64::mul_lanes4(self.lanes, rhs.lanes)) },
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
impl F192x4Unreduced {
    #[inline(always)]
    pub const fn zero() -> Self {
        Self {
            // SAFETY: every register is plain bits, and all-zero ones are the zero products.
            lanes: unsafe { core::mem::zeroed() },
        }
    }

    /// The four lanes' sum.
    #[inline(always)]
    pub fn sum(self) -> F192Unreduced {
        // SAFETY: both features are enabled at compile time.
        unsafe { x86_64::sum_lanes4(self.lanes) }
    }

    /// The lane-wise reductions.
    #[inline(always)]
    pub fn reduce(self) -> F192x4 {
        F192x4 {
            // SAFETY: both features are enabled at compile time.
            lanes: unsafe { x86_64::reduce_lanes4(self.lanes) },
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
impl BitXorAssign for F192x4Unreduced {
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: Self) {
        // SAFETY: both features are enabled at compile time.
        self.lanes = unsafe { x86_64::xor_lanes(self.lanes, rhs.lanes) };
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
impl BitXor for F192x4Unreduced {
    type Output = Self;
    #[inline(always)]
    fn bitxor(mut self, rhs: Self) -> Self {
        self ^= rhs;
        self
    }
}

/// Eight `E` weights, laid out once for [`dot_base`].
///
/// Pairs share a 128-bit lane, so the kernel loads them with no shuffle:
///
/// ```text
///     lo  lane j = [w_2j.c0,   w_2j.c1  ]
///     hi  lane j = [w_2j+1.c0, w_2j+1.c1]
///     c2  lane j = [w_2j.c2,   w_2j+1.c2]
/// ```
#[derive(Clone, Copy, Debug, Default)]
#[repr(C, align(64))]
pub struct Weights8 {
    lo: [u64; 8],
    hi: [u64; 8],
    c2: [u64; 8],
}

impl Weights8 {
    /// Pack eight weights.
    pub fn new(w: &[F192; 8]) -> Self {
        let mut out = Self::default();
        for j in 0..4 {
            let (e, o) = (w[2 * j], w[2 * j + 1]);
            out.lo[2 * j..2 * j + 2].copy_from_slice(&[e.c0, e.c1]);
            out.hi[2 * j..2 * j + 2].copy_from_slice(&[o.c0, o.c1]);
            out.c2[2 * j..2 * j + 2].copy_from_slice(&[e.c2, o.c2]);
        }
        out
    }

    /// Weight `i`, unpacked.
    #[inline]
    pub const fn get(&self, i: usize) -> F192 {
        let j = i / 2;
        let pair = if i.is_multiple_of(2) { &self.lo } else { &self.hi };
        F192::new(pair[2 * j], pair[2 * j + 1], self.c2[2 * j + i % 2])
    }
}

/// The mixed inner product `sum_i w_i * k_i`, unreduced.
///
/// `k.len()` must be `8 * w.len()`.
///
/// On AVX-512 the sums stay in three registers for the whole slice: six CLMULs per eight terms.
#[inline]
pub fn dot_base(w: &[Weights8], k: &[F64]) -> F192Unreduced {
    assert_eq!(k.len(), 8 * w.len());
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    // SAFETY: both features are enabled at compile time; the lengths match.
    return unsafe { x86_64::dot_base(w, k) };
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
    w.iter()
        .zip(k.as_chunks::<8>().0)
        .fold(F192Unreduced::ZERO, |acc, (w, k)| {
            (0..8).fold(acc, |acc, i| acc ^ w.get(i).mul_base_unreduced(k[i]))
        })
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
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            aarch64::reduce(self)
        }
        #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
        {
            let [c0, c1, c2] = self
                .coeffs
                .map(|[lo, hi]| reduce(u128::from(hi) << 64 | u128::from(lo)));
            F192 { c0, c1, c2 }
        }
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

/// aarch64 kernels.
///
/// On Apple cores a carry-less multiply issues as fast as an XOR.
/// So these kernels trade shuffles for products, and reduce with two more products.
///
/// Moving a word between the integer and SIMD register files is slower than a product.
/// So every operand stays in SIMD registers from load to store.
///
/// An element sits in two registers:
///
/// ```text
///     register     lo qword     hi qword
///     c01          c0           c1
///     c22          c2           c2
/// ```
///
/// A product then reads any coefficient pair with the low-lane or high-lane multiply.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
pub mod aarch64;

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
pub mod x86_64;

/// Portable fallback, and the reference every accelerated path is tested against.
pub mod software;

// Tests: every backend against the software reference, independent Python vectors, field axioms,
// and computational irreducibility proofs for both moduli.

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::gf2_64::R64;
    use crate::test_util::Rng;
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    use aarch64::{F192x1, F192x1Unreduced};
    #[cfg(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(target_arch = "x86_64", target_feature = "pclmulqdq")
    ))]
    use core::mem::MaybeUninit;
    #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
    use x86_64::{F192x1, F192x1Unreduced};

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

    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
    #[test]
    fn lane_products_match_software() {
        let pairs = operand_pairs(11);
        // Padded to whole batches, so the last corner pair is tested too.
        let pairs = [
            pairs.as_slice(),
            &pairs[..pairs.len().next_multiple_of(4) - pairs.len()],
        ]
        .concat();
        for batch in pairs.as_chunks::<4>().0 {
            let a = batch.map(|(a, _)| a);
            let b = batch.map(|(_, b)| b);
            let want: [F192; 4] = std::array::from_fn(|i| software::mul(a[i], b[i]));
            let (a4, b4) = (F192x4::new(a), F192x4::new(b));
            assert_eq!(a4.to_array(), a);
            assert_eq!(F192x4::load(&a).to_array(), a);
            let rows = [a, b, want, a].map(F192x4::new);
            let columns = F192x4::transpose(rows).map(F192x4::to_array);
            let rows = rows.map(F192x4::to_array);
            assert!((0..4).all(|i| (0..4).all(|j| columns[i][j] == rows[j][i])));
            assert_eq!(a4.mul(b4).to_array(), want);
            assert_eq!((a4 + b4).to_array(), std::array::from_fn(|i| a[i] + b[i]));
            let mut acc = F192x4Unreduced::zero();
            acc ^= a4.mul_unreduced(b4);
            acc ^= F192x4::splat(a[0]).mul_unreduced(b4);
            let sum = (0..4).fold(F192::ZERO, |s, i| s + want[i] + software::mul(a[0], b[i]));
            assert_eq!(acc.sum().reduce(), sum);
        }
    }

    /// Sums, products, unreduced sums and the loads and stores of elements held in registers,
    /// every corner pair among the operands, and each corner's words as base-field scalars.
    #[cfg(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(target_arch = "x86_64", target_feature = "pclmulqdq")
    ))]
    #[test]
    fn register_products_match_software() {
        for (a, b) in operand_pairs(12) {
            let (a1, b1) = (F192x1::load(&a), F192x1::new(b));
            assert_eq!(F192::from(a1 * b1), software::mul(a, b));
            assert_eq!(F192::from(a1 + b1), a + b);
            let mut acc = F192x1Unreduced::zero();
            acc ^= a1.mul_unreduced(b1);
            acc ^= b1.mul_base_unreduced(F64(a.c2));
            let want = software::mul(a, b) + software::mul(b, F192::from(F64(a.c2)));
            assert_eq!(F192::from(acc.reduce()), want);
            assert_eq!(F192Unreduced::from(acc).reduce(), want);
            let mut out = MaybeUninit::uninit();
            a1.store(&mut out);
            // SAFETY: `store` wrote it.
            assert_eq!(unsafe { out.assume_init() }, a);
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

    #[test]
    fn batched_mixed_products_match_scalar() {
        let mut rng = Rng::new(9);
        for _ in 0..200 {
            let t = rng.ext();
            // Edge scalars sit next to random ones, so every lane sees a zero and an all-ones word.
            let mut k: [F64; 8] = std::array::from_fn(|_| F64(rng.ext().c0));
            k[1] = F64(0);
            k[6] = F64(u64::MAX);
            assert_eq!(mul_base8(t, k), k.map(|k| t.mul_base(k)));

            let w: [F192; 16] = std::array::from_fn(|_| rng.ext());
            let packed = [
                Weights8::new(w[..8].try_into().unwrap()),
                Weights8::new(w[8..].try_into().unwrap()),
            ];
            assert!((0..16).all(|i| packed[i / 8].get(i % 8) == w[i]));
            let k: [F64; 16] = std::array::from_fn(|_| F64(rng.ext().c0));
            let want = (0..16).fold(F192::ZERO, |acc, i| acc + w[i].mul_base(k[i]));
            assert_eq!(dot_base(&packed, &k).reduce(), want);
        }
    }

    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
    #[test]
    fn mixed_sums_match_software() {
        let mut rng = Rng::new(10);
        for _ in 0..200 {
            // A zero and an all-ones word in every term, a corner coefficient in the first.
            let terms: [(F192, [F64; 8]); 3] = std::array::from_fn(|i| {
                let t = if i == 0 {
                    CORNERS[rng.next_u64() as usize % CORNERS.len()]
                } else {
                    rng.ext()
                };
                let mut k: [F64; 8] = std::array::from_fn(|_| F64(rng.next_u64()));
                k[i] = F64(0);
                k[7 - i] = F64(u64::MAX);
                (t, k)
            });
            let mut sums = MixedSums8::new();
            for (t, k) in terms {
                sums.add(t, k);
            }
            let want: [F192; 8] = std::array::from_fn(|i| {
                terms
                    .iter()
                    .fold(F192::ZERO, |acc, (t, k)| acc + software::mul(*t, F192::from(k[i])))
            });
            assert_eq!(sums.reduce(), want);
        }
    }

    /// The planar AVX-512 kernels: eight lane-wise sums and products, and an unreduced sum of products.
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    #[test]
    fn planar_products_match_software() {
        use core::arch::x86_64::__m512i;
        use core::mem::transmute;
        use x86_64::{F192x8, F192x8Sum};
        // Qword `l` of plane `k` is coefficient `k` of element `l`.
        let planes = |e: [F192; 8]| {
            let plane = |k: fn(&F192) -> u64| {
                // SAFETY: eight words and a 512-bit register have the same size and no invalid values.
                unsafe { transmute::<[u64; 8], __m512i>(e.each_ref().map(k)) }
            };
            F192x8([plane(|e| e.c0), plane(|e| e.c1), plane(|e| e.c2)])
        };
        let elements = |p: F192x8| {
            // SAFETY: as above.
            let [c0, c1, c2] = p.0.map(|plane| unsafe { transmute::<__m512i, [u64; 8]>(plane) });
            std::array::from_fn::<F192, 8, _>(|l| F192::new(c0[l], c1[l], c2[l]))
        };
        let pairs = operand_pairs(13);
        // Padded to whole batches, so the last corner pairs are tested too.
        let pairs = [
            pairs.as_slice(),
            &pairs[..pairs.len().next_multiple_of(8) - pairs.len()],
        ]
        .concat();
        for batch in pairs.as_chunks::<8>().0 {
            let (a, b) = (batch.map(|(a, _)| a), batch.map(|(_, b)| b));
            let want: [F192; 8] = std::array::from_fn(|i| software::mul(a[i], b[i]));
            let (a8, b8) = (planes(a), planes(b));
            // SAFETY: the kernels' target features are enabled at compile time.
            let (product, sum, total) = unsafe {
                let mut sum = F192x8Sum::zero();
                sum.mul_add(a8, b8);
                sum.mul_add(b8, a8.add(b8));
                (a8.mul(b8), a8.add(b8), sum.total())
            };
            assert_eq!(elements(product), want);
            assert_eq!(elements(sum), std::array::from_fn(|i| a[i] + b[i]));
            let want_total = (0..8).fold(F192::ZERO, |s, i| s + want[i] + software::mul(b[i], a[i] + b[i]));
            assert_eq!(total.reduce(), want_total);
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
