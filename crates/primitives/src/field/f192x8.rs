//! Eight-element `F192` kernels that never move a word through an integer register.
//!
//! On AVX-512 the eight elements live in three plane registers, the [`Weights8`](super::Weights8) layout:
//!
//! ```text
//!     lo  lane j = [c0, c1] of element 2j        hi  lane j = [c0, c1] of element 2j+1
//!     c2  qword i = c2 of element i
//! ```
//!
//! A kernel loads its operands straight from memory, so it must only read values stored before the
//! current loop iteration: a 512-bit load over a word just stored stalls on the store buffer.
//!
//! Products accumulate unreduced in [`Acc8`], one reduction per sum rather than per term.

use super::gf2_64::F64;
use super::gf2_64x3::{F192, F192Unreduced};

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
pub use avx512::{Acc8, F64x8, F192x8};
#[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
pub use portable::{Acc8, F64x8, F192x8, Prod8};

/// The unreduced products of eight elements, lane by lane: what [`F192x8::mul_unreduced`] returns.
/// A sum of them is an XOR, and [`Prod8::reduce_lanes`] reduces each lane on its own.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
pub type Prod8 = Acc8;

/// The eight-lane types on a target without the wide multiplier.
#[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
mod portable {
    use super::{F64, F192, F192Unreduced};
    use crate::field::gf2_64x3::{mul_unreduced4, mul4};

    /// The two quads of eight lanes. Straight-line, so a product's halves stay in registers:
    /// an `array::map` over the halves is not inlined and passes both through memory.
    #[inline(always)]
    fn halves<T: Copy>(x: &[T; 8]) -> ([T; 4], [T; 4]) {
        ([x[0], x[1], x[2], x[3]], [x[4], x[5], x[6], x[7]])
    }

    #[inline(always)]
    fn join<T: Copy>(a: [T; 4], b: [T; 4]) -> [T; 8] {
        [a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3]]
    }

    /// The even lanes of `a` then of `b`, and the odd ones.
    fn even_odd<T: Copy>(a: &[T; 8], b: &[T; 8]) -> ([T; 8], [T; 8]) {
        let pick = |parity: usize| {
            core::array::from_fn(|i| {
                if i < 4 {
                    a[2 * i + parity]
                } else {
                    b[2 * (i - 4) + parity]
                }
            })
        };
        (pick(0), pick(1))
    }

    /// The 8x8 transpose: element `j` of `out[p]` is element `p` of `g[j]`.
    fn transpose<T: Copy>(g: [[T; 8]; 8]) -> [[T; 8]; 8] {
        core::array::from_fn(|p| core::array::from_fn(|j| g[j][p]))
    }

    /// Eight elements, on a target without the wide multiplier. Line-aligned, so that an
    /// array of them is still published by the streaming stores where those exist.
    #[derive(Clone, Copy, Debug)]
    #[repr(C, align(64))]
    pub struct F192x8([F192; 8]);

    // SAFETY: one field, an array of plain elements.
    unsafe impl crate::Plain for F192x8 {}

    impl F192x8 {
        pub const ZERO: Self = Self([F192::ZERO; 8]);
        pub const ONE: Self = Self([F192::ONE; 8]);

        #[inline]
        pub fn splat(r: F192) -> Self {
            Self([r; 8])
        }

        #[inline]
        pub fn from_array(e: &[F192; 8]) -> Self {
            Self(*e)
        }

        #[inline]
        pub fn to_array(self) -> [F192; 8] {
            self.0
        }

        #[inline]
        pub fn lane(&self, i: usize) -> F192 {
            self.0[i]
        }

        #[inline]
        pub fn set_lane(&mut self, i: usize, e: F192) {
            self.0[i] = e;
        }

        #[inline(always)]
        pub fn mul_unreduced(self, rhs: Self) -> Prod8 {
            let ((x0, x1), (y0, y1)) = (halves(&self.0), halves(&rhs.0));
            Prod8(join(mul_unreduced4(x0, y0), mul_unreduced4(x1, y1)))
        }

        /// `([a0, a2, a4, a6, b0, b2, b4, b6], [a1, a3, a5, a7, b1, b3, b5, b7])`.
        #[inline]
        pub fn even_odd(a: Self, b: Self) -> (Self, Self) {
            let (even, odd) = even_odd(&a.0, &b.0);
            (Self(even), Self(odd))
        }

        /// The 8x8 transpose: lane `j` of `out[p]` is lane `p` of `g[j]`.
        #[inline]
        pub fn transpose(g: [Self; 8]) -> [Self; 8] {
            transpose(g.map(|v| v.0)).map(Self)
        }
    }

    impl core::ops::Mul for F192x8 {
        type Output = Self;

        #[inline(always)]
        fn mul(self, rhs: Self) -> Self {
            let ((x0, x1), (y0, y1)) = (halves(&self.0), halves(&rhs.0));
            Self(join(mul4(x0, y0), mul4(x1, y1)))
        }
    }

    impl core::ops::Add for F192x8 {
        type Output = Self;

        #[inline]
        fn add(self, rhs: Self) -> Self {
            Self(core::array::from_fn(|i| self.0[i] + rhs.0[i]))
        }
    }

    /// Eight base-field elements, on a target without the wide multiplier.
    #[derive(Clone, Copy, Debug)]
    #[repr(transparent)]
    pub struct F64x8([F64; 8]);

    // SAFETY: one field, an array of plain elements.
    unsafe impl crate::Plain for F64x8 {}

    impl F64x8 {
        pub const ZERO: Self = Self([F64::ZERO; 8]);
        pub const ONE: Self = Self([F64::ONE; 8]);

        #[inline]
        pub fn from_array(k: &[F64; 8]) -> Self {
            Self(*k)
        }

        #[inline]
        pub fn to_array(self) -> [F64; 8] {
            self.0
        }

        #[inline]
        pub fn lane(&self, i: usize) -> F64 {
            self.0[i]
        }

        #[inline]
        pub fn set_lane(&mut self, i: usize, k: F64) {
            self.0[i] = k;
        }

        /// `([a0, a2, a4, a6, b0, b2, b4, b6], [a1, a3, a5, a7, b1, b3, b5, b7])`.
        #[inline]
        pub fn even_odd(a: Self, b: Self) -> (Self, Self) {
            let (even, odd) = even_odd(&a.0, &b.0);
            (Self(even), Self(odd))
        }

        /// The 8x8 transpose: lane `j` of `out[p]` is lane `p` of `g[j]`.
        #[inline]
        pub fn transpose(g: [Self; 8]) -> [Self; 8] {
            transpose(g.map(|v| v.0)).map(Self)
        }
    }

    impl core::ops::Add for F64x8 {
        type Output = Self;

        #[inline]
        fn add(self, rhs: Self) -> Self {
            Self(core::array::from_fn(|i| self.0[i] + rhs.0[i]))
        }
    }

    impl core::ops::Mul for F64x8 {
        type Output = Self;

        #[inline]
        fn mul(self, rhs: Self) -> Self {
            Self(core::array::from_fn(|i| self.0[i] * rhs.0[i]))
        }
    }

    impl F192x8 {
        /// The eight mixed products `self_i * k_i`, unreduced.
        #[inline]
        pub fn mul_base_unreduced(self, k: F64x8) -> Prod8 {
            Prod8(core::array::from_fn(|i| self.0[i].mul_base_unreduced(k.0[i])))
        }
    }

    /// The embedding of the base field.
    impl From<F64x8> for F192x8 {
        #[inline]
        fn from(k: F64x8) -> Self {
            Self(k.0.map(F192::from))
        }
    }

    /// The unreduced products of eight elements, lane by lane, on a target without the wide multiplier.
    #[derive(Clone, Copy, Debug)]
    pub struct Prod8([F192Unreduced; 8]);

    impl Prod8 {
        pub const ZERO: Self = Self([F192Unreduced::ZERO; 8]);

        /// The sum of the eight lanes, reduced.
        #[inline]
        pub fn reduce(self) -> F192 {
            self.0
                .into_iter()
                .fold(F192Unreduced::ZERO, |sum, lane| sum ^ lane)
                .reduce()
        }

        /// Every lane reduced on its own.
        #[inline]
        pub fn reduce_lanes(self) -> F192x8 {
            F192x8(self.0.map(F192Unreduced::reduce))
        }
    }

    impl core::ops::BitXorAssign for Prod8 {
        #[inline]
        fn bitxor_assign(&mut self, rhs: Self) {
            for (a, b) in self.0.iter_mut().zip(rhs.0) {
                *a ^= b;
            }
        }
    }

    impl core::ops::BitXor for Prod8 {
        type Output = Self;

        #[inline]
        fn bitxor(mut self, rhs: Self) -> Self {
            self ^= rhs;
            self
        }
    }

    /// The unreduced sum of eight-element products, on a target without the wide multiplier: one
    /// sum, where [`Prod8`] keeps eight. A NEON register file cannot hold eight lanes of three
    /// 128-bit coefficients, so a sum read only whole is kept as one.
    #[derive(Clone, Copy, Debug)]
    pub struct Acc8(F192Unreduced);

    impl Acc8 {
        pub const ZERO: Self = Self(F192Unreduced::ZERO);

        #[inline]
        pub fn reduce(self) -> F192 {
            self.0.reduce()
        }
    }

    impl From<F192Unreduced> for Acc8 {
        #[inline]
        fn from(u: F192Unreduced) -> Self {
            Self(u)
        }
    }

    impl core::ops::BitXorAssign for Acc8 {
        #[inline]
        fn bitxor_assign(&mut self, rhs: Self) {
            self.0 ^= rhs.0;
        }
    }

    #[inline(always)]
    pub(super) fn dot_ext(x: &[F192; 8], y: &[F192; 8]) -> Acc8 {
        let ((x0, x1), (y0, y1)) = (halves(x), halves(y));
        let sum = mul_unreduced4(x0, y0)
            .into_iter()
            .chain(mul_unreduced4(x1, y1))
            .fold(F192Unreduced::ZERO, |sum, p| sum ^ p);
        Acc8(sum)
    }
}

/// `x0 + r * (x0 + x1)`, elementwise.
#[inline(always)]
pub fn fold_pairs8_ext(x0: &[F192; 8], x1: &[F192; 8], r: F192) -> [F192; 8] {
    let a = F192x8::from_array(x0);
    (a + F192x8::splat(r) * (a + F192x8::from_array(x1))).to_array()
}

/// `x0 + r * x0`, elementwise.
#[inline(always)]
pub fn fold_lones8_ext(x0: &[F192; 8], r: F192) -> [F192; 8] {
    let a = F192x8::from_array(x0);
    (a + F192x8::splat(r) * a).to_array()
}

/// `(sum x0*y0, sum (x0+x1)*(y0+y1))` over eight terms.
#[inline(always)]
pub fn msg_terms8_ext(x0: &[F192; 8], x1: &[F192; 8], y0: &[F192; 8], y1: &[F192; 8]) -> (Acc8, Acc8) {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    {
        let (a0, a1) = (F192x8::from_array(x0), F192x8::from_array(x1));
        let (b0, b1) = (F192x8::from_array(y0), F192x8::from_array(y1));
        (a0.mul_unreduced(b0), (a0 + a1).mul_unreduced(b0 + b1))
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
    {
        let xs: [F192; 8] = core::array::from_fn(|j| x0[j] + x1[j]);
        let ys: [F192; 8] = core::array::from_fn(|j| y0[j] + y1[j]);
        (portable::dot_ext(x0, y0), portable::dot_ext(&xs, &ys))
    }
}

/// `sum x0*y0` over eight terms.
#[inline(always)]
pub fn msg_lone8_ext(x0: &[F192; 8], y0: &[F192; 8]) -> Acc8 {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    return F192x8::from_array(x0).mul_unreduced(F192x8::from_array(y0));
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
    portable::dot_ext(x0, y0)
}

/// The eight mixed products `c * k_i`, unreduced.
#[inline]
pub fn mul_base_splat8(c: F192, k: &[F64; 8]) -> Prod8 {
    F192x8::splat(c).mul_base_unreduced(F64x8::from_array(k))
}

/// `out[i] += add[i]` over eight elements.
#[inline]
pub fn xor_into8(out: &mut [F192; 8], add: &[F192; 8]) {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
    for i in 0..3 {
        use crate::simd::{load, store, xor};
        let sum = xor(load(out, i), load(add, i));
        store(out, i, sum);
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "avx512f")))]
    for (o, a) in out.iter_mut().zip(add) {
        *o += *a;
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
mod avx512 {
    use core::arch::x86_64::*;

    use super::{F64, F192, F192Unreduced};
    use crate::field::gf2_64x3::x86_64::{fold, mul_by_pairs, pair, reduce_lanes512};
    use crate::simd::{from_words, load, store, to_words, xor};

    // The kernels enable avx512bw for `reduce_lanes512`, so the build must have it.
    #[cfg(not(target_feature = "avx512bw"))]
    compile_error!("the F192x8 kernels need avx512bw, which every CPU with avx512f and vpclmulqdq has");

    /// Eight elements in their three planes.
    #[derive(Clone, Copy, Debug)]
    #[repr(C)]
    pub struct F192x8 {
        lo: __m512i,
        hi: __m512i,
        c2: __m512i,
    }

    // SAFETY: `repr(C)` over three vectors, which have no padding and no invalid bit pattern.
    unsafe impl crate::Plain for F192x8 {}

    /// The unreduced products of eight elements: the 128-bit coefficients of the even elements, lane
    /// by lane, then those of the odd ones.
    #[derive(Clone, Copy, Debug)]
    pub struct Acc8 {
        even: [__m512i; 3],
        odd: [__m512i; 3],
    }

    /// Eight base-field elements, one per qword.
    #[derive(Clone, Copy, Debug)]
    #[repr(transparent)]
    pub struct F64x8(__m512i);

    // SAFETY: `repr(transparent)` over a vector, which has no invalid bit pattern.
    unsafe impl crate::Plain for F64x8 {}

    impl F64x8 {
        pub const ZERO: Self = Self(from_words([0; 8]));
        pub const ONE: Self = Self(from_words([1; 8]));

        #[inline(always)]
        pub fn from_array(k: &[F64; 8]) -> Self {
            Self(load(k, 0))
        }

        #[inline(always)]
        pub fn to_array(self) -> [F64; 8] {
            to_words(self.0).map(F64)
        }

        #[inline]
        pub fn lane(&self, i: usize) -> F64 {
            self.to_array()[i]
        }

        #[inline]
        pub fn set_lane(&mut self, i: usize, k: F64) {
            let mut lanes = self.to_array();
            lanes[i] = k;
            *self = Self::from_array(&lanes);
        }

        /// `([a0, a2, a4, a6, b0, b2, b4, b6], [a1, a3, a5, a7, b1, b3, b5, b7])`.
        #[inline(always)]
        pub fn even_odd(a: Self, b: Self) -> (Self, Self) {
            #[inline]
            #[target_feature(enable = "avx512f")]
            fn kernel(a: __m512i, b: __m512i) -> (__m512i, __m512i) {
                let evens = _mm512_setr_epi64(0, 2, 4, 6, 8, 10, 12, 14);
                let odds = _mm512_setr_epi64(1, 3, 5, 7, 9, 11, 13, 15);
                (
                    _mm512_permutex2var_epi64(a, evens, b),
                    _mm512_permutex2var_epi64(a, odds, b),
                )
            }
            // SAFETY: the module is compiled only with avx512f enabled.
            let (even, odd) = unsafe { kernel(a.0, b.0) };
            (Self(even), Self(odd))
        }

        /// The 8x8 transpose: lane `j` of `out[p]` is lane `p` of `g[j]`.
        #[inline(always)]
        pub fn transpose(g: [Self; 8]) -> [Self; 8] {
            crate::simd::transpose8(g.map(|k| k.0)).map(Self)
        }
    }

    impl core::ops::Add for F64x8 {
        type Output = Self;

        #[inline(always)]
        fn add(self, rhs: Self) -> Self {
            Self(xor(self.0, rhs.0))
        }
    }

    /// The eight lane-wise products: one carry-less multiplication per parity of word, then the
    /// lane-wise reduction of both.
    impl core::ops::Mul for F64x8 {
        type Output = Self;

        #[inline(always)]
        fn mul(self, rhs: Self) -> Self {
            // SAFETY: the module is compiled only with the features enabled.
            Self(unsafe { mul_words(self.0, rhs.0) })
        }
    }

    impl F192x8 {
        /// The eight mixed products `self_i * k_i`, unreduced: six carry-less multiplications.
        #[inline(always)]
        pub fn mul_base_unreduced(self, k: F64x8) -> Acc8 {
            // SAFETY: the module is compiled only with the features enabled.
            unsafe { mul_base(self, k.0) }
        }
    }

    /// The embedding of the base field.
    impl From<F64x8> for F192x8 {
        #[inline(always)]
        fn from(k: F64x8) -> Self {
            // SAFETY: the module is compiled only with avx512f enabled.
            unsafe {
                let zero = _mm512_setzero_si512();
                // Each word is its element's `c0`.
                Self {
                    lo: _mm512_unpacklo_epi64(k.0, zero),
                    hi: _mm512_unpackhi_epi64(k.0, zero),
                    c2: zero,
                }
            }
        }
    }

    impl Acc8 {
        pub const ZERO: Self = Self {
            even: [from_words([0; 8]); 3],
            odd: [from_words([0; 8]); 3],
        };

        /// The sum of the eight products, reduced.
        #[inline]
        pub fn reduce(self) -> F192 {
            // SAFETY: the module is compiled only with the features enabled.
            unsafe { reduce_sum(self) }
        }

        /// Every lane reduced on its own.
        #[inline(always)]
        pub fn reduce_lanes(self) -> F192x8 {
            // SAFETY: the module is compiled only with the features enabled.
            unsafe { reduce_planes(self) }
        }
    }

    impl From<F192Unreduced> for Acc8 {
        /// One scalar product, in the first even lane.
        #[inline]
        fn from(u: F192Unreduced) -> Self {
            let [c0, c1, c2] = u.coeffs();
            let lane = |[lo, hi]: [u64; 2]| from_words([lo, hi, 0, 0, 0, 0, 0, 0]);
            Self {
                even: [lane(c0), lane(c1), lane(c2)],
                odd: Self::ZERO.odd,
            }
        }
    }

    impl core::ops::BitXorAssign for Acc8 {
        #[inline(always)]
        fn bitxor_assign(&mut self, rhs: Self) {
            for i in 0..3 {
                self.even[i] = xor(self.even[i], rhs.even[i]);
                self.odd[i] = xor(self.odd[i], rhs.odd[i]);
            }
        }
    }

    impl core::ops::BitXor for Acc8 {
        type Output = Self;

        #[inline(always)]
        fn bitxor(mut self, rhs: Self) -> Self {
            self ^= rhs;
            self
        }
    }

    #[inline]
    #[target_feature(enable = "avx512f")]
    fn reduce_sum(acc: Acc8) -> F192 {
        let coeffs = core::array::from_fn(|i| {
            let a = _mm512_xor_si512(acc.even[i], acc.odd[i]);
            let half = _mm256_xor_si256(_mm512_castsi512_si256(a), _mm512_extracti64x4_epi64::<1>(a));
            let q = _mm_xor_si128(_mm256_castsi256_si128(half), _mm256_extracti128_si256::<1>(half));
            [_mm_cvtsi128_si64(q) as u64, _mm_extract_epi64::<1>(q) as u64]
        });
        F192Unreduced::from_coeffs(coeffs).reduce()
    }

    /// Eight consecutive elements, 24 qwords, into their planes: three loads, six permutes.
    #[inline]
    #[target_feature(enable = "avx512f")]
    fn load_planes(e: &[F192; 8]) -> F192x8 {
        let [z0, z1, z2] = [0, 1, 2].map(|i| load(e, i));
        // Element i is qwords 3i..3i+3; a permute index 8 + j names qword 8 + j, the third register fills the rest.
        let lo = _mm512_permutex2var_epi64(z0, _mm512_setr_epi64(0, 1, 6, 7, 12, 13, 0, 0), z1);
        let lo = _mm512_mask_permutexvar_epi64(lo, 0b1100_0000, _mm512_setr_epi64(0, 0, 0, 0, 0, 0, 2, 3), z2);
        let hi = _mm512_permutex2var_epi64(z0, _mm512_setr_epi64(3, 4, 9, 10, 15, 0, 0, 0), z1);
        let hi = _mm512_mask_permutexvar_epi64(hi, 0b1110_0000, _mm512_setr_epi64(0, 0, 0, 0, 0, 0, 5, 6), z2);
        let c2 = _mm512_permutex2var_epi64(z0, _mm512_setr_epi64(2, 5, 8, 11, 14, 0, 0, 0), z1);
        let c2 = _mm512_mask_permutexvar_epi64(c2, 0b1110_0000, _mm512_setr_epi64(0, 0, 0, 0, 0, 1, 4, 7), z2);
        F192x8 { lo, hi, c2 }
    }

    /// The inverse of [`load_planes`]: six permutes, three stores.
    #[inline]
    #[target_feature(enable = "avx512f")]
    fn store_planes(p: F192x8, out: &mut [F192; 8]) {
        let F192x8 { lo, hi, c2 } = p;
        let v0 = _mm512_permutex2var_epi64(lo, _mm512_setr_epi64(0, 1, 0, 8, 9, 0, 2, 3), hi);
        let v0 = _mm512_mask_permutexvar_epi64(v0, 0b0010_0100, _mm512_setr_epi64(0, 0, 0, 0, 0, 1, 0, 0), c2);
        let v1 = _mm512_permutex2var_epi64(lo, _mm512_setr_epi64(0, 10, 11, 0, 4, 5, 0, 12), hi);
        let v1 = _mm512_mask_permutexvar_epi64(v1, 0b0100_1001, _mm512_setr_epi64(2, 0, 0, 3, 0, 0, 4, 0), c2);
        let v2 = _mm512_permutex2var_epi64(lo, _mm512_setr_epi64(13, 0, 6, 7, 0, 14, 15, 0), hi);
        let v2 = _mm512_mask_permutexvar_epi64(v2, 0b1001_0010, _mm512_setr_epi64(0, 5, 0, 0, 6, 0, 0, 7), c2);
        [v0, v1, v2].into_iter().enumerate().for_each(|(i, v)| store(out, i, v));
    }

    impl F192x8 {
        pub const ZERO: Self = Self {
            lo: from_words([0; 8]),
            hi: from_words([0; 8]),
            c2: from_words([0; 8]),
        };

        /// Element `i` has `c0 = 1` and no other bit.
        pub const ONE: Self = Self {
            lo: from_words([1, 0, 1, 0, 1, 0, 1, 0]),
            hi: from_words([1, 0, 1, 0, 1, 0, 1, 0]),
            c2: from_words([0; 8]),
        };

        /// One scalar in every element.
        #[inline(always)]
        pub fn splat(r: F192) -> Self {
            // SAFETY: the module is compiled only with avx512f enabled.
            unsafe {
                let lo = _mm512_broadcast_i32x4(pair(r.c0, r.c1));
                Self {
                    lo,
                    hi: lo,
                    c2: _mm512_set1_epi64(r.c2 as i64),
                }
            }
        }

        #[inline(always)]
        pub fn from_array(e: &[F192; 8]) -> Self {
            // SAFETY: the module is compiled only with the features enabled.
            unsafe { load_planes(e) }
        }

        #[inline(always)]
        pub fn to_array(self) -> [F192; 8] {
            let mut out = [F192::ZERO; 8];
            // SAFETY: the module is compiled only with the features enabled.
            unsafe { store_planes(self, &mut out) };
            out
        }

        /// Element `i`, read from memory with scalar loads: `[c0, c1]` from its plane, `c2` from the third.
        #[inline]
        pub fn lane(&self, i: usize) -> F192 {
            assert!(i < 8);
            let q = crate::cast_slice::<Self, u64>(core::slice::from_ref(self));
            let at = 8 * (i % 2) + 2 * (i / 2);
            F192::new(q[at], q[at + 1], q[16 + i])
        }

        /// Overwrite element `i` with scalar stores.
        #[inline]
        pub fn set_lane(&mut self, i: usize, e: F192) {
            assert!(i < 8);
            let q = crate::cast_slice_mut::<Self, u64>(core::slice::from_mut(self));
            let at = 8 * (i % 2) + 2 * (i / 2);
            (q[at], q[at + 1], q[16 + i]) = (e.c0, e.c1, e.c2);
        }

        /// The eight lane-wise products, unreduced: twelve carry-less multiplications.
        #[inline(always)]
        pub fn mul_unreduced(self, rhs: Self) -> Acc8 {
            // SAFETY: the module is compiled only with the features enabled.
            unsafe { mul(self, rhs) }
        }

        /// `([a0, a2, a4, a6, b0, b2, b4, b6], [a1, a3, a5, a7, b1, b3, b5, b7])`.
        ///
        /// Even elements are the `lo` plane and odd ones the `hi` plane, so each output plane is one
        /// 128-bit lane shuffle of two inputs, and `c2` is one two-source qword permute.
        #[inline(always)]
        pub fn even_odd(a: Self, b: Self) -> (Self, Self) {
            #[inline]
            #[target_feature(enable = "avx512f")]
            fn kernel(a: F192x8, b: F192x8) -> (F192x8, F192x8) {
                let evens = _mm512_setr_epi64(0, 2, 4, 6, 8, 10, 12, 14);
                let odds = _mm512_setr_epi64(1, 3, 5, 7, 9, 11, 13, 15);
                (
                    F192x8 {
                        lo: _mm512_shuffle_i64x2::<0x88>(a.lo, b.lo),
                        hi: _mm512_shuffle_i64x2::<0xDD>(a.lo, b.lo),
                        c2: _mm512_permutex2var_epi64(a.c2, evens, b.c2),
                    },
                    F192x8 {
                        lo: _mm512_shuffle_i64x2::<0x88>(a.hi, b.hi),
                        hi: _mm512_shuffle_i64x2::<0xDD>(a.hi, b.hi),
                        c2: _mm512_permutex2var_epi64(a.c2, odds, b.c2),
                    },
                )
            }
            // SAFETY: the module is compiled only with avx512f enabled.
            unsafe { kernel(a, b) }
        }

        /// The 8x8 transpose: lane `j` of `out[p]` is lane `p` of `g[j]`.
        ///
        /// Even elements sit in `lo` and odd ones in `hi`, so each source plane splits by the parity
        /// of `j` into a 4x4 transpose of 128-bit lanes, and `c2` is an 8x8 transpose of qwords.
        #[inline(always)]
        pub fn transpose(g: [Self; 8]) -> [Self; 8] {
            #[inline]
            #[target_feature(enable = "avx512f")]
            fn kernel(g: [F192x8; 8]) -> [F192x8; 8] {
                // The 128-bit lanes of four registers, out[m] lane i = r[i] lane m.
                let lanes = |r: [__m512i; 4]| {
                    let t0 = _mm512_shuffle_i64x2::<0x88>(r[0], r[1]);
                    let t1 = _mm512_shuffle_i64x2::<0xDD>(r[0], r[1]);
                    let t2 = _mm512_shuffle_i64x2::<0x88>(r[2], r[3]);
                    let t3 = _mm512_shuffle_i64x2::<0xDD>(r[2], r[3]);
                    [
                        _mm512_shuffle_i64x2::<0x88>(t0, t2),
                        _mm512_shuffle_i64x2::<0x88>(t1, t3),
                        _mm512_shuffle_i64x2::<0xDD>(t0, t2),
                        _mm512_shuffle_i64x2::<0xDD>(t1, t3),
                    ]
                };
                let mut out = [F192x8::ZERO; 8];
                // Source plane `lo` feeds the even outputs and `hi` the odd; even `j` feed `lo`.
                let from_lo_even = lanes([g[0].lo, g[2].lo, g[4].lo, g[6].lo]);
                let from_lo_odd = lanes([g[1].lo, g[3].lo, g[5].lo, g[7].lo]);
                let from_hi_even = lanes([g[0].hi, g[2].hi, g[4].hi, g[6].hi]);
                let from_hi_odd = lanes([g[1].hi, g[3].hi, g[5].hi, g[7].hi]);
                for m in 0..4 {
                    out[2 * m].lo = from_lo_even[m];
                    out[2 * m].hi = from_lo_odd[m];
                    out[2 * m + 1].lo = from_hi_even[m];
                    out[2 * m + 1].hi = from_hi_odd[m];
                }
                let c2 = crate::simd::transpose8(g.map(|e| e.c2));
                for (o, c2) in out.iter_mut().zip(c2) {
                    o.c2 = c2;
                }
                out
            }
            // SAFETY: the module is compiled only with avx512f enabled.
            unsafe { kernel(g) }
        }
    }

    impl core::ops::Add for F192x8 {
        type Output = Self;

        #[inline(always)]
        fn add(self, rhs: Self) -> Self {
            Self {
                lo: xor(self.lo, rhs.lo),
                hi: xor(self.hi, rhs.hi),
                c2: xor(self.c2, rhs.c2),
            }
        }
    }

    /// The eight lane-wise products.
    impl core::ops::Mul for F192x8 {
        type Output = Self;

        #[inline(always)]
        fn mul(self, rhs: Self) -> Self {
            // SAFETY: the module is compiled only with the features enabled.
            unsafe { reduce_planes(mul(self, rhs)) }
        }
    }

    impl core::ops::AddAssign for F192x8 {
        #[inline]
        fn add_assign(&mut self, rhs: Self) {
            *self = *self + rhs;
        }
    }

    /// The Karatsuba operands of one parity: the pair plane, `c0 + c1` in both qwords, and the pair
    /// plane with that parity's `c2` added to both qwords.
    #[inline]
    #[target_feature(enable = "avx512f")]
    fn karatsuba_operands(pairs: __m512i, c2_dup: __m512i) -> (__m512i, __m512i, __m512i) {
        let swapped = _mm512_shuffle_epi32::<0x4E>(pairs);
        (pairs, _mm512_xor_si512(pairs, swapped), _mm512_xor_si512(pairs, c2_dup))
    }

    /// The six Karatsuba products of one parity, y-folded.
    #[inline]
    #[target_feature(enable = "avx512f,vpclmulqdq")]
    fn karatsuba_lanes(
        (ap, a_s, a_t): (__m512i, __m512i, __m512i),
        a2: __m512i,
        (bp, b_s, b_t): (__m512i, __m512i, __m512i),
        b2: __m512i,
    ) -> [__m512i; 3] {
        let p0 = _mm512_clmulepi64_epi128::<0x00>(ap, bp);
        let p1 = _mm512_clmulepi64_epi128::<0x11>(ap, bp);
        let p2 = _mm512_clmulepi64_epi128::<0x00>(a2, b2);
        let p01 = _mm512_clmulepi64_epi128::<0x00>(a_s, b_s);
        let p02 = _mm512_clmulepi64_epi128::<0x00>(a_t, b_t);
        let p12 = _mm512_clmulepi64_epi128::<0x11>(a_t, b_t);
        fold(p0, p1, p2, p01, p02, p12, |x, y| _mm512_xor_si512(x, y))
    }

    /// The eight lane-wise products, unreduced: twelve carry-less multiplications.
    #[inline]
    #[target_feature(enable = "avx512f,vpclmulqdq")]
    fn mul(a: F192x8, b: F192x8) -> Acc8 {
        // Each parity's c2 in both qwords of its lane.
        let (a2e, a2o) = (_mm512_shuffle_epi32::<0x44>(a.c2), _mm512_shuffle_epi32::<0xEE>(a.c2));
        let (b2e, b2o) = (_mm512_shuffle_epi32::<0x44>(b.c2), _mm512_shuffle_epi32::<0xEE>(b.c2));
        Acc8 {
            even: karatsuba_lanes(karatsuba_operands(a.lo, a2e), a2e, karatsuba_operands(b.lo, b2e), b2e),
            odd: karatsuba_lanes(karatsuba_operands(a.hi, a2o), a2o, karatsuba_operands(b.hi, b2o), b2o),
        }
    }

    /// The eight mixed products by the words of `k`, unreduced: six carry-less multiplications.
    #[inline]
    #[target_feature(enable = "avx512f,vpclmulqdq")]
    fn mul_base(a: F192x8, k: __m512i) -> Acc8 {
        let [e0, e1, o0, o1, e2, o2] = mul_by_pairs(a.lo, a.hi, a.c2, k);
        Acc8 {
            even: [e0, e1, e2],
            odd: [o0, o1, o2],
        }
    }

    /// Reduce every lane back to planes.
    #[inline]
    #[target_feature(enable = "avx512f,avx512bw")]
    fn reduce_planes(acc: Acc8) -> F192x8 {
        let [d0e, d1e, d2e] = acc.even;
        let [d0o, d1o, d2o] = acc.odd;
        let red = |x, y| reduce_lanes512(_mm512_unpacklo_epi64(x, y), _mm512_unpackhi_epi64(x, y));
        F192x8 {
            lo: red(d0e, d1e),
            hi: red(d0o, d1o),
            c2: red(d2e, d2o),
        }
    }

    /// Eight base-field products: one carry-less multiplication per parity of word, then the lane-wise
    /// reduction of both.
    #[inline]
    #[target_feature(enable = "avx512f,avx512bw,vpclmulqdq")]
    fn mul_words(a: __m512i, b: __m512i) -> __m512i {
        let (even, odd) = (
            _mm512_clmulepi64_epi128::<0x00>(a, b),
            _mm512_clmulepi64_epi128::<0x11>(a, b),
        );
        reduce_lanes512(_mm512_unpacklo_epi64(even, odd), _mm512_unpackhi_epi64(even, odd))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_rng::Rng;

    #[test]
    fn kernels_match_the_scalar_forms() {
        let mut rng = Rng::new(0xF192_0008);
        for _ in 0..200 {
            let x0: [F192; 8] = core::array::from_fn(|_| rng.ext());
            let x1: [F192; 8] = core::array::from_fn(|_| rng.ext());
            let y0: [F192; 8] = core::array::from_fn(|_| rng.ext());
            let y1: [F192; 8] = core::array::from_fn(|_| rng.ext());
            let k0: [F64; 8] = core::array::from_fn(|_| F64(rng.next_u64()));
            let k1: [F64; 8] = core::array::from_fn(|_| F64(rng.next_u64()));
            let r = rng.ext();

            assert_eq!(
                fold_pairs8_ext(&x0, &x1, r),
                core::array::from_fn(|j| x0[j] + r * (x0[j] + x1[j]))
            );
            assert_eq!(fold_lones8_ext(&x0, r), core::array::from_fn(|j| x0[j] + r * x0[j]));

            let dot = |x: &[F192; 8], y: &[F192; 8]| (0..8).fold(F192::ZERO, |acc, j| acc + x[j] * y[j]);
            let (u0, u2) = msg_terms8_ext(&x0, &x1, &y0, &y1);
            assert_eq!(u0.reduce(), dot(&x0, &y0));
            let xs: [F192; 8] = core::array::from_fn(|j| x0[j] + x1[j]);
            let ys: [F192; 8] = core::array::from_fn(|j| y0[j] + y1[j]);
            assert_eq!(u2.reduce(), dot(&xs, &ys));
            assert_eq!(msg_lone8_ext(&x0, &y0).reduce(), dot(&x0, &y0));

            let mut per: Prod8 = mul_base_splat8(r, &k0);
            per ^= mul_base_splat8(x0[0], &k1);
            assert_eq!(
                per.reduce_lanes().to_array(),
                core::array::from_fn(|j| r.mul_base(k0[j]) + x0[0].mul_base(k1[j]))
            );
            let mut sum = x0;
            xor_into8(&mut sum, &x1);
            assert_eq!(sum, core::array::from_fn(|j| x0[j] + x1[j]));

            let (xa, xb, xc) = (
                F192x8::from_array(&x0),
                F192x8::from_array(&x1),
                F192x8::from_array(&y0),
            );
            assert_eq!(xa.to_array(), x0);
            assert_eq!(F192x8::splat(r).to_array(), [r; 8]);
            assert_eq!(F192x8::ONE.to_array(), [F192::ONE; 8]);
            assert_eq!((xa + xb).to_array(), core::array::from_fn(|j| x0[j] + x1[j]));
            assert_eq!((xa * xb).to_array(), core::array::from_fn(|j| x0[j] * x1[j]));
            let sum = (xa.mul_unreduced(xb) ^ xc.mul_unreduced(xa)).reduce_lanes();
            assert_eq!(sum.to_array(), core::array::from_fn(|j| x0[j] * x1[j] + y0[j] * x0[j]));
            assert_eq!(xa.mul_unreduced(xb).reduce(), dot(&x0, &x1));
            let rows: [F192x8; 8] = core::array::from_fn(|j| {
                let element = |p: usize| F192::new(x0[p].c0 ^ j as u64, x1[j].c1, y0[(j + p) % 8].c2);
                F192x8::from_array(&core::array::from_fn(element))
            });
            let columns = F192x8::transpose(rows);
            for (p, column) in columns.iter().enumerate() {
                for j in 0..8 {
                    assert_eq!(column.lane(j), rows[j].lane(p));
                }
            }
            let (even, odd) = F192x8::even_odd(xa, xb);
            assert_eq!(
                even.to_array(),
                core::array::from_fn(|j| if j < 4 { x0[2 * j] } else { x1[2 * (j - 4)] })
            );
            assert_eq!(
                odd.to_array(),
                core::array::from_fn(|j| if j < 4 { x0[2 * j + 1] } else { x1[2 * (j - 4) + 1] })
            );
            assert_eq!(xa.lane(5), x0[5]);
            let mut moved = F192x8::ZERO;
            for j in 0..8 {
                moved.set_lane(j, y1[j]);
            }
            assert_eq!(moved.to_array(), y1);

            let (ka, kb) = (F64x8::from_array(&k0), F64x8::from_array(&k1));
            assert_eq!(ka.to_array(), k0);
            assert_eq!(F64x8::ONE.to_array(), [F64::ONE; 8]);
            assert_eq!((ka + kb).to_array(), core::array::from_fn(|j| k0[j] + k1[j]));
            assert_eq!((ka * kb).to_array(), core::array::from_fn(|j| k0[j] * k1[j]));
            let (even, odd) = F64x8::even_odd(ka, kb);
            assert_eq!(
                even.to_array(),
                core::array::from_fn(|j| if j < 4 { k0[2 * j] } else { k1[2 * (j - 4)] })
            );
            assert_eq!(
                odd.to_array(),
                core::array::from_fn(|j| if j < 4 { k0[2 * j + 1] } else { k1[2 * (j - 4) + 1] })
            );
            let rows: [F64x8; 8] = core::array::from_fn(|j| {
                F64x8::from_array(&core::array::from_fn(|p| {
                    F64(k0[p].0 ^ k1[(j + p) % 8].0.rotate_left(j as u32))
                }))
            });
            for (p, column) in F64x8::transpose(rows).into_iter().enumerate() {
                for j in 0..8 {
                    assert_eq!(column.lane(j), rows[j].lane(p));
                }
            }
            let mut moved = ka;
            moved.set_lane(3, k1[0]);
            assert_eq!(moved.lane(3), k1[0]);
            assert_eq!(moved.lane(2), k0[2]);
            assert_eq!(F192x8::from(ka).to_array(), k0.map(F192::from));
            assert_eq!(
                xa.mul_base_unreduced(ka).reduce_lanes().to_array(),
                core::array::from_fn(|j| x0[j].mul_base(k0[j]))
            );

            // Accumulation across calls sums before the one reduction.
            let mut acc = Acc8::ZERO;
            acc ^= msg_lone8_ext(&x0, &y0);
            acc ^= msg_lone8_ext(&x1, &y1);
            assert_eq!(acc.reduce(), dot(&x0, &y0) + dot(&x1, &y1));
        }
    }
}
