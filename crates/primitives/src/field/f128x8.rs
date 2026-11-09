//! Eight-element `F128` kernels that never move a word through an integer register.
//!
//! On AVX-512 the eight elements live in two plane registers, the [`Weights8`](super::Weights8) layout:
//!
//! ```text
//!     lo  lane j = [c0, c1] of element 2j        hi  lane j = [c0, c1] of element 2j+1
//! ```
//!
//! With VPCLMULQDQ but no AVX-512 they are two halves of four lanes in the `x4` form, a YMM plane per
//! coefficient.
//!
//! A kernel loads its operands straight from memory, so it must only read values stored before the
//! current loop iteration: a 512-bit load over a word just stored stalls on the store buffer.
//!
//! Products accumulate unreduced in [`Acc8`], one reduction per sum rather than per term.

use super::gf2_64::F64;
use super::gf2_64x2::{F128, F128Unreduced};

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "vpclmulqdq",
    target_feature = "avx2",
    not(target_feature = "avx512f")
))]
pub use avx2::{F64x8, F128x8, Prod8};
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
pub use avx512::{Acc8, F64x8, F128x8};
#[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2")))]
pub use portable::{F64x8, F128x8, Prod8};
#[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
pub use sum::Acc8;

/// The unreduced products of eight elements, lane by lane: what [`F128x8::mul_unreduced`] returns.
/// A sum of them is an XOR, and [`Prod8::reduce_lanes`] reduces each lane on its own.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
pub type Prod8 = Acc8;

/// The eight-lane types on a target without the wide multiplier.
#[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2")))]
mod portable {
    use super::sum::halves;
    use super::{F64, F128, F128Unreduced};
    use crate::field::gf2_64x2::{mul_unreduced4, mul4};

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

    /// Eight elements, on a target without the wide multiplier. Line-aligned, so that an
    /// array of them is still published by the streaming stores where those exist.
    #[derive(Clone, Copy, Debug)]
    #[repr(C, align(64))]
    pub struct F128x8([F128; 8]);

    // SAFETY: one field, an array of plain elements.
    unsafe impl crate::Plain for F128x8 {}

    impl F128x8 {
        #[inline]
        pub fn splat(r: F128) -> Self {
            Self([r; 8])
        }

        #[inline]
        pub fn from_array(e: &[F128; 8]) -> Self {
            Self(*e)
        }

        #[inline]
        pub fn to_array(self) -> [F128; 8] {
            self.0
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
    }

    impl core::ops::Mul for F128x8 {
        type Output = Self;

        #[inline(always)]
        fn mul(self, rhs: Self) -> Self {
            let ((x0, x1), (y0, y1)) = (halves(&self.0), halves(&rhs.0));
            Self(join(mul4(x0, y0), mul4(x1, y1)))
        }
    }

    impl core::ops::Add for F128x8 {
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
        #[inline]
        pub fn from_array(k: &[F64; 8]) -> Self {
            Self(*k)
        }
    }

    impl core::ops::Add for F64x8 {
        type Output = Self;

        #[inline]
        fn add(self, rhs: Self) -> Self {
            Self(core::array::from_fn(|i| self.0[i] + rhs.0[i]))
        }
    }

    impl F128x8 {
        /// The eight mixed products `self_i * k_i`, unreduced.
        #[inline]
        pub fn mul_base_unreduced(self, k: F64x8) -> Prod8 {
            Prod8(core::array::from_fn(|i| self.0[i].mul_base_unreduced(k.0[i])))
        }
    }

    /// The embedding of the base field.
    impl From<F64x8> for F128x8 {
        #[inline]
        fn from(k: F64x8) -> Self {
            Self(k.0.map(F128::from))
        }
    }

    /// The unreduced products of eight elements, lane by lane, on a target without the wide multiplier.
    #[derive(Clone, Copy, Debug)]
    pub struct Prod8([F128Unreduced; 8]);

    impl Prod8 {
        pub const ZERO: Self = Self([F128Unreduced::ZERO; 8]);

        /// The sum of the eight lanes, reduced.
        #[inline]
        pub fn reduce(self) -> F128 {
            self.0
                .into_iter()
                .fold(F128Unreduced::ZERO, |sum, lane| sum ^ lane)
                .reduce()
        }

        /// Every lane reduced on its own.
        #[inline]
        pub fn reduce_lanes(self) -> F128x8 {
            F128x8(self.0.map(F128Unreduced::reduce))
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
}

/// The dot-product accumulator on a target without the AVX-512 multiplier.
#[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
mod sum {
    use super::{F128, F128Unreduced};
    use crate::field::gf2_64x2::mul_unreduced4;

    /// The two quads of eight lanes. Straight-line, so a product's halves stay in registers:
    /// an `array::map` over the halves is not inlined and passes both through memory.
    #[inline(always)]
    pub(super) fn halves<T: Copy>(x: &[T; 8]) -> ([T; 4], [T; 4]) {
        ([x[0], x[1], x[2], x[3]], [x[4], x[5], x[6], x[7]])
    }

    /// The unreduced sum of eight-element products: one sum, where [`Prod8`](super::Prod8) keeps
    /// eight. A NEON register file cannot hold eight lanes of three 128-bit coefficients, and on
    /// AVX2 the dot products it sums take their operands straight from memory, with no plane
    /// transpose, so a sum read only whole is kept as one.
    #[derive(Clone, Copy, Debug)]
    pub struct Acc8(F128Unreduced);

    impl Acc8 {
        pub const ZERO: Self = Self(F128Unreduced::ZERO);

        #[inline]
        pub fn reduce(self) -> F128 {
            self.0.reduce()
        }
    }

    impl From<F128Unreduced> for Acc8 {
        #[inline]
        fn from(u: F128Unreduced) -> Self {
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
    pub(super) fn dot_ext(x: &[F128; 8], y: &[F128; 8]) -> Acc8 {
        let ((x0, x1), (y0, y1)) = (halves(x), halves(y));
        let sum = mul_unreduced4(x0, y0)
            .into_iter()
            .chain(mul_unreduced4(x1, y1))
            .fold(F128Unreduced::ZERO, |sum, p| sum ^ p);
        Acc8(sum)
    }
}

/// `x0 + r * (x0 + x1)`, elementwise.
#[inline(always)]
pub fn fold_pairs8_ext(x0: &[F128; 8], x1: &[F128; 8], r: F128) -> [F128; 8] {
    let a = F128x8::from_array(x0);
    (a + F128x8::splat(r) * (a + F128x8::from_array(x1))).to_array()
}

/// `x0 + r * x0`, elementwise.
#[inline(always)]
pub fn fold_lones8_ext(x0: &[F128; 8], r: F128) -> [F128; 8] {
    let a = F128x8::from_array(x0);
    (a + F128x8::splat(r) * a).to_array()
}

/// `(sum x0*y0, sum (x0+x1)*(y0+y1))` over eight terms.
#[inline(always)]
pub fn msg_terms8_ext(x0: &[F128; 8], x1: &[F128; 8], y0: &[F128; 8], y1: &[F128; 8]) -> (Acc8, Acc8) {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    {
        let (a0, a1) = (F128x8::from_array(x0), F128x8::from_array(x1));
        let (b0, b1) = (F128x8::from_array(y0), F128x8::from_array(y1));
        (a0.mul_unreduced(b0), (a0 + a1).mul_unreduced(b0 + b1))
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
    {
        let xs: [F128; 8] = core::array::from_fn(|j| x0[j] + x1[j]);
        let ys: [F128; 8] = core::array::from_fn(|j| y0[j] + y1[j]);
        (sum::dot_ext(x0, y0), sum::dot_ext(&xs, &ys))
    }
}

/// `sum x0*y0` over eight terms.
#[inline(always)]
pub fn msg_lone8_ext(x0: &[F128; 8], y0: &[F128; 8]) -> Acc8 {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    return F128x8::from_array(x0).mul_unreduced(F128x8::from_array(y0));
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
    sum::dot_ext(x0, y0)
}

/// The eight mixed products `c * k_i`, unreduced.
#[inline]
pub fn mul_base_splat8(c: F128, k: &[F64; 8]) -> Prod8 {
    F128x8::splat(c).mul_base_unreduced(F64x8::from_array(k))
}

/// `out[i] += add[i]` over eight elements.
#[inline]
pub fn xor_into8(out: &mut [F128; 8], add: &[F128; 8]) {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
    for i in 0..2 {
        use crate::simd::{load, store, xor};
        let sum = xor(load(out, i), load(add, i));
        store(out, i, sum);
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "avx512f")))]
    for (o, a) in out.iter_mut().zip(add) {
        *o += *a;
    }
}

/// The eight-lane types with VPCLMULQDQ but no AVX-512: two halves of four lanes, each the `x4` form, a
/// YMM plane per coefficient, so a product is lane-wise, two lanes to an instruction.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "vpclmulqdq",
    target_feature = "avx2",
    not(target_feature = "avx512f")
))]
mod avx2 {
    use core::arch::x86_64::*;

    use super::{F64, F128};
    use crate::field::x4::{F64x4, F128x4, Mixed4};

    /// Lanes `4h ..= 4h + 3` in half `h`. Line-aligned, as the portable form is.
    #[derive(Clone, Copy, Debug)]
    #[repr(C, align(64))]
    pub struct F128x8([F128x4; 2]);

    // SAFETY: `repr(C)` over vectors that fill the alignment, so no padding and no invalid bit pattern.
    unsafe impl crate::Plain for F128x8 {}

    /// Lanes `4h ..= 4h + 3` in half `h`.
    #[derive(Clone, Copy, Debug)]
    #[repr(C)]
    pub struct F64x8([F64x4; 2]);

    // SAFETY: `repr(C)` over vectors, which have no padding and no invalid bit pattern.
    unsafe impl crate::Plain for F64x8 {}

    /// Unreduced lane-wise products, half by half.
    #[derive(Clone, Copy, Debug)]
    pub struct Prod8([Mixed4; 2]);

    impl F128x8 {
        #[inline(always)]
        pub fn splat(r: F128) -> Self {
            Self([F128x4::splat(r); 2])
        }

        #[inline(always)]
        pub fn from_array(e: &[F128; 8]) -> Self {
            let (halves, _) = e.as_chunks::<4>();
            Self([F128x4::load(&halves[0]), F128x4::load(&halves[1])])
        }

        #[inline(always)]
        pub fn to_array(self) -> [F128; 8] {
            let mut out = [F128::ZERO; 8];
            let (halves, _) = out.as_chunks_mut::<4>();
            self.0[0].store(&mut halves[0]);
            self.0[1].store(&mut halves[1]);
            out
        }

        #[inline(always)]
        pub fn mul_unreduced(self, rhs: Self) -> Prod8 {
            Prod8(std::array::from_fn(|h| self.0[h].mul_unreduced(rhs.0[h])))
        }

        /// The eight mixed products `self_i * k_i`, unreduced.
        #[inline(always)]
        pub fn mul_base_unreduced(self, k: F64x8) -> Prod8 {
            Prod8(std::array::from_fn(|h| {
                let mut p = Mixed4::ZERO;
                p.add(self.0[h], k.0[h]);
                p
            }))
        }

        /// `([a0, a2, a4, a6, b0, b2, b4, b6], [a1, a3, a5, a7, b1, b3, b5, b7])`.
        #[inline(always)]
        pub fn even_odd(a: Self, b: Self) -> (Self, Self) {
            // Per plane, `[x0, x4, x2, x6]` reordered to `[x0, x2, x4, x6]`, and the same for the odd lanes.
            let split = |x: Self| -> (F128x4, F128x4) {
                let [lo, hi] = x.0.map(|h| h.0);
                // SAFETY: the module's cfg enables avx2.
                unsafe {
                    (
                        F128x4(std::array::from_fn(|k| {
                            _mm256_permute4x64_epi64::<0xD8>(_mm256_unpacklo_epi64(lo[k], hi[k]))
                        })),
                        F128x4(std::array::from_fn(|k| {
                            _mm256_permute4x64_epi64::<0xD8>(_mm256_unpackhi_epi64(lo[k], hi[k]))
                        })),
                    )
                }
            };
            let ((ae, ao), (be, bo)) = (split(a), split(b));
            (Self([ae, be]), Self([ao, bo]))
        }
    }

    impl core::ops::Add for F128x8 {
        type Output = Self;

        #[inline(always)]
        fn add(self, rhs: Self) -> Self {
            Self([self.0[0] + rhs.0[0], self.0[1] + rhs.0[1]])
        }
    }

    impl core::ops::Mul for F128x8 {
        type Output = Self;

        #[inline(always)]
        fn mul(self, rhs: Self) -> Self {
            self.mul_unreduced(rhs).reduce_lanes()
        }
    }

    /// The embedding of the base field.
    impl From<F64x8> for F128x8 {
        #[inline(always)]
        fn from(k: F64x8) -> Self {
            Self(k.0.map(F128x4::from))
        }
    }

    impl F64x8 {
        #[inline(always)]
        pub fn from_array(k: &[F64; 8]) -> Self {
            let (halves, _) = k.as_chunks::<4>();
            Self([F64x4::load(&halves[0]), F64x4::load(&halves[1])])
        }
    }

    impl core::ops::Add for F64x8 {
        type Output = Self;

        #[inline(always)]
        fn add(self, rhs: Self) -> Self {
            Self([self.0[0] + rhs.0[0], self.0[1] + rhs.0[1]])
        }
    }

    impl Prod8 {
        pub const ZERO: Self = Self([Mixed4::ZERO; 2]);

        /// The sum of the eight lanes, reduced once.
        #[inline]
        pub fn reduce(self) -> F128 {
            let [mut sum, other] = self.0;
            sum ^= other;
            sum.sum()
        }

        /// Every lane reduced on its own.
        #[inline(always)]
        pub fn reduce_lanes(self) -> F128x8 {
            F128x8(self.0.map(Mixed4::reduce))
        }
    }

    impl core::ops::BitXorAssign for Prod8 {
        #[inline(always)]
        fn bitxor_assign(&mut self, rhs: Self) {
            self.0[0] ^= rhs.0[0];
            self.0[1] ^= rhs.0[1];
        }
    }

    impl core::ops::BitXor for Prod8 {
        type Output = Self;

        #[inline(always)]
        fn bitxor(mut self, rhs: Self) -> Self {
            self ^= rhs;
            self
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
mod avx512 {
    use core::arch::x86_64::*;

    use super::{F64, F128, F128Unreduced};
    use crate::field::gf2_64x2::x86_64::{fold, mul_by_pairs, pair, reduce_lanes512, times_x512};
    use crate::simd::{from_words, load, store, xor};

    // The kernels enable avx512bw for `reduce_lanes512`, so the build must have it.
    #[cfg(not(target_feature = "avx512bw"))]
    compile_error!("the F128x8 kernels need avx512bw, which every CPU with avx512f and vpclmulqdq has");

    /// Eight elements in their two planes.
    #[derive(Clone, Copy, Debug)]
    #[repr(C)]
    pub struct F128x8 {
        lo: __m512i,
        hi: __m512i,
    }

    // SAFETY: `repr(C)` over two vectors, which have no padding and no invalid bit pattern.
    unsafe impl crate::Plain for F128x8 {}

    /// The unreduced products of eight elements: the 128-bit coefficients of the even elements, lane
    /// by lane, then those of the odd ones.
    #[derive(Clone, Copy, Debug)]
    pub struct Acc8 {
        even: [__m512i; 2],
        odd: [__m512i; 2],
    }

    /// Eight base-field elements, one per qword.
    #[derive(Clone, Copy, Debug)]
    #[repr(transparent)]
    pub struct F64x8(__m512i);

    // SAFETY: `repr(transparent)` over a vector, which has no invalid bit pattern.
    unsafe impl crate::Plain for F64x8 {}

    impl F64x8 {
        #[inline(always)]
        pub fn from_array(k: &[F64; 8]) -> Self {
            Self(load(k, 0))
        }
    }

    impl core::ops::Add for F64x8 {
        type Output = Self;

        #[inline(always)]
        fn add(self, rhs: Self) -> Self {
            Self(xor(self.0, rhs.0))
        }
    }

    impl F128x8 {
        /// The eight mixed products `self_i * k_i`, unreduced: four carry-less multiplications.
        #[inline(always)]
        pub fn mul_base_unreduced(self, k: F64x8) -> Acc8 {
            // SAFETY: the module is compiled only with the features enabled.
            let [e0, e1, o0, o1] = unsafe { mul_by_pairs(self.lo, self.hi, k.0) };
            Acc8 {
                even: [e0, e1],
                odd: [o0, o1],
            }
        }
    }

    /// The embedding of the base field.
    impl From<F64x8> for F128x8 {
        #[inline(always)]
        fn from(k: F64x8) -> Self {
            // SAFETY: the module is compiled only with avx512f enabled.
            unsafe {
                let zero = _mm512_setzero_si512();
                // Each word is its element's `c0`.
                Self {
                    lo: _mm512_unpacklo_epi64(k.0, zero),
                    hi: _mm512_unpackhi_epi64(k.0, zero),
                }
            }
        }
    }

    impl Acc8 {
        pub const ZERO: Self = Self {
            even: [from_words([0; 8]); 2],
            odd: [from_words([0; 8]); 2],
        };

        /// The sum of the eight products, reduced.
        #[inline]
        pub fn reduce(self) -> F128 {
            // SAFETY: the module is compiled only with the features enabled.
            unsafe { reduce_sum(self) }
        }

        /// Every lane reduced on its own.
        #[inline(always)]
        pub fn reduce_lanes(self) -> F128x8 {
            // SAFETY: the module is compiled only with the features enabled.
            unsafe { reduce_planes(self) }
        }
    }

    impl From<F128Unreduced> for Acc8 {
        /// One scalar product, in the first even lane.
        #[inline]
        fn from(u: F128Unreduced) -> Self {
            let [c0, c1] = u.coeffs();
            let lane = |[lo, hi]: [u64; 2]| from_words([lo, hi, 0, 0, 0, 0, 0, 0]);
            Self {
                even: [lane(c0), lane(c1)],
                odd: Self::ZERO.odd,
            }
        }
    }

    impl core::ops::BitXorAssign for Acc8 {
        #[inline(always)]
        fn bitxor_assign(&mut self, rhs: Self) {
            for i in 0..2 {
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
    fn reduce_sum(acc: Acc8) -> F128 {
        let coeffs = core::array::from_fn(|i| {
            let a = _mm512_xor_si512(acc.even[i], acc.odd[i]);
            let half = _mm256_xor_si256(_mm512_castsi512_si256(a), _mm512_extracti64x4_epi64::<1>(a));
            let q = _mm_xor_si128(_mm256_castsi256_si128(half), _mm256_extracti128_si256::<1>(half));
            [_mm_cvtsi128_si64(q) as u64, _mm_extract_epi64::<1>(q) as u64]
        });
        F128Unreduced::from_coeffs(coeffs).reduce()
    }

    /// Eight consecutive elements, 16 qwords, into their planes: two loads, two 128-bit lane shuffles.
    #[inline]
    #[target_feature(enable = "avx512f")]
    fn load_planes(e: &[F128; 8]) -> F128x8 {
        let [z0, z1] = [0, 1].map(|i| load(e, i));
        // Register `i` holds elements `4i..4i+4`, one per 128-bit lane.
        F128x8 {
            lo: _mm512_shuffle_i64x2::<0x88>(z0, z1),
            hi: _mm512_shuffle_i64x2::<0xDD>(z0, z1),
        }
    }

    /// The inverse of [`load_planes`]: two permutes, two stores.
    #[inline]
    #[target_feature(enable = "avx512f")]
    fn store_planes(p: F128x8, out: &mut [F128; 8]) {
        let F128x8 { lo, hi } = p;
        let v0 = _mm512_permutex2var_epi64(lo, _mm512_setr_epi64(0, 1, 8, 9, 2, 3, 10, 11), hi);
        let v1 = _mm512_permutex2var_epi64(lo, _mm512_setr_epi64(4, 5, 12, 13, 6, 7, 14, 15), hi);
        store(out, 0, v0);
        store(out, 1, v1);
    }

    impl F128x8 {
        /// One scalar in every element.
        #[inline(always)]
        pub fn splat(r: F128) -> Self {
            // SAFETY: the module is compiled only with avx512f enabled.
            let lo = unsafe { _mm512_broadcast_i32x4(pair(r.c0, r.c1)) };
            Self { lo, hi: lo }
        }

        #[inline(always)]
        pub fn from_array(e: &[F128; 8]) -> Self {
            // SAFETY: the module is compiled only with the features enabled.
            unsafe { load_planes(e) }
        }

        #[inline(always)]
        pub fn to_array(self) -> [F128; 8] {
            let mut out = [F128::ZERO; 8];
            // SAFETY: the module is compiled only with the features enabled.
            unsafe { store_planes(self, &mut out) };
            out
        }

        /// The eight lane-wise products, unreduced: six carry-less multiplications.
        #[inline(always)]
        pub fn mul_unreduced(self, rhs: Self) -> Acc8 {
            // SAFETY: the module is compiled only with the features enabled.
            unsafe { mul(self, rhs) }
        }

        /// `([a0, a2, a4, a6, b0, b2, b4, b6], [a1, a3, a5, a7, b1, b3, b5, b7])`.
        ///
        /// Even elements are the `lo` plane and odd ones the `hi` plane, so each output plane is one
        /// 128-bit lane shuffle of two inputs.
        #[inline(always)]
        pub fn even_odd(a: Self, b: Self) -> (Self, Self) {
            #[inline]
            #[target_feature(enable = "avx512f")]
            fn kernel(a: F128x8, b: F128x8) -> (F128x8, F128x8) {
                (
                    F128x8 {
                        lo: _mm512_shuffle_i64x2::<0x88>(a.lo, b.lo),
                        hi: _mm512_shuffle_i64x2::<0xDD>(a.lo, b.lo),
                    },
                    F128x8 {
                        lo: _mm512_shuffle_i64x2::<0x88>(a.hi, b.hi),
                        hi: _mm512_shuffle_i64x2::<0xDD>(a.hi, b.hi),
                    },
                )
            }
            // SAFETY: the module is compiled only with avx512f enabled.
            unsafe { kernel(a, b) }
        }
    }

    impl core::ops::Add for F128x8 {
        type Output = Self;

        #[inline(always)]
        fn add(self, rhs: Self) -> Self {
            Self {
                lo: xor(self.lo, rhs.lo),
                hi: xor(self.hi, rhs.hi),
            }
        }
    }

    /// The eight lane-wise products.
    impl core::ops::Mul for F128x8 {
        type Output = Self;

        #[inline(always)]
        fn mul(self, rhs: Self) -> Self {
            // SAFETY: the module is compiled only with the features enabled.
            unsafe { reduce_planes(mul(self, rhs)) }
        }
    }

    /// The three Karatsuba products of one parity's pair plane, y-folded: `c0 + c1` sits in both
    /// qwords of the swapped sum, so all three products read one qword per 128-bit lane.
    #[inline]
    #[target_feature(enable = "avx512f,avx512bw,vpclmulqdq")]
    fn karatsuba_lanes(a: __m512i, b: __m512i) -> [__m512i; 2] {
        let a_s = _mm512_xor_si512(a, _mm512_shuffle_epi32::<0x4E>(a));
        let b_s = _mm512_xor_si512(b, _mm512_shuffle_epi32::<0x4E>(b));
        let p0 = _mm512_clmulepi64_epi128::<0x00>(a, b);
        let p1 = _mm512_clmulepi64_epi128::<0x11>(a, b);
        let p01 = _mm512_clmulepi64_epi128::<0x00>(a_s, b_s);
        fold(p0, p1, p01, |x, y| _mm512_xor_si512(x, y), |p| times_x512(p))
    }

    /// The eight lane-wise products, unreduced: six carry-less multiplications.
    #[inline]
    #[target_feature(enable = "avx512f,avx512bw,vpclmulqdq")]
    fn mul(a: F128x8, b: F128x8) -> Acc8 {
        Acc8 {
            even: karatsuba_lanes(a.lo, b.lo),
            odd: karatsuba_lanes(a.hi, b.hi),
        }
    }

    /// Reduce every lane back to planes.
    #[inline]
    #[target_feature(enable = "avx512f,avx512bw")]
    fn reduce_planes(acc: Acc8) -> F128x8 {
        let [d0e, d1e] = acc.even;
        let [d0o, d1o] = acc.odd;
        let red = |x, y| reduce_lanes512(_mm512_unpacklo_epi64(x, y), _mm512_unpackhi_epi64(x, y));
        F128x8 {
            lo: red(d0e, d1e),
            hi: red(d0o, d1o),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_rng::Rng;

    #[test]
    fn kernels_match_the_scalar_forms() {
        let mut rng = Rng::new(0xF128_0008);
        for _ in 0..200 {
            let x0: [F128; 8] = core::array::from_fn(|_| rng.ext());
            let x1: [F128; 8] = core::array::from_fn(|_| rng.ext());
            let y0: [F128; 8] = core::array::from_fn(|_| rng.ext());
            let y1: [F128; 8] = core::array::from_fn(|_| rng.ext());
            let k0: [F64; 8] = core::array::from_fn(|_| F64(rng.next_u64()));
            let k1: [F64; 8] = core::array::from_fn(|_| F64(rng.next_u64()));
            let r = rng.ext();

            assert_eq!(
                fold_pairs8_ext(&x0, &x1, r),
                core::array::from_fn(|j| crate::multilinear::interp(x0[j], x1[j], r))
            );
            assert_eq!(fold_lones8_ext(&x0, r), core::array::from_fn(|j| x0[j] + r * x0[j]));

            let dot = |x: &[F128; 8], y: &[F128; 8]| (0..8).map(|j| x[j] * y[j]).sum();
            let (u0, u2) = msg_terms8_ext(&x0, &x1, &y0, &y1);
            assert_eq!(u0.reduce(), dot(&x0, &y0));
            let xs: [F128; 8] = core::array::from_fn(|j| x0[j] + x1[j]);
            let ys: [F128; 8] = core::array::from_fn(|j| y0[j] + y1[j]);
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
                F128x8::from_array(&x0),
                F128x8::from_array(&x1),
                F128x8::from_array(&y0),
            );
            assert_eq!(xa.to_array(), x0);
            assert_eq!(F128x8::splat(r).to_array(), [r; 8]);
            assert_eq!((xa + xb).to_array(), core::array::from_fn(|j| x0[j] + x1[j]));
            assert_eq!((xa * xb).to_array(), core::array::from_fn(|j| x0[j] * x1[j]));
            let sum = (xa.mul_unreduced(xb) ^ xc.mul_unreduced(xa)).reduce_lanes();
            assert_eq!(sum.to_array(), core::array::from_fn(|j| x0[j] * x1[j] + y0[j] * x0[j]));
            assert_eq!(xa.mul_unreduced(xb).reduce(), dot(&x0, &x1));
            let (even, odd) = F128x8::even_odd(xa, xb);
            assert_eq!(
                even.to_array(),
                core::array::from_fn(|j| if j < 4 { x0[2 * j] } else { x1[2 * (j - 4)] })
            );
            assert_eq!(
                odd.to_array(),
                core::array::from_fn(|j| if j < 4 { x0[2 * j + 1] } else { x1[2 * (j - 4) + 1] })
            );

            let (ka, kb) = (F64x8::from_array(&k0), F64x8::from_array(&k1));
            assert_eq!(
                F128x8::from(ka + kb).to_array(),
                core::array::from_fn(|j| F128::from(k0[j] + k1[j]))
            );
            assert_eq!(F128x8::from(ka).to_array(), k0.map(F128::from));
            assert_eq!(
                xa.mul_base_unreduced(ka).reduce_lanes().to_array(),
                core::array::from_fn(|j| x0[j].mul_base(k0[j]))
            );

            // Accumulation across calls sums before the one reduction.
            let mut acc = Acc8::from(x0[0].mul_unreduced(y1[0]));
            acc ^= msg_lone8_ext(&x0, &y0);
            acc ^= msg_lone8_ext(&x1, &y1);
            assert_eq!(acc.reduce(), x0[0] * y1[0] + dot(&x0, &y0) + dot(&x1, &y1));
        }
    }
}
