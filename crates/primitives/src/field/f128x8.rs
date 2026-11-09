//! Eight-element `F128` kernels.
//!
//! These are the portable forms: eight elements as an array, products by the batched scalar kernels
//! (`mul4`, `mul_unreduced4`), which use the wide multiplier where the target has one.
//!
//! Products accumulate unreduced in [`Acc8`], one reduction per sum rather than per term.

use super::gf2_64::F64;
use super::gf2_64x2::{F128, F128Unreduced};

pub use portable::{F64x8, F128x8, Prod8};
pub use sum::Acc8;

/// The eight-lane types.
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

/// The dot-product accumulator.
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
    let xs: [F128; 8] = core::array::from_fn(|j| x0[j] + x1[j]);
    let ys: [F128; 8] = core::array::from_fn(|j| y0[j] + y1[j]);
    (sum::dot_ext(x0, y0), sum::dot_ext(&xs, &ys))
}

/// `sum x0*y0` over eight terms.
#[inline(always)]
pub fn msg_lone8_ext(x0: &[F128; 8], y0: &[F128; 8]) -> Acc8 {
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
            let mut acc = Acc8::ZERO;
            acc ^= msg_lone8_ext(&x0, &y0);
            acc ^= msg_lone8_ext(&x1, &y1);
            assert_eq!(acc.reduce(), dot(&x0, &y0) + dot(&x1, &y1));
        }
    }
}
