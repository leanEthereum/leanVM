//! Eight-element `F128` helpers, lane by lane over plain arrays.
//!
//! Products accumulate unreduced in [`Acc8`], one reduction per sum rather than per term.

use super::gf2_64::F64;
use super::gf2_64x2::{F128, F128Unreduced};

/// Eight elements.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct F128x8([F128; 8]);

// SAFETY: `repr(transparent)` over an array of plain elements.
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

    /// The eight products `self_i * rhs_i`, unreduced.
    #[inline]
    pub fn mul_unreduced(self, rhs: Self) -> Prod8 {
        Prod8(core::array::from_fn(|i| self.0[i].mul_unreduced(rhs.0[i])))
    }

    /// The eight mixed products `self_i * k_i`, unreduced.
    #[inline]
    pub fn mul_base_unreduced(self, k: F64x8) -> Prod8 {
        Prod8(core::array::from_fn(|i| self.0[i].mul_base_unreduced(k.0[i])))
    }

    /// `([a0, a2, a4, a6, b0, b2, b4, b6], [a1, a3, a5, a7, b1, b3, b5, b7])`.
    #[inline]
    pub fn even_odd(a: Self, b: Self) -> (Self, Self) {
        let pick = |parity: usize| {
            Self(core::array::from_fn(|i| {
                let src = if i < 4 { &a.0 } else { &b.0 };
                src[2 * (i % 4) + parity]
            }))
        };
        (pick(0), pick(1))
    }
}

impl core::ops::Mul for F128x8 {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|i| self.0[i] * rhs.0[i]))
    }
}

impl core::ops::Add for F128x8 {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|i| self.0[i] + rhs.0[i]))
    }
}

/// The embedding of the base field.
impl From<F64x8> for F128x8 {
    #[inline]
    fn from(k: F64x8) -> Self {
        Self(k.0.map(F128::from))
    }
}

/// Eight base-field elements.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct F64x8([F64; 8]);

// SAFETY: `repr(transparent)` over an array of plain elements.
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

/// The unreduced products of eight elements, lane by lane: what [`F128x8::mul_unreduced`] returns.
/// A sum of them is an XOR, and [`Prod8::reduce_lanes`] reduces each lane on its own.
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

/// An unreduced sum of products.
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

/// `sum x_i * y_i` over eight terms, unreduced.
#[inline]
fn dot(x: &[F128; 8], y: &[F128; 8]) -> Acc8 {
    Acc8(
        x.iter()
            .zip(y)
            .fold(F128Unreduced::ZERO, |sum, (x, &y)| sum ^ x.mul_unreduced(y)),
    )
}

/// `x0 + r * (x0 + x1)`, elementwise.
#[inline]
pub fn fold_pairs8_ext(x0: &[F128; 8], x1: &[F128; 8], r: F128) -> [F128; 8] {
    core::array::from_fn(|i| x0[i] + r * (x0[i] + x1[i]))
}

/// `x0 + r * x0`, elementwise.
#[inline]
pub fn fold_lones8_ext(x0: &[F128; 8], r: F128) -> [F128; 8] {
    core::array::from_fn(|i| x0[i] + r * x0[i])
}

/// `(sum x0*y0, sum (x0+x1)*(y0+y1))` over eight terms.
#[inline]
pub fn msg_terms8_ext(x0: &[F128; 8], x1: &[F128; 8], y0: &[F128; 8], y1: &[F128; 8]) -> (Acc8, Acc8) {
    let xs: [F128; 8] = core::array::from_fn(|j| x0[j] + x1[j]);
    let ys: [F128; 8] = core::array::from_fn(|j| y0[j] + y1[j]);
    (dot(x0, y0), dot(&xs, &ys))
}

/// `sum x0*y0` over eight terms.
#[inline]
pub fn msg_lone8_ext(x0: &[F128; 8], y0: &[F128; 8]) -> Acc8 {
    dot(x0, y0)
}

/// The eight mixed products `c * k_i`, unreduced.
#[inline]
pub fn mul_base_splat8(c: F128, k: &[F64; 8]) -> Prod8 {
    Prod8(k.map(|k| c.mul_base_unreduced(k)))
}

/// `out[i] += add[i]` over eight elements.
#[inline]
pub fn xor_into8(out: &mut [F128; 8], add: &[F128; 8]) {
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
            let mut acc = Acc8::from(x0[0].mul_unreduced(y1[0]));
            acc ^= msg_lone8_ext(&x0, &y0);
            acc ^= msg_lone8_ext(&x1, &y1);
            assert_eq!(acc.reduce(), x0[0] * y1[0] + dot(&x0, &y0) + dot(&x1, &y1));
        }
    }
}
