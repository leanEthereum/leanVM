//! Field elements in vector lanes, so that one kernel serves every target.

use primitives::field::{F192, F192Unreduced};
#[cfg(any(
    all(target_arch = "aarch64", target_feature = "aes"),
    all(target_arch = "x86_64", target_feature = "pclmulqdq")
))]
use primitives::field::{F192x1, F192x1Unreduced};
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
use primitives::field::{F192x4, F192x4Unreduced};
use std::mem::MaybeUninit;
use std::ops::{Add, Mul};

/// The widest lanes the target multiplies in.
///
/// - Four elements per vector with VPCLMULQDQ.
/// - One element held in vector registers with PCLMULQDQ or PMULL.
/// - The portable element elsewhere.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
pub(super) type Lane = F192x4;

/// The widest lanes the target multiplies in.
#[cfg(all(
    any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(target_arch = "x86_64", target_feature = "pclmulqdq")
    ),
    not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))
))]
pub(super) type Lane = F192x1;

/// The widest lanes the target multiplies in.
#[cfg(not(any(
    all(target_arch = "aarch64", target_feature = "aes"),
    all(target_arch = "x86_64", target_feature = "pclmulqdq")
)))]
pub(super) type Lane = F192;

/// A value added by XOR: an element, an unreduced product, or an array of them.
///
/// In characteristic two every sum is a XOR, reduced or not.
pub(super) trait Xor: Copy {
    fn xor(self, rhs: Self) -> Self;
}

impl<T: Xor, const N: usize> Xor for [T; N] {
    #[inline(always)]
    fn xor(self, rhs: Self) -> Self {
        std::array::from_fn(|i| self[i].xor(rhs[i]))
    }
}

/// A polynomial as its coefficients, lowest degree first.
///
/// The product is Karatsuba's, over any product of the coefficients.
/// Nesting it multiplies polynomials in two variables.
///
/// Karatsuba's products are combined by sums alone.
/// So products summed over many operands can be combined once, after the sum.
pub(super) trait Polynomial: Copy {
    /// One coefficient.
    type Coeff;

    /// Karatsuba's products, before they are combined.
    type Terms<P>;

    /// The coefficients of a product.
    type Product<P>;

    /// Karatsuba's products of the two polynomials, each formed by the given coefficient product.
    fn terms<P>(self, rhs: Self, mul: impl Fn(Self::Coeff, Self::Coeff) -> P) -> Self::Terms<P>;

    /// The product's coefficients, from its terms or from a sum of terms.
    fn combine<P: Xor>(terms: Self::Terms<P>) -> Self::Product<P>;

    /// The product's coefficients.
    #[inline(always)]
    fn product<P: Xor>(self, rhs: Self, mul: impl Fn(Self::Coeff, Self::Coeff) -> P) -> Self::Product<P> {
        Self::combine(self.terms(rhs, mul))
    }
}

impl<T: Xor> Polynomial for [T; 2] {
    type Coeff = T;
    type Terms<P> = [P; 3];
    type Product<P> = [P; 3];

    /// The two products of equal degrees, then the product of the sums.
    #[inline(always)]
    fn terms<P>(self, rhs: Self, mul: impl Fn(T, T) -> P) -> [P; 3] {
        let ([u0, u1], [w0, w1]) = (self, rhs);
        [mul(u0, w0), mul(u1, w1), mul(u0.xor(u1), w0.xor(w1))]
    }

    /// The product of the sums holds the cross term and both of the others.
    #[inline(always)]
    fn combine<P: Xor>([low, high, sum]: [P; 3]) -> [P; 3] {
        [low, sum.xor(low).xor(high), high]
    }
}

impl<T: Xor> Polynomial for [T; 3] {
    type Coeff = T;
    type Terms<P> = [P; 6];
    type Product<P> = [P; 5];

    /// The three products of equal degrees, then the product of each pair's sums.
    #[inline(always)]
    fn terms<P>(self, rhs: Self, mul: impl Fn(T, T) -> P) -> [P; 6] {
        let sum = |i: usize, j: usize| mul(self[i].xor(self[j]), rhs[i].xor(rhs[j]));
        [
            mul(self[0], rhs[0]),
            mul(self[1], rhs[1]),
            mul(self[2], rhs[2]),
            sum(0, 1),
            sum(0, 2),
            sum(1, 2),
        ]
    }

    /// Each pair's sum holds its cross term and the two products of equal degrees.
    #[inline(always)]
    fn combine<P: Xor>([z0, z1, z2, s01, s02, s12]: [P; 6]) -> [P; 5] {
        [
            z0,
            s01.xor(z0).xor(z1),
            s02.xor(z0).xor(z2).xor(z1),
            s12.xor(z1).xor(z2),
            z2,
        ]
    }
}

/// `WIDTH` elements of `E` in vector registers, with lane-wise arithmetic.
pub(super) trait Lanes: Xor + Add<Output = Self> + Mul<Output = Self> {
    /// Lane-wise products before their reduction, summed by XOR.
    type Wide: Xor;

    /// The number of lanes.
    const WIDTH: usize;

    /// `x` in every lane.
    fn splat(x: F192) -> Self;

    /// The first `WIDTH` elements of `values`, element `l` in lane `l`.
    fn load(values: &[F192]) -> Self;

    /// Lane `l` to `out[l]`.
    fn store(self, out: &mut [MaybeUninit<F192>]);

    /// The lane-wise products, unreduced.
    fn mul_wide(self, rhs: Self) -> Self::Wide;

    /// The unreduced zero.
    fn zero_wide() -> Self::Wide;

    /// The sum of the lanes.
    fn sum(wide: Self::Wide) -> F192Unreduced;

    /// The four children of `WIDTH` rows placed `stride` elements apart.
    ///
    /// Vector `c` holds child `c`, of row `l` in lane `l`.
    fn gather(values: &[F192], stride: usize) -> [Self; 4];
}

impl Xor for F192 {
    #[inline(always)]
    fn xor(self, rhs: Self) -> Self {
        self + rhs
    }
}

impl Xor for F192Unreduced {
    #[inline(always)]
    fn xor(self, rhs: Self) -> Self {
        self ^ rhs
    }
}

impl Lanes for F192 {
    type Wide = F192Unreduced;
    const WIDTH: usize = 1;

    #[inline(always)]
    fn splat(x: F192) -> Self {
        x
    }

    #[inline(always)]
    fn load(values: &[F192]) -> Self {
        values[0]
    }

    #[inline(always)]
    fn store(self, out: &mut [MaybeUninit<F192>]) {
        out[0].write(self);
    }

    #[inline(always)]
    fn mul_wide(self, rhs: Self) -> F192Unreduced {
        self.mul_unreduced(rhs)
    }

    #[inline(always)]
    fn zero_wide() -> F192Unreduced {
        F192Unreduced::ZERO
    }

    #[inline(always)]
    fn sum(wide: F192Unreduced) -> F192Unreduced {
        wide
    }

    #[inline(always)]
    fn gather(values: &[F192], _: usize) -> [Self; 4] {
        std::array::from_fn(|c| values[c])
    }
}

#[cfg(any(
    all(target_arch = "aarch64", target_feature = "aes"),
    all(target_arch = "x86_64", target_feature = "pclmulqdq")
))]
impl Xor for F192x1 {
    #[inline(always)]
    fn xor(self, rhs: Self) -> Self {
        self + rhs
    }
}

#[cfg(any(
    all(target_arch = "aarch64", target_feature = "aes"),
    all(target_arch = "x86_64", target_feature = "pclmulqdq")
))]
impl Xor for F192x1Unreduced {
    #[inline(always)]
    fn xor(self, rhs: Self) -> Self {
        self ^ rhs
    }
}

/// One element kept in vector registers from its load to its store.
///
/// The portable element's integer words would move out of them at every sum.
#[cfg(any(
    all(target_arch = "aarch64", target_feature = "aes"),
    all(target_arch = "x86_64", target_feature = "pclmulqdq")
))]
impl Lanes for F192x1 {
    type Wide = F192x1Unreduced;
    const WIDTH: usize = 1;

    #[inline(always)]
    fn splat(x: F192) -> Self {
        Self::new(x)
    }

    #[inline(always)]
    fn load(values: &[F192]) -> Self {
        Self::load(&values[0])
    }

    #[inline(always)]
    fn store(self, out: &mut [MaybeUninit<F192>]) {
        self.store(&mut out[0]);
    }

    #[inline(always)]
    fn mul_wide(self, rhs: Self) -> F192x1Unreduced {
        self.mul_unreduced(rhs)
    }

    #[inline(always)]
    fn zero_wide() -> F192x1Unreduced {
        F192x1Unreduced::zero()
    }

    #[inline(always)]
    fn sum(wide: F192x1Unreduced) -> F192Unreduced {
        wide.into()
    }

    #[inline(always)]
    fn gather(values: &[F192], _: usize) -> [Self; 4] {
        std::array::from_fn(|c| Self::load(&values[c]))
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
impl Xor for F192x4 {
    #[inline(always)]
    fn xor(self, rhs: Self) -> Self {
        self + rhs
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
impl Xor for F192x4Unreduced {
    #[inline(always)]
    fn xor(self, rhs: Self) -> Self {
        self ^ rhs
    }
}

/// Four elements, one per 128-bit lane.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
impl Lanes for F192x4 {
    type Wide = F192x4Unreduced;
    const WIDTH: usize = 4;

    #[inline(always)]
    fn splat(x: F192) -> Self {
        Self::splat(x)
    }

    #[inline(always)]
    fn load(values: &[F192]) -> Self {
        Self::load(values[..4].as_array().expect("four elements"))
    }

    #[inline(always)]
    fn store(self, out: &mut [MaybeUninit<F192>]) {
        self.store(out[..4].as_mut_array().expect("four slots"));
    }

    #[inline(always)]
    fn mul_wide(self, rhs: Self) -> F192x4Unreduced {
        self.mul_unreduced(rhs)
    }

    #[inline(always)]
    fn zero_wide() -> F192x4Unreduced {
        F192x4Unreduced::zero()
    }

    #[inline(always)]
    fn sum(wide: F192x4Unreduced) -> F192Unreduced {
        wide.sum()
    }

    /// Each row loads with its children in lanes, then one transpose puts the rows in lanes.
    #[inline(always)]
    fn gather(values: &[F192], stride: usize) -> [Self; 4] {
        Self::transpose(std::array::from_fn(|row| {
            <Self as Lanes>::load(&values[stride * row..])
        }))
    }
}
