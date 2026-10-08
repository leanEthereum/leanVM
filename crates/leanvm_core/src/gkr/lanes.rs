//! Field elements in vector lanes, so that one kernel serves every target.

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
use primitives::multilinear::{store_packed, sum_packed};
use primitives::{F192, PrimeCharacteristicRing};
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
use primitives::{F192_LANES, F192Packed, PackedFieldExtension};
use std::mem::MaybeUninit;

/// The widest Plonky3 extension packing used by this kernel.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
pub(super) type Lane = F192Packed;
#[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2")))]
pub(super) type Lane = F192;

/// A value added by XOR: an element or an array of elements.
///
/// Field additions use the external backend; array additions are componentwise.
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

/// `WIDTH` elements of `E`, with arithmetic supplied by Plonky3.
pub(super) trait Lanes: Xor + PrimeCharacteristicRing {
    const WIDTH: usize;
    fn splat(x: F192) -> Self;
    fn load(values: &[F192]) -> Self;
    fn store(self, out: &mut [MaybeUninit<F192>]);
    fn sum_lanes(values: Self) -> F192;
    /// Child `c` of row `l` is placed in lane `l` of vector `c`.
    fn gather(values: &[F192], stride: usize) -> [Self; 4];
}

impl Xor for F192 {
    #[inline(always)]
    fn xor(self, rhs: Self) -> Self {
        self + rhs
    }
}
impl Lanes for F192 {
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
    fn sum_lanes(values: Self) -> F192 {
        values
    }
    #[inline(always)]
    fn gather(values: &[F192], _: usize) -> [Self; 4] {
        std::array::from_fn(|c| values[c])
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
impl Xor for F192Packed {
    #[inline(always)]
    fn xor(self, rhs: Self) -> Self {
        self + rhs
    }
}
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
impl Lanes for F192Packed {
    const WIDTH: usize = F192_LANES;
    #[inline(always)]
    fn splat(x: F192) -> Self {
        Self::from(x)
    }
    #[inline(always)]
    fn load(values: &[F192]) -> Self {
        // A final child row may contain fewer values than the backend width.
        if values.len() >= F192_LANES {
            Self::from_ext_slice(&values[..F192_LANES])
        } else {
            Self::from_ext_fn(|i| values.get(i).copied().unwrap_or(F192::ZERO))
        }
    }
    #[inline(always)]
    fn store(self, out: &mut [MaybeUninit<F192>]) {
        if out.len() >= F192_LANES {
            store_packed(self, out[..F192_LANES].as_mut_array().expect("one packed group"));
        } else {
            // Padding lanes carry no output slot.
            for (i, slot) in out.iter_mut().enumerate() {
                slot.write(self.extract(i));
            }
        }
    }
    #[inline(always)]
    fn sum_lanes(values: Self) -> F192 {
        sum_packed(values)
    }
    #[inline(always)]
    fn gather(values: &[F192], stride: usize) -> [Self; 4] {
        // Child c: [row_0[c], ..., row_(WIDTH-1)[c]].
        std::array::from_fn(|c| Self::from_ext_fn(|row| values[stride * row + c]))
    }
}
