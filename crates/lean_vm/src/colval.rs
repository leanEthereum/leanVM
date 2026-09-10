//! Column operations shared by the `F64` joining round and subsequent `F192` rounds.

use primitives::field::{F64, F192, F192BaseUnreduced, F192Unreduced};
use std::ops::{Add, BitXor, BitXorAssign, Mul};

/// A value a constraint reads out of a column.
pub trait ColVal: Copy + Send + Sync + Add<Output = Self> + Mul<Output = Self> {
    const ZERO: Self;
    const ONE: Self;

    /// Where this column's products XOR-accumulate before the one reduction that
    /// ends a form.
    type Unreduced: Copy + Send + Sync + BitXor<Output = Self::Unreduced> + BitXorAssign;

    /// Times an `E` value: an `η`-power, a bus coefficient, a machine word.
    fn mul_e(self, e: F192) -> F192;

    /// The same product, left for the caller to accumulate.
    fn mul_e_unreduced(self, e: F192) -> Self::Unreduced;

    /// An already-reduced `E` value as an accumulator term; exact, because
    /// reducing a reduced value fixes it.
    fn lift(e: F192) -> Self::Unreduced;

    fn reduce(acc: Self::Unreduced) -> F192;

    /// `Σ coeffs[i]·vals[i]`, unreduced.
    fn dot_unreduced(coeffs: &[F192], vals: &[Self]) -> Self::Unreduced;

    /// `constant + Σ coeffs[i]·vals[i]`, one reduction for the whole slice.
    #[inline(always)]
    fn dot(coeffs: &[F192], vals: &[Self], constant: F192) -> F192 {
        Self::reduce(Self::dot_unreduced(coeffs, vals) ^ Self::lift(constant))
    }
}

impl ColVal for F64 {
    const ZERO: Self = F64::ZERO;
    const ONE: Self = F64::ONE;

    type Unreduced = F192BaseUnreduced;

    #[inline(always)]
    fn mul_e(self, e: F192) -> F192 {
        e.mul_base(self)
    }

    #[inline(always)]
    fn mul_e_unreduced(self, e: F192) -> Self::Unreduced {
        e.mul_base_unreduced(self)
    }

    #[inline(always)]
    fn lift(e: F192) -> Self::Unreduced {
        F192BaseUnreduced {
            p0: e.c0 as u128,
            p1: e.c1 as u128,
            p2: e.c2 as u128,
        }
    }

    #[inline(always)]
    fn reduce(acc: Self::Unreduced) -> F192 {
        acc.reduce()
    }

    #[inline(always)]
    fn dot_unreduced(coeffs: &[F192], vals: &[Self]) -> Self::Unreduced {
        coeffs
            .iter()
            .zip(vals)
            .fold(F192BaseUnreduced::ZERO, |acc, (&w, &v)| acc ^ w.mul_base_unreduced(v))
    }
}

impl ColVal for F192 {
    const ZERO: Self = F192::ZERO;
    const ONE: Self = F192::ONE;

    type Unreduced = F192Unreduced;

    #[inline(always)]
    fn mul_e(self, e: F192) -> F192 {
        self * e
    }

    #[inline(always)]
    fn mul_e_unreduced(self, e: F192) -> Self::Unreduced {
        self.mul_unreduced(e)
    }

    #[inline(always)]
    fn lift(e: F192) -> Self::Unreduced {
        F192Unreduced {
            w: [e.c0, 0, e.c1, 0, e.c2, 0, 0, 0, 0, 0],
        }
    }

    #[inline(always)]
    fn reduce(acc: Self::Unreduced) -> F192 {
        acc.reduce()
    }

    #[inline(always)]
    fn dot_unreduced(coeffs: &[F192], vals: &[Self]) -> Self::Unreduced {
        coeffs
            .iter()
            .zip(vals)
            .fold(F192Unreduced::ZERO, |acc, (&w, &v)| acc ^ w.mul_unreduced(v))
    }
}
