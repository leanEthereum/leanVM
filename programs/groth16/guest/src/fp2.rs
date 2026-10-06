//! `F_p2 = F_p[u] / (u^2 + 1)`, where G2's coordinates live.

use crate::fp::Fp;

/// `c0 + c1 u`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Fp2 {
    pub c0: Fp,
    pub c1: Fp,
}

impl Fp2 {
    pub const ZERO: Self = Self::new(Fp::ZERO, Fp::ZERO);
    pub const ONE: Self = Self::new(Fp::ONE, Fp::ZERO);

    pub const fn new(c0: Fp, c1: Fp) -> Self {
        Self { c0, c1 }
    }

    /// A constant's element, from the canonical limbs of `c0` and `c1`.
    pub const fn constant(c0: [u64; 4], c1: [u64; 4]) -> Self {
        Self::new(Fp::constant(c0), Fp::constant(c1))
    }

    pub const fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero()
    }

    #[inline(always)]
    pub const fn add(&self, rhs: &Self) -> Self {
        Self::new(self.c0.add(&rhs.c0), self.c1.add(&rhs.c1))
    }

    #[inline(always)]
    pub const fn sub(&self, rhs: &Self) -> Self {
        Self::new(self.c0.sub(&rhs.c0), self.c1.sub(&rhs.c1))
    }

    #[inline(always)]
    pub const fn double(&self) -> Self {
        Self::new(self.c0.double(), self.c1.double())
    }

    #[inline(always)]
    pub const fn neg(&self) -> Self {
        Self::new(self.c0.neg(), self.c1.neg())
    }

    /// `c0 - c1 u`, the Frobenius map `x^p`.
    #[inline(always)]
    pub const fn conjugate(&self) -> Self {
        Self::new(self.c0, self.c1.neg())
    }

    /// Karatsuba: three products.
    #[inline(always)]
    pub const fn mul(&self, rhs: &Self) -> Self {
        let v0 = self.c0.mul(&rhs.c0);
        let v1 = self.c1.mul(&rhs.c1);
        let s = self.c0.add(&self.c1).mul(&rhs.c0.add(&rhs.c1));
        Self::new(v0.sub(&v1), s.sub(&v0).sub(&v1))
    }

    /// `(c0 + c1)(c0 - c1) + 2 c0 c1 u`: two products.
    #[inline(always)]
    pub const fn square(&self) -> Self {
        let a = self.c0.add(&self.c1).mul(&self.c0.sub(&self.c1));
        let b = self.c0.mul(&self.c1);
        Self::new(a, b.double())
    }

    #[inline(always)]
    pub const fn mul_by_fp(&self, k: &Fp) -> Self {
        Self::new(self.c0.mul(k), self.c1.mul(k))
    }

    /// The product by `xi = 9 + u`, the non-residue that builds `F_p6`: no product.
    #[inline(always)]
    pub const fn mul_by_xi(&self) -> Self {
        Self::new(nine(&self.c0).sub(&self.c1), nine(&self.c1).add(&self.c0))
    }

    /// `x^(p^k)`.
    pub const fn frobenius(&self, k: usize) -> Self {
        if k % 2 == 1 { self.conjugate() } else { *self }
    }

    /// `(c0 - c1 u) / (c0^2 + c1^2)`; zero has none.
    pub const fn inverse(&self) -> Option<Self> {
        match self.c0.square().add(&self.c1.square()).inverse() {
            Some(t) => Some(Self::new(self.c0.mul(&t), self.c1.neg().mul(&t))),
            None => None,
        }
    }
}

/// `9 x`, by three doublings.
#[inline(always)]
const fn nine(x: &Fp) -> Fp {
    x.double().double().double().add(x)
}
