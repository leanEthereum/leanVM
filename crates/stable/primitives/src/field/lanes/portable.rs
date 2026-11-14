//! The lanes as arrays of scalars, for a target without a vector carry-less multiplier: each lane is the scalar
//! operation, so this backend is also the reference the others are tested against.

use crate::field::gf2_64::mul_wide;
use crate::field::{F64, F128, F128Unreduced};

/// Eight `K` elements.
#[derive(Clone, Copy, Debug)]
pub struct F64x8([F64; 8]);

/// Eight `E` elements.
#[derive(Clone, Copy, Debug)]
pub struct F128x8([F128; 8]);

/// Eight unreduced `E` sums of products.
#[derive(Clone, Copy, Debug)]
pub struct Acc8([F128Unreduced; 8]);

/// One product, the scalar [`F128`] multiply.
#[inline(always)]
pub(crate) fn mul(a: F128, b: F128) -> F128 {
    a.mul_unreduced(b).reduce()
}

/// The eight carry-less products `a[i] * b[i]`, each 128 bits.
#[inline]
pub fn clmul8(a: [u64; 8], b: [u64; 8]) -> [u128; 8] {
    core::array::from_fn(|i| mul_wide(a[i], b[i]))
}

/// The low 64 bits of the eight carry-less products `a[i] * b[i]`.
#[inline]
pub fn clmul8_low(a: [u64; 8], b: [u64; 8]) -> [u64; 8] {
    clmul8(a, b).map(|p| p as u64)
}

impl F64x8 {
    pub const ZERO: Self = Self([F64::ZERO; 8]);

    #[inline(always)]
    pub fn splat(k: F64) -> Self {
        Self([k; 8])
    }

    #[inline(always)]
    pub fn from_array(k: &[F64; 8]) -> Self {
        Self(*k)
    }

    #[inline(always)]
    pub fn to_array(self) -> [F64; 8] {
        self.0
    }

    #[inline(always)]
    pub(super) fn xor(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|i| self.0[i] + rhs.0[i]))
    }

    #[inline(always)]
    pub(super) fn product(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|i| self.0[i] * rhs.0[i]))
    }
}

impl F128x8 {
    pub const ZERO: Self = Self([F128::ZERO; 8]);

    #[inline(always)]
    pub fn splat(e: F128) -> Self {
        Self([e; 8])
    }

    #[inline(always)]
    pub fn from_array(e: &[F128; 8]) -> Self {
        Self(*e)
    }

    #[inline(always)]
    pub fn to_array(self) -> [F128; 8] {
        self.0
    }

    /// The eight products, unreduced.
    #[inline(always)]
    pub fn mul_unreduced(self, rhs: Self) -> Acc8 {
        Acc8(core::array::from_fn(|i| self.0[i].mul_unreduced(rhs.0[i])))
    }

    /// The eight mixed products `self[i] * k[i]`.
    #[inline(always)]
    pub fn mul_base(self, k: F64x8) -> Self {
        Self(core::array::from_fn(|i| self.0[i].mul_base(k.0[i])))
    }

    /// The eight mixed products `self[i] * k[i]`, unreduced.
    #[inline(always)]
    pub fn mul_base_unreduced(self, k: F64x8) -> Acc8 {
        Acc8(core::array::from_fn(|i| self.0[i].mul_base_unreduced(k.0[i])))
    }

    #[inline(always)]
    pub(super) fn xor(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|i| self.0[i] + rhs.0[i]))
    }

    #[inline(always)]
    pub(super) fn product(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|i| self.0[i] * rhs.0[i]))
    }
}

impl Acc8 {
    pub const ZERO: Self = Self([F128Unreduced::ZERO; 8]);

    /// The eight sums as they are, unreduced.
    #[inline(always)]
    pub fn to_array(self) -> [F128Unreduced; 8] {
        self.0
    }

    /// Every lane reduced.
    #[inline(always)]
    pub fn reduce(self) -> F128x8 {
        F128x8(self.0.map(F128Unreduced::reduce))
    }

    /// The sum of the eight lanes, reduced once.
    #[inline(always)]
    pub fn sum(self) -> F128 {
        self.0.into_iter().fold(F128Unreduced::ZERO, |s, x| s ^ x).reduce()
    }

    #[inline(always)]
    pub(super) fn xor(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|i| self.0[i] ^ rhs.0[i]))
    }
}
