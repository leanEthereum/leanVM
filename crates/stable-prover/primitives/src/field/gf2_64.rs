// CREDIT: https://github.com/binius-zk/binius64, Apache-2.0.
//! The base field `K = GF(2)[x] / (x^64 + x^4 + x^3 + x + 1)`, in which `x` has order `2^64 - 1`.
//!
//! A product is one carry-less 64x64 multiplication ([`mul_wide`]) followed by a reduction (`reduce`).

use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Mul, MulAssign};

pub use super::lanes::mul_wide;

/// Reduction constant of the base field: `x^64 = x^4 + x^3 + x + 1 = 0x1B`.
pub(crate) const R64: u64 = 0x1B;

/// A GF(2^64) element; bit i = coefficient of x^i.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct F64(pub u64);

impl F64 {
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);
    /// The generator `g = x`, with `ord(g) = 2^64 - 1`, larger than every index an admissible instance uses (§sec:vm).
    ///
    /// For `k < 64`, `g^k` is the monomial `x^k` (bit `k`), which the WOTS+C encoding check relies on.
    pub const G: Self = Self(2);

    #[inline]
    pub const fn is_zero(self) -> bool {
        self.0 == 0
    }

    #[inline]
    pub fn square(self) -> Self {
        self * self
    }

    /// `self^e` by square-and-multiply, low bit first: `O(log e)` products.
    ///
    /// The exponent is wider than the order `2^64 - 1`, so a caller need not reduce it first.
    #[inline]
    #[must_use]
    pub fn pow(self, mut e: u128) -> Self {
        let (mut result, mut base) = (Self::ONE, self);
        while e > 0 {
            if e & 1 == 1 {
                result *= base;
            }
            base = base.square();
            e >>= 1;
        }
        result
    }

    /// Multiplicative inverse `x^(2^64 - 2)`, mapping zero to zero, by Itoh-Tsujii: each `t_k = x^(2^k - 1)` comes
    /// from two shorter ones, so the exponent costs 63 squarings and 8 products.
    pub fn inv(self) -> Self {
        let sq = |mut v: Self, n: u32| {
            for _ in 0..n {
                v = v.square();
            }
            v
        };
        let t1 = self;
        let t2 = sq(t1, 1) * t1;
        let t3 = sq(t2, 1) * t1;
        let t6 = sq(t3, 3) * t3;
        let t12 = sq(t6, 6) * t6;
        let t24 = sq(t12, 12) * t12;
        let t48 = sq(t24, 24) * t24;
        let t60 = sq(t48, 12) * t12;
        let t63 = sq(t60, 3) * t3;
        sq(t63, 1)
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl Add for F64 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0)
    }
}

#[allow(clippy::suspicious_op_assign_impl)]
impl AddAssign for F64 {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.0 ^= rhs.0;
    }
}

impl Mul for F64 {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        Self(reduce(mul_wide(self.0, rhs.0)))
    }
}

impl MulAssign for F64 {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl Sum for F64 {
    #[inline]
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |acc, x| acc + x)
    }
}

impl<'a> Sum<&'a F64> for F64 {
    #[inline]
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.copied().sum()
    }
}

impl Product for F64 {
    #[inline]
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ONE, |acc, x| acc * x)
    }
}

impl<'a> Product<&'a F64> for F64 {
    #[inline]
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.copied().product()
    }
}

/// Reduce a 128-bit carry-less product modulo `x^64 + x^4 + x^3 + x + 1`.
///
/// Write the product as `lo + hi * x^64` and substitute `x^64 = x^4 + x^3 + x + 1`:
///
/// ```text
///     hi * x^64  =  hi ^ hi<<1 ^ hi<<3 ^ hi<<4        (a 68-bit value)
///     spill      =  hi>>63 ^ hi>>61 ^ hi>>60          (its 4 bits past x^63)
///     spill * x^64 fits in 8 bits, so a second fold is exact and final.
///
///     result = lo ^ f(hi ^ spill),   f(v) = v ^ v<<1 ^ v<<3 ^ v<<4  (mod 2^64)
/// ```
///
/// The two folds merge into one because the truncated map `f` is GF(2)-linear.
#[inline]
pub(crate) const fn reduce(p: u128) -> u64 {
    let (lo, hi) = (p as u64, (p >> 64) as u64);
    let spill = (hi >> 63) ^ (hi >> 61) ^ (hi >> 60);
    let v = hi ^ spill;
    lo ^ v ^ (v << 1) ^ (v << 3) ^ (v << 4)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_rng::Rng;

    /// Independent Python reference vectors: (a, b, a * b).
    const VECTORS: [(u64, u64, u64); 3] = [
        (0x01090913877ed8ed, 0x66ab35ac2768468f, 0x50c4519dc383744a),
        (0xa7715ae18f12a3b5, 0x05743059f43fa4f5, 0xeb64cd9cd9cda6df),
        (0xbd3efb4705e79ddd, 0x3aff618604de4ae0, 0xc3d7a95fa9cb59bb),
    ];

    /// Operands that exercise the reduction's spill: the top bits set, all bits set, and the identities.
    const CORNERS: [u64; 6] = [0, 1, u64::MAX, 1 << 63, 0xF000_0000_0000_0000, R64];

    /// Reference product: shift and add, `a_i * b * x^i` for each bit `i` of `a`, `b * x^i` reduced a step at a time.
    fn reference_mul(a: u64, b: u64) -> u64 {
        let (mut acc, mut shifted) = (0, b);
        for i in 0..64 {
            if (a >> i) & 1 != 0 {
                acc ^= shifted;
            }
            shifted = (shifted << 1) ^ (R64 * (shifted >> 63));
        }
        acc
    }

    #[test]
    fn python_vectors() {
        for (a, b, c) in VECTORS {
            assert_eq!(F64(a) * F64(b), F64(c));
            assert_eq!(reference_mul(a, b), c);
        }
    }

    #[test]
    fn mul_and_square_match_the_reference() {
        let mut rng = Rng::new(1);
        // Random operands, then every pair of corners.
        let random = (0..10_000).map(|_| (rng.next_u64(), rng.next_u64()));
        let corners = CORNERS.iter().flat_map(|&a| CORNERS.iter().map(move |&b| (a, b)));
        for (a, b) in random.chain(corners) {
            let want = reference_mul(a, b);
            assert_eq!((F64(a) * F64(b)).0, want);
            assert_eq!(F64(a).square(), F64(reference_mul(a, a)));
        }
    }

    #[test]
    fn inverses() {
        let mut rng = Rng::new(2);
        // Random elements, then the nonzero corners.
        let elements = (0..200).map(|_| rng.next_u64()).chain(CORNERS.into_iter().skip(1));
        for a in elements.map(F64) {
            assert_eq!(a * a.inv(), F64::ONE);
        }
        // Zero has no inverse and maps to zero by convention.
        assert_eq!(F64::ZERO.inv(), F64::ZERO);
    }

    #[test]
    fn pow_matches_repeated_products() {
        let mut rng = Rng::new(3);
        let a = F64(rng.next_u64());
        // Small exponents against a running product: 0 gives one, 1 gives `a`.
        let mut want = F64::ONE;
        for e in 0..70u128 {
            assert_eq!(a.pow(e), want, "a^{e}");
            want *= a;
        }
        // Exponents past 64 bits: `a^(2^64) = a` in GF(2^64), and the order `2^64 - 1` wraps.
        let order: u128 = (1 << 64) - 1;
        assert_eq!(a.pow(1 << 64), a);
        assert_eq!(a.pow(order + 5), a.pow(5));
        assert_eq!(a.pow(u128::MAX), a.pow(u128::MAX % order));
        // Zero to a positive power stays zero.
        assert_eq!(F64::ZERO.pow(order), F64::ZERO);
    }

    /// x is primitive: x^((2^64−1)/q) ≠ 1 for every prime q | 2^64 − 1.
    #[test]
    fn x_is_primitive() {
        let n: u128 = (1 << 64) - 1;
        for q in [3u128, 5, 17, 257, 641, 65537, 6700417] {
            assert_ne!(F64::G.pow(n / q), F64::ONE, "x^((2^64-1)/{q}) == 1");
        }
        // The full order closes the cycle.
        assert_eq!(F64::G.pow(n), F64::ONE);
    }
}
