//! The portable products: integer code with no SIMD intrinsic or assembly, the same on every target.

use super::{F192, F192Unreduced};
use crate::field::gf2_64::portable::{clmul, spread};
use crate::field::gf2_64::{F64, reduce as reduce_wide};

/// Karatsuba: six base products into the five coefficients of `y^0..y^4`, then the `y`-fold.
#[inline]
pub const fn mul_unreduced(a: F192, b: F192) -> F192Unreduced {
    let (p0, p1, p2) = (clmul(a.c0, b.c0), clmul(a.c1, b.c1), clmul(a.c2, b.c2));
    let p01 = clmul(a.c0 ^ a.c1, b.c0 ^ b.c1);
    let p02 = clmul(a.c0 ^ a.c2, b.c0 ^ b.c2);
    let p12 = clmul(a.c1 ^ a.c2, b.c1 ^ b.c2);
    // `a_i b_j + a_j b_i = p_ij + p_i + p_j` lands on `y^(i + j)`.
    let (e1, e2, e3) = (p01 ^ p0 ^ p1, p02 ^ p0 ^ p2 ^ p1, p12 ^ p1 ^ p2);
    // `y^3 = y + 1` and `y^4 = y^2 + y`.
    F192Unreduced::from_wide([p0 ^ e3, e1 ^ e3 ^ p2, e2 ^ p2])
}

/// Each coefficient reduced modulo the base polynomial.
#[inline]
pub const fn reduce(u: F192Unreduced) -> F192 {
    const fn wide([lo, hi]: [u64; 2]) -> u64 {
        reduce_wide((hi as u128) << 64 | lo as u128)
    }
    let [c0, c1, c2] = u.coeffs;
    F192::new(wide(c0), wide(c1), wide(c2))
}

#[inline]
pub const fn mul(a: F192, b: F192) -> F192 {
    reduce(mul_unreduced(a, b))
}

/// Three base-field squares: `(c0 + c1 y + c2 y^2)^2 = c0^2 + c2^2 y + (c1^2 + c2^2) y^2`.
#[inline]
pub const fn square(a: F192) -> F192 {
    let (s0, s1, s2) = (spread(a.c0), spread(a.c1), spread(a.c2));
    reduce(F192Unreduced::from_wide([s0, s2, s1 ^ s2]))
}

/// The three coefficients times one base-field scalar.
#[inline]
pub const fn mul_base(a: F192, k: F64) -> F192 {
    F192::new(
        F64(a.c0).mul_portable(k).0,
        F64(a.c1).mul_portable(k).0,
        F64(a.c2).mul_portable(k).0,
    )
}

/// Through the norm, as [`F192::inv`].
pub const fn inv(a: F192) -> F192 {
    let m = mul(a.frobenius(), a.frobenius().frobenius());
    let norm = mul(a, m);
    mul_base(m, F64(norm.c0).inv_portable())
}
