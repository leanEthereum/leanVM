// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! [`F64`] is `K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)` and [`F128`] is `E = K[y]/(y^2 + x*y + 1)`. Addresses,
//! pc/fp, counters, and physical committed columns are K-valued. A machine word is `c0 + c1*y ∈ E` with
//! `c0,c1 ∈ K`; challenges, sumcheck/GKR values, and transcript scalars are E-valued.
//!
//! - [`F128Unreduced`]: its deferred-reduction accumulator, for full and mixed products alike
//! - [`lanes`]: eight elements at a time, the one SIMD layer

pub mod gf2_64;
pub mod gf2_64x2;
pub mod lanes;

pub use gf2_64::F64;
use gf2_64::R64;
pub use gf2_64x2::{F128, F128Unreduced};
pub use lanes::{Acc8, F64x8, F128x8, clmul8_low};

/// Multiply by `x = g` in `K`: a shift, and a fold of bit 64 by `x^64 = x^4 + x^3 + x + 1`. `const` for tables of
/// `g^k` built at compile time.
#[inline]
pub const fn mul_by_g(a: F64) -> F64 {
    let carry = a.0 >> 63;
    F64((a.0 << 1) ^ (R64 * carry))
}

/// Divide by `x = g` in `K`, the inverse of the product by `g`.
///
/// Bit 0 of the input says whether that product folded: if so, unfold it and set bit 63.
#[inline(always)]
pub const fn div_by_g(a: F64) -> F64 {
    F64(if a.0 & 1 == 1 {
        (a.0 ^ R64) >> 1 | 1 << 63
    } else {
        a.0 >> 1
    })
}

/// `[x^0, x^1, …, x^{n-1}]`: the weights of a random linear combination batched with the powers of one challenge.
pub fn powers(x: F128, n: usize) -> Vec<F128> {
    let mut out = Vec::with_capacity(n);
    let mut p = F128::ONE;
    for _ in 0..n {
        out.push(p);
        p *= x;
    }
    out
}

/// `[g^0, g^1, …, g^{n-1}]`, built in parallel by [`isa::g_pow`].
pub fn g_powers(n: usize) -> Vec<F64> {
    assert!(n <= 1 << 32, "a g-power index fits in 32 bits");
    parallel::map_collect(n, |i| F64(isa::g_pow(i as u32)))
}

/// `g^i = x^i` in the monomial basis of `K` by square-and-multiply: domain separators, opcodes, and the g-power
/// encoding of index `i` (§sec:vm).
#[inline]
pub fn g_pow(i: usize) -> F64 {
    F64::G.pow(i as u128)
}

/// `sum_i a[i] b[i]` over `E`, reduced once; zero if either is empty.
pub fn dot(a: &[F128], b: &[F128]) -> F128 {
    if a.is_empty() || b.is_empty() {
        return F128::ZERO;
    }
    assert_eq!(a.len(), b.len());
    let ((a8, a1), (b8, b1)) = (a.as_chunks::<8>(), b.as_chunks::<8>());
    let acc = a8.iter().zip(b8).fold(Acc8::ZERO, |acc, (a, b)| {
        acc + F128x8::from_array(a).mul_unreduced(F128x8::from_array(b))
    });
    a1.iter().zip(b1).fold(acc.sum(), |sum, (&a, &b)| sum + a * b)
}

/// MLE of the index column `[g^0, …, g^{2^n−1}]` over the `n`-variable cube, evaluated at an `E`-point:
/// `∏_k (1 + ζ_k·(1 + g^{2^k}))` (§sec:idxcol), one mixed product per term.
pub fn index_mle(zeta: &[F128]) -> F128 {
    let mut acc = F128::ONE;
    let mut g2k = F64::G; // g^{2^0} = g
    for &z in zeta {
        acc *= F128::ONE + z.mul_base(F64::ONE + g2k);
        g2k = g2k * g2k;
    }
    acc
}
