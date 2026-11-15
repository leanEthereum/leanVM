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

/// Multiply by `x = g` in `K`: a shift, and a fold of bit 64 by `x^64 = x^4 + x^3 + x + 1`.
/// `const` so table constants (`g^k` separators, opcodes) evaluate at compile time.
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

/// `[x^0, x^1, …, x^{n-1}]`: the weights of a random linear combination batched
/// with the powers of one challenge, rather than `n` independent ones.
pub fn powers(x: F128, n: usize) -> Vec<F128> {
    let mut out = Vec::with_capacity(n);
    let mut p = F128::ONE;
    for _ in 0..n {
        out.push(p);
        p *= x;
    }
    out
}

/// `[g^0, g^1, …, g^{n-1}]`, built in parallel by [`g_pow32_by_lookup`].
pub fn g_powers(n: usize) -> Vec<F64> {
    assert!(n <= 1 << 32, "a g-power index fits in 32 bits");
    parallel::map_collect(n, |i| g_pow32_by_lookup(i as u32))
}

/// `g^i = x^i` in the monomial basis of `K` by square-and-multiply (`O(log i)`):
/// domain separators, opcodes, and the g-power encoding of index `i` (§sec:vm).
#[inline]
pub fn g_pow(i: usize) -> F64 {
    F64::G.pow(i as u128)
}

/// `g^i` for a `u32` exponent, from two `2^16`-entry tables built once: `i` splits as
/// `hi·2^16 + lo`, so a small exponent is one load and any other one more load and a
/// product. Unlike a table grown to the exponent, the cost says nothing about `i`, which
/// is what keeps an operand's magnitude out of the work its program costs.
pub fn g_pow32_by_lookup(i: u32) -> F64 {
    const LOG_SPLIT: u32 = 16;
    const SPAN: usize = 1 << LOG_SPLIT;
    static TABLES: std::sync::OnceLock<[Vec<F64>; 2]> = std::sync::OnceLock::new();
    let [baby, giant] = TABLES.get_or_init(|| {
        let mut baby = Vec::with_capacity(SPAN);
        let mut acc = F64::ONE;
        for _ in 0..SPAN {
            baby.push(acc);
            acc = mul_by_g(acc);
        }
        // `acc` is `g^{2^16}` now, one past the baby table: the step between giant entries.
        let (step, mut giant) = (acc, Vec::with_capacity(SPAN));
        acc = F64::ONE;
        for _ in 0..SPAN {
            giant.push(acc);
            acc *= step;
        }
        [baby, giant]
    });
    match i >> LOG_SPLIT {
        0 => baby[i as usize],
        hi => baby[i as usize & (SPAN - 1)] * giant[hi as usize],
    }
}

/// MLE of the index column `[g^0, …, g^{2^n−1}]` over the `n`-variable cube,
/// evaluated at an `E`-point: `∏_k (1 + ζ_k·(1 + g^{2^k}))` in `O(n)` (§sec:idxcol).
/// The `g^{2^k}` factors are `K`-constants, so each term is one mixed product.
pub fn index_mle(zeta: &[F128]) -> F128 {
    let mut acc = F128::ONE;
    let mut g2k = F64::G; // g^{2^0} = g
    for &z in zeta {
        acc *= F128::ONE + z.mul_base(F64::ONE + g2k);
        g2k = g2k * g2k;
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The split table against the square-and-multiply it replaces, at both sides of the
    /// `2^16` boundary and at the ends of the operand range.
    #[test]
    fn g_pow32_matches_square_and_multiply() {
        const SPLIT: u32 = 1 << 16;
        for i in [
            0,
            1,
            63,
            64,
            SPLIT - 1,
            SPLIT,
            SPLIT + 1,
            1 << 28,
            u32::MAX - 1,
            u32::MAX,
        ] {
            assert_eq!(g_pow32_by_lookup(i), g_pow(i as usize), "g^{i}");
        }
    }
}
