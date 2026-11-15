// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! `K = F64 = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)` and
//! `E = F128 = K[y]/(y^2 + x*y + 1)`. Addresses, pc/fp, counters, and physical
//! committed columns are K-valued. A machine word is `c0 + c1*y ∈ E`
//! with `c0,c1 ∈ K`; challenges, sumcheck/GKR values, and transcript scalars
//! are E-valued.
//!
//! - [`F64`]: GF(2^64), polynomial x^64 + x^4 + x^3 + x + 1
//! - [`F128`]: `K[y]/(y^2 + x*y + 1)`
//! - [`F128Unreduced`]: its deferred-reduction accumulator, for full and mixed products alike

#[cfg(target_arch = "aarch64")]
pub mod neon;

pub mod f128x8;
pub mod gf2_64;
pub mod gf2_64x2;
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx2",
    target_feature = "vpclmulqdq",
    not(target_feature = "avx512f")
))]
pub mod x4;
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
pub mod x8;

pub use f128x8::{
    Acc8, F64x8, F128x8, Prod8, fold_lones8_ext, fold_pairs8_ext, msg_lone8_ext, msg_terms8_ext, mul_base_splat8,
    xor_into8,
};
pub use gf2_64::F64;
use gf2_64::R64;
pub use gf2_64x2::{F128, F128Unreduced, Weights8, dot_base, mul_unreduced4, mul2, mul4};

// ---------------------------------------------------------------------------
// leanVM g-power helpers: domain separators / opcodes as x^k, and the g-power
// index encoding (§sec:vm, §sec:e2e-bc).
// ---------------------------------------------------------------------------

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

/// `[g^0, g^1, …, g^{n-1}]`, built in parallel: each chunk seeds with one
/// [`g_pow`] (`O(log)`) and fills by `mul_by_g`, breaking the serial prefix
/// chain across cores.
pub fn g_powers(n: usize) -> Vec<F64> {
    const CHUNK: usize = 1 << 12;
    // SAFETY: the fill writes every element before it reads any.
    unsafe {
        crate::filled_vec(n, |v| {
            parallel::chunks_mut(v, CHUNK, |ci, chunk| {
                let mut acc = g_pow(ci * CHUNK);
                for slot in chunk.iter_mut() {
                    *slot = acc;
                    acc = mul_by_g(acc);
                }
            });
        })
    }
}

/// `g^i = x^i` in the monomial basis of `K` by square-and-multiply (`O(log i)`):
/// domain separators, opcodes, and the g-power encoding of index `i` (§sec:vm).
#[inline]
pub fn g_pow(i: usize) -> F64 {
    F64::G.pow(i as u128)
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
