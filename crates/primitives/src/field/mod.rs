// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! `K = F64 = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)` and
//! `E = F192 = K[y]/(y^3 + y + 1)`. Addresses, pc/fp, counters, and physical
//! committed columns are K-valued. A machine word is `c0 + c1*y + c2*y² ∈ E`
//! with `c0,c1,c2 ∈ K`; challenges, sumcheck/GKR values, and transcript scalars
//! are E-valued.
//!
//! - [`F64`]: GF(2^64), polynomial x^64 + x^4 + x^3 + x + 1
//! - [`F8`]: GF(2^8) with AES polynomial x^8 + x^4 + x^3 + x + 1
//! - [`F192`]: `K[y]/(y^3 + y + 1)`
//! - [`F192Unreduced`]: its deferred-reduction accumulator, for full and mixed products alike

#[cfg(target_arch = "aarch64")]
pub mod neon;

pub mod gf2_64;
pub mod gf2_64x3;
pub mod gf2_8;
pub mod phi8_tower;

pub use gf2_8::F8;
pub use gf2_64::F64;
pub use gf2_64x3::{F192, F192Unreduced, Weights8, dot_base, mul_base8, mul_unreduced4, mul2, mul4};
pub use phi8_tower::{PHI_8_TABLE_192, phi8_192};

// ---------------------------------------------------------------------------
// leanVM g-power helpers: domain separators / opcodes as x^k, and the g-power
// index encoding (§sec:vm, §sec:e2e-bc).
// ---------------------------------------------------------------------------

/// Multiply by `x = g` in `K`, where `x^64 = x^4 + x^3 + x + 1` and
/// `0x1B = x^4 + x^3 + x + 1`.
/// `const` so table constants (`g^k` separators, opcodes) evaluate at compile time.
#[inline]
pub const fn mul_by_g(a: F64) -> F64 {
    let carry = a.0 >> 63;
    F64((a.0 << 1) ^ (0x1B * carry))
}

/// `[x^0, x^1, …, x^{n-1}]`: the weights of a random linear combination batched
/// with the powers of one challenge, rather than `n` independent ones.
pub fn powers(x: F192, n: usize) -> Vec<F192> {
    let mut out = Vec::with_capacity(n);
    let mut p = F192::ONE;
    for _ in 0..n {
        out.push(p);
        p *= x;
    }
    out
}

/// `g^i = x^i` in the monomial basis of `K` by square-and-multiply (`O(log i)`):
/// domain separators, opcodes, and the g-power encoding of index `i` (§sec:vm).
#[inline]
pub fn g_pow(i: usize) -> F64 {
    let mut result = F64::ONE;
    let mut base = G; // x = g
    let mut e = i;
    while e > 0 {
        if e & 1 == 1 {
            result *= base;
        }
        base = base * base;
        e >>= 1;
    }
    result
}

/// The fixed generator `g = x ∈ K`, with `ord(g) = 2^64 - 1` (pinned by a
/// field test), larger than every index any admissible
/// instance uses (the verifier's instance caps, §cpu). For `k < 64`, `g^k` is
/// the monomial `x^k` (bit `k`).
pub const G: F64 = F64::G;

/// MLE of the integer column `[base ^ (z << shift)]_z`, entry `z` being the element
/// whose bits are that integer's: `base + Σ_k ζ_k·x^{k+shift}`, linear, since bit `k`
/// contributes the monomial `x^k` (§sec:idxcol). What addresses the registers, RAM
/// and the bytecode: with `base` a multiple of the region's size, the XOR is the sum.
pub fn int_index_mle(base: F64, shift: u32, zeta: &[F192]) -> F192 {
    zeta.iter().enumerate().fold(F192::from(base), |acc, (k, z)| {
        acc + z.mul_base(F64(1 << (k as u32 + shift)))
    })
}
