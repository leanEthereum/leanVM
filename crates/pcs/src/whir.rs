// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! WHIR with `K = GF(2)[x]/(x^64+x^4+x^3+x+1)` and
//! `E = K[y]/(y^3+y+1)`.
//!
//! The committed message is a
//! vector of [`F64`] values; every verifier challenge, sumcheck message, basis
//! poly, and post-fold witness is [`F192`]-valued.
//!
//! Representations:
//! - committed message / L0 codeword / L0 opened rows: `F64` (8 bytes)
//! - challenges, sumcheck messages, folded witnesses, deeper-level codewords
//!   and opened rows, `b_initial`, betas, alphas, `yr`: `F192` (24 bytes)
//! - the RS-encoding evaluation domain and all LCH twiddles stay in K, so the
//!   deeper-level (E-valued) encodes use K-twiddles via the mixed product
//!   Plonky3's mixed `F192 * F64` product instead of a full E multiplication.
//!
//! Soundness note: the parameters ([`config_for_rate`]) come from an analysis of the actual
//! challenge field size `q = 2^192`; the committed alphabet remains `K = GF(2^64)`.
//!
//! The opening splits by concern:
//!
//! ```text
//!     commit    L0 base encode and the deeper levels' encodes, Merkle-committed
//!     sumcheck  round messages, fold kernels, the running claim
//!     prove     the recursive prover, level by level
//!     verify    the succinct verifier
//! ```

use primitives::PrimeCharacteristicRing;

mod commit;
pub mod config;
mod induce;
mod ntt_ext;
mod prove;
mod sumcheck;
#[cfg(test)]
mod tests;
mod verify;

use fiat_shamir::transcript::Challenger;
use primitives::multilinear::inner_product_base;
use primitives::{F64, F192};

pub use config::{
    INITIAL_FOLDING_FACTOR, L0_LIST_BITS, LOG_INV_RATE_0, MAX_LOG_INV_RATE, MAX_LOG_N, MIN_LOG_INV_RATE, MIN_LOG_N,
    ProverConfig, QUERY_GRINDING_BITS, RESIDUAL_MAX_LOG, RS_DOMAIN_INITIAL_REDUCTION_FACTOR, SECURITY_BITS,
    SUBSEQUENT_FOLDING_FACTOR, VerifierConfig, config_for_rate,
};

pub use commit::{Commitment, ProverData, commit};
pub use induce::eval_sk_at_vks;
pub use prove::recursive_prover_with_basis;
pub(crate) use prove::recursive_prover_with_prepared_basis;
pub(crate) use sumcheck::{INITIAL_BASIS_CHUNK, initial_rounds_virtual};
pub use verify::WhirError;
pub(crate) use verify::recursive_verifier_with_basis_succinct;

/// Mixed inner product `Σ_i b[i] · witness[i]` (E x K via `mul_base`). The
/// evaluation-claim `target` for a K-witness against an E-basis.
pub fn inner_product_base_ext(witness: &[F64], b: &[F192]) -> F192 {
    assert_eq!(witness.len(), b.len());
    const PAR_THRESHOLD: usize = 4096;
    if witness.len() < PAR_THRESHOLD {
        return inner_product_base(witness, b);
    }
    parallel::map_reduce(witness.len(), || F192::ZERO, |i| b[i] * witness[i], |a, v| a + v)
}

/// Where a query of a batch lands: the top `bits` bits of its position are `index`, the rest uniform.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Stratum {
    /// How many of the position's top bits are fixed.
    pub bits: usize,
    /// Their value.
    pub index: usize,
}

/// The strata of a batch of `count` queries into `2^depth` positions, in query order.
///
/// The batch is cut by the binary digits of `count`, highest first. A group of `2^g` queries fixes the top `s = min(g, depth)` bits of its `j`-th query's position to `j mod 2^s`, so each of the `2^s` cosets of those bits holds equally many of the group's queries.
/// A set of positions every query misses with probability at most `1 - delta` then is missed by the whole batch with probability at most `(1 - delta)^count`, as by i.i.d. queries (the PCS annex, `thm:rbr`), and the top `s` levels of the group's Merkle paths are a complete subtree the verifier hashes once.
pub fn strata(count: usize, depth: usize) -> Vec<Stratum> {
    let mut out = Vec::with_capacity(count);
    for g in (0..usize::BITS as usize).rev().filter(|&g| count >> g & 1 == 1) {
        let bits = g.min(depth);
        out.extend((0..1usize << g).map(|j| Stratum {
            bits,
            index: j & ((1 << bits) - 1),
        }));
    }
    out
}

/// Sample `count` query positions in transcript order: no dedup, no sort.
/// `block_len = 2^d`; each squeezed field element yields `⌊192/d⌋` uniform positions as
/// its disjoint d-bit chunks (low bits first) (fixed `192/d` per
/// squeeze), each then placed in its [`strata`] coset: its top bits replaced by its stratum's.
/// Duplicates are harmless, a repeated position re-opens the
/// same Merkle-authenticated row.
pub(crate) fn sample_queries_ordered(ch: &mut impl Challenger, block_len: usize, count: usize) -> Vec<usize> {
    let d = block_len.trailing_zeros() as usize;
    let per = 192 / d;
    let mut out = Vec::with_capacity(count);
    while out.len() < count {
        let v = ch.sample();
        for j in 0..per.min(count - out.len()) {
            let off = j * d;
            let limbs = [
                v.coefficients()[0].to_bits(),
                v.coefficients()[1].to_bits(),
                v.coefficients()[2].to_bits(),
            ];
            let (li, sh) = (off / 64, off % 64);
            let mut chunk = limbs[li] >> sh;
            if sh + d > 64 {
                chunk |= limbs[li + 1] << (64 - sh);
            }
            out.push(chunk as usize & (block_len - 1));
        }
    }
    for (x, s) in out.iter_mut().zip(strata(count, d)) {
        let low = d - s.bits;
        *x = (*x & ((1 << low) - 1)) | s.index << low;
    }
    out
}
