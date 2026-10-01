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
//!   [`F192::mul_base`] (3 PMULL) instead of a full E multiplication.
//!
//! Soundness note: [`WhirSecurityConfig`] analyzes the actual challenge
//! field size `q = 2^192`; the committed alphabet remains `K = GF(2^64)`.
//!
//! The opening splits by concern:
//!
//! ```text
//!     commit    L0 base encode and the deeper levels' encodes, Merkle-committed
//!     sumcheck  round messages, fold kernels, the running claim
//!     prove     the recursive prover, level by level
//!     verify    the succinct verifier
//! ```

mod commit;
mod prove;
mod sumcheck;
#[cfg(test)]
mod tests;
mod verify;

use fiat_shamir::transcript::Challenger;
use primitives::field::{F64, F192};

#[cfg(test)]
pub use super::whir_config::default_config;
pub use super::whir_config::{
    ConfigError, FinalBlockConfig, INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0, MAX_LOG_INV_RATE, MIN_LOG_INV_RATE,
    ProverConfig, QUERY_GRINDING_BITS, RESIDUAL_MAX_LOG, RS_DOMAIN_INITIAL_REDUCTION_FACTOR, SECURITY_BITS,
    SUBSEQUENT_FOLDING_FACTOR, VerifierConfig, WhirLevelConfig, WhirSecurityConfig, validate_log_inv_rate,
};

pub use crate::whir_induce::*;
pub use commit::{Commitment, ProverData, commit};
pub use prove::recursive_prover_with_basis;
pub(crate) use prove::recursive_prover_with_prepared_basis;
#[cfg(test)]
pub(crate) use sumcheck::build_initial_basis;
pub(crate) use sumcheck::{Basis, INITIAL_BASIS_CHUNK, initial_message};
pub use verify::{VerifyError, recursive_verifier_with_basis_succinct};

/// Mixed inner product `Σ_i b[i] · witness[i]` (E x K via `mul_base`). The
/// evaluation-claim `target` for a K-witness against an E-basis.
pub fn inner_product_base_ext(witness: &[F64], b: &[F192]) -> F192 {
    assert_eq!(witness.len(), b.len());
    const PAR_THRESHOLD: usize = 4096;
    if witness.len() < PAR_THRESHOLD {
        return witness
            .iter()
            .zip(b.iter())
            .map(|(&w, &e)| e.mul_base(w))
            .fold(F192::ZERO, |a, v| a + v);
    }
    parallel::map_reduce(
        witness.len(),
        || F192::ZERO,
        |i| b[i].mul_base(witness[i]),
        |a, v| a + v,
    )
}

// ===================================================================
// Config reuse
// ===================================================================

/// Derive the shared prover/verifier config for a K-witness of `2^log_n` F64
/// elements at L0 inverse-rate logarithm `log_inv_rate`, using the production
/// 128-bit Johnson/OOD profile at `m = log_n + LOG_PACKING`.
pub fn config_for_rate(log_n: usize, log_inv_rate: usize) -> Result<ProverConfig, ConfigError> {
    let sec = WhirSecurityConfig::derive_config_with_log_inv_rate(log_n + crate::LOG_PACKING, log_inv_rate)?;
    sec.to_config()
}

/// Sample `count` query positions in transcript order: no dedup, no sort.
/// `block_len = 2^d`; each squeezed field element yields `⌊192/d⌋` positions as
/// its disjoint d-bit chunks (low bits first) (fixed `192/d` per
/// squeeze, dup-tolerant: soundness matches the deployed PCS with the same
/// `config.queries`). Duplicates are harmless, a repeated position re-opens the
/// same Merkle-authenticated row.
///
fn sample_queries_ordered(ch: &mut impl Challenger, block_len: usize, count: usize) -> Vec<usize> {
    let d = block_len.trailing_zeros() as usize;
    let per = 192 / d;
    let mut out = Vec::with_capacity(count);
    while out.len() < count {
        let v = ch.sample();
        for j in 0..per.min(count - out.len()) {
            let off = j * d;
            let limbs = [v.c0, v.c1, v.c2];
            let (li, sh) = (off / 64, off % 64);
            let mut chunk = limbs[li] >> sh;
            if sh + d > 64 {
                chunk |= limbs[li + 1] << (64 - sh);
            }
            out.push(chunk as usize & (block_len - 1));
        }
    }
    out
}
