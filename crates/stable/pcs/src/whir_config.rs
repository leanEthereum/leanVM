// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// CREDIT: https://github.com/bcc-research/bolt-rs, MIT.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The shape of the affine-combiner WHIR opening: its level ladder, its query counts and its grinds.
//!
//! The query counts and grinds come from the round-by-round soundness analysis, which `crates/verifier` tabulates
//! (`verifier::whir_queries`) rather than repeats. This prover reads the same table, so it opens exactly the shapes the
//! verifier accepts: a stack of `2^log_n` words with `log_n` in `MIN_STACKED_LOG..=MAX_STACKED_LOG`, at every rate.

pub use verifier::{
    BATCH_GRINDING_BITS, FOLD_GRINDING_BITS, MAX_STACKED_CLAIMS, OOD_GRINDING_BITS, QUERY_GRINDING_BITS,
};

/// Round-by-round soundness target (bits): every verifier message's error, after its grind, is at most
/// `2^-SECURITY_BITS` (`fiat_shamir::SECURITY_BITS`).
pub const SECURITY_BITS: usize = fiat_shamir::SECURITY_BITS as usize;

/// L0 code rate index: `rho_0 = 2^-LOG_INV_RATE_0` (rate 1/2).
pub const LOG_INV_RATE_0: usize = 1;

/// The smallest `log_inv_rate` a proof can use, its code rate being `2^-log_inv_rate`.
pub const MIN_LOG_INV_RATE: usize = 1;
/// The largest `log_inv_rate` a proof can use, its code rate being `2^-log_inv_rate`.
pub const MAX_LOG_INV_RATE: usize = 4;

/// Validate a production WHIR inverse-rate logarithm.
pub fn validate_log_inv_rate(log_inv_rate: usize) -> Result<(), String> {
    if !(MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE).contains(&log_inv_rate) {
        return Err(format!(
            "log_inv_rate must be in {MIN_LOG_INV_RATE}..={MAX_LOG_INV_RATE}, got {log_inv_rate}"
        ));
    }
    Ok(())
}

pub const INITIAL_FOLDING_FACTOR: usize = 6;
const SUBSEQUENT_FOLDING_FACTOR: usize = 4;

/// The RS domain loses this many bits after the initial fold, and one bit after each later fold, so a fold of `k`
/// variables raises the inverse-rate logarithm by `k` less that.
const RS_DOMAIN_INITIAL_REDUCTION_FACTOR: usize = 3;
const RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR: usize = 1;

/// Folding stops once at most this many variables remain: the final level is sent in clear instead of committed and
/// folded further.
const RESIDUAL_MAX_LOG: usize = 5;

// The recursion guest rotates the terminal point left by the lane fold to index it by witness coordinate, and the
// residual segment is what the last lane challenges rotate past, so the residual may never be longer than that fold.
const _: () = assert!(RESIDUAL_MAX_LOG <= INITIAL_FOLDING_FACTOR);

/// Shape plus per-level query counts for one WHIR opening. Prover and verifier read exactly the same numbers.
#[derive(Clone, Debug)]
pub struct ProverConfig {
    pub log_inv_rates: Vec<usize>,
    pub level_steps: usize,
    pub initial_k: usize,
    pub(crate) level_ks: Vec<usize>,
    /// Per-level query counts (L0, L1, ..., L_r). Length = level_steps + 1.
    pub queries: Vec<usize>,
}

/// The per-level shape table a [`ProverConfig`] implies for a
/// `log_n`-variable opening: the numbers every consumer of the multilevel
/// protocol (the prover, recursion harnesses) otherwise re-derives.
#[derive(Clone, Debug)]
pub struct LevelShapes {
    /// Level count (`level_steps + 1`).
    pub levels: usize,
    /// Fold count per level: `initial_k` then `level_ks`.
    pub ks: Vec<usize>,
    /// Log message columns after each level's fold (`log_n - initial_k`,
    /// then descending by each level's `k`).
    pub log_msg_cols: Vec<usize>,
    /// Committed block length per level (`msg_cols * inv_rate`).
    pub block_len: Vec<usize>,
    /// The residual cube dimension left after every fold.
    pub yr_log_n: usize,
}

impl ProverConfig {
    /// See [`LevelShapes`].
    pub fn level_shapes(&self, log_n: usize) -> LevelShapes {
        let r = self.level_steps;
        let ks: Vec<usize> = std::iter::once(self.initial_k)
            .chain(self.level_ks.iter().copied())
            .collect();
        let mut log_msg_cols = vec![log_n - self.initial_k];
        for i in 0..r {
            log_msg_cols.push(log_msg_cols[i] - self.level_ks[i]);
        }
        let block_len: Vec<usize> = (0..=r)
            .map(|i| 1usize << (log_msg_cols[i] + self.log_inv_rates[i]))
            .collect();
        LevelShapes {
            levels: r + 1,
            ks,
            yr_log_n: *log_msg_cols.last().unwrap(),
            log_msg_cols,
            block_len,
        }
    }
}

/// The configuration for a `2^log_n`-word stack at L0 rate `2^-log_inv_rate`: the ladder folds
/// [`INITIAL_FOLDING_FACTOR`], then `SUBSEQUENT_FOLDING_FACTOR` variables a level until at most
/// `RESIDUAL_MAX_LOG` remain, and every level takes the verifier's tabulated query count.
pub fn config_for_rate(log_n: usize, log_inv_rate: usize) -> Result<ProverConfig, String> {
    validate_log_inv_rate(log_inv_rate)?;
    let queries = verifier::whir_queries(log_n, log_inv_rate)
        .ok_or_else(|| format!("no WHIR configuration at log_n = {log_n}, rate {log_inv_rate}"))?;
    let mut log_inv_rates = vec![log_inv_rate];
    let mut level_ks = Vec::new();
    let (mut remaining, mut fold) = (log_n - INITIAL_FOLDING_FACTOR, INITIAL_FOLDING_FACTOR);
    while remaining > RESIDUAL_MAX_LOG {
        let reduction = if level_ks.is_empty() {
            RS_DOMAIN_INITIAL_REDUCTION_FACTOR
        } else {
            RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR
        };
        log_inv_rates.push(log_inv_rates[log_inv_rates.len() - 1] + fold - reduction);
        fold = SUBSEQUENT_FOLDING_FACTOR.min(remaining);
        remaining -= fold;
        level_ks.push(fold);
    }
    assert_eq!(queries.len(), level_ks.len() + 1, "one query count per level");
    Ok(ProverConfig {
        log_inv_rates,
        level_steps: level_ks.len(),
        initial_k: INITIAL_FOLDING_FACTOR,
        level_ks,
        queries: queries.to_vec(),
    })
}
