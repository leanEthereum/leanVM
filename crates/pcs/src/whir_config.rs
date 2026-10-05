// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// CREDIT: https://github.com/bcc-research/bolt-rs, MIT.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Ported from bolt-rs (https://github.com/bcc-research/bolt-rs,
// `whir_recursive.rs`).

//! The WHIR configuration: the protocol's constants, and the per-level parameters of each opening.
//!
//! [`config_for_rate`] builds those parameters from integers alone: the level ladder, and the query counts `WHIR_QUERIES` tabulates, so neither the prover nor a verifier computes in floating point.
//! The table is what the floating-point soundness analysis (the PCS annex, Theorem `thm:rbr`) derives at every size and rate it covers.
//! That analysis lives in the test-only `tests` module, and its test `the_table_is_the_derivation` checks every entry, so changing a constant it reads fails that test until the table is regenerated (AGENTS.md, "One protocol, three verifiers").

use fiat_shamir::MAX_GRINDING_BITS;
use thiserror::Error;

// ===================================================================
// Config
// ===================================================================

// The production WHIR configuration: Johnson list decoding at rates 2^-1 to 2^-4 and 128-bit round-by-round soundness over F192.
// L0 takes no OOD sample, so the commitment binds only to a list, whose size every challenge before the opening pays; every later level takes one OOD sample.

/// Round-by-round soundness target (bits): every verifier-challenge transition
/// must have conditional failure probability at most `2^-SECURITY_BITS`.
pub const SECURITY_BITS: usize = 128;

/// Bits a challenge drawn after the commitment loses to the commitment's list.
///
/// Level 0 takes no out-of-domain sample.
/// So the root binds the prover to a list of up to `L_0 = 1/(2 eta_0 sqrt(rho_0))` polynomials (Johnson bound).
///
/// A challenge drawn between the root and the opening must hold against every list member.
/// By a union bound its error grows by a factor `L_0`.
///
/// The value is `ceil(log2 L_0)` at its largest over every configured size and rate.
/// A test pins it to the derivation.
pub const L0_LIST_BITS: usize = 12;

/// L0 code rate index: `rho_0 = 2^-LOG_INV_RATE_0` (rate 1/2).
pub const LOG_INV_RATE_0: usize = 1;

/// CLI-selectable L0 rates are `2^-r` for `r = 1, 2, 3, 4`.
pub const MIN_LOG_INV_RATE: usize = 1;
pub const MAX_LOG_INV_RATE: usize = 4;

/// Why [`config_for_rate`] has no configuration for a witness size and a rate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum ConfigError {
    /// An L0 rate outside the supported range.
    #[error("log_inv_rate {log_inv_rate} is not in {MIN_LOG_INV_RATE}..={MAX_LOG_INV_RATE}")]
    RateOutOfRange { log_inv_rate: usize },
    /// A witness size outside the tabulated range.
    #[error("log_n {log_n} is not in {MIN_LOG_N}..={MAX_LOG_N}")]
    SizeOutOfRange { log_n: usize },
}

/// Why the level ladder has no shape for a witness size. No size [`config_for_rate`] accepts gets here; the test-only derivation and its fallback ladder, which take any size, can.
///
/// `level` counts from L0, the commitment's own code.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub(crate) enum LadderError {
    /// No variable is left after the initial fold.
    #[error("log_n {log_n} does not exceed the initial fold {initial_k}")]
    TooFewVariables { log_n: usize, initial_k: usize },
    /// The witness is too small for two fold levels.
    #[error("log_n {log_n} gives fewer than two fold levels")]
    TooFewLevels { log_n: usize },
    /// A fold smaller than the RS domain reduction it pays for.
    #[error("level {level} folds {fold} variables, below the RS domain reduction {reduction}")]
    FoldBelowReduction {
        level: usize,
        fold: usize,
        reduction: usize,
    },
}

/// Validate a production WHIR inverse-rate logarithm.
pub fn validate_log_inv_rate(log_inv_rate: usize) -> Result<(), ConfigError> {
    if !(MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE).contains(&log_inv_rate) {
        return Err(ConfigError::RateOutOfRange { log_inv_rate });
    }
    Ok(())
}

/// Per-level query-phase proof-of-work budget. These bits are ground after the
/// level commitment and before its query positions are sampled, so the query
/// count only needs to close the remaining `SECURITY_BITS - 17` bits.
pub const QUERY_GRINDING_BITS: usize = 17;

const _: () = assert!(QUERY_GRINDING_BITS <= MAX_GRINDING_BITS as usize);

pub const INITIAL_FOLDING_FACTOR: usize = 6;
pub const SUBSEQUENT_FOLDING_FACTOR: usize = 4;

/// Logarithmic reduction of the total Reed--Solomon domain after the initial
/// fold. With the production six-variable initial fold, `3` changes the
/// inverse-rate logarithm by `6 - 3 = 3` at the first recursive level.
pub const RS_DOMAIN_INITIAL_REDUCTION_FACTOR: usize = 3;

/// After each subsequent fold, shrink the total Reed--Solomon domain by one
/// bit. This mirrors WHIR's recursive-domain schedule; unlike the initial
/// reduction, it is deliberately fixed rather than a tuning parameter.
pub const RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR: usize = 1;

const _: () = assert!(RS_DOMAIN_INITIAL_REDUCTION_FACTOR <= INITIAL_FOLDING_FACTOR);
const _: () = assert!(RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR <= SUBSEQUENT_FOLDING_FACTOR);

/// Folding stops once at most this many variables remain: the residual
/// polynomial (`yr`, at most `2^RESIDUAL_MAX_LOG` coefficients) is sent in
/// clear instead of committed and folded further.
pub const RESIDUAL_MAX_LOG: usize = 5;

// A verifier rotates the terminal point left by the lane fold to index it by
// witness coordinate, and the residual segment is what the last lane challenges
// rotate past, so the residual may never be longer than that fold.
const _: () = assert!(RESIDUAL_MAX_LOG <= INITIAL_FOLDING_FACTOR);

/// Shape plus per-level soundness parameters for one WHIR opening. Prover
/// and verifier read exactly the same numbers, hence the single struct and the
/// [`VerifierConfig`] alias.
///
/// Built only in this crate, from the table (or, in tests, by the soundness derivation and the test-support ladder), and checked once there.
/// The prover and the verifier index the per-level vectors without checking them again.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProverConfig {
    initial_k: usize,
    level_ks: Vec<usize>,
    log_inv_rates: Vec<usize>,
    queries: Vec<usize>,
    grinding_bits: Vec<usize>,
    ood_samples: Vec<usize>,
}

pub type VerifierConfig = ProverConfig;

impl ProverConfig {
    /// A config of `level_ks.len()` recursive levels after the lane fold.
    ///
    /// # Panics
    ///
    /// Panics unless there is a lane fold and at least one recursive level, every per-level vector covers L0 to the last level, and L0 takes no OOD sample.
    fn new(
        initial_k: usize,
        level_ks: Vec<usize>,
        log_inv_rates: Vec<usize>,
        queries: Vec<usize>,
        grinding_bits: Vec<usize>,
        ood_samples: Vec<usize>,
    ) -> Self {
        let levels = level_ks.len() + 1;
        assert!(initial_k >= 1, "the lane fold binds at least one variable");
        assert!(levels >= 2, "at least one recursive level");
        assert_eq!(log_inv_rates.len(), levels);
        assert_eq!(queries.len(), levels);
        assert_eq!(grinding_bits.len(), levels);
        assert_eq!(ood_samples.len(), levels);
        // The lane rounds fold the truncated witness against a weight over the whole
        // `2^log_n` cube. Every claim weight vanishes on the absent lanes, but an OOD
        // weight `eq(z, .)` is a full tensor that does not, so L0 can take none.
        assert_eq!(ood_samples[0], 0, "L0 takes no OOD sample");
        assert!(
            grinding_bits.iter().all(|&g| g <= MAX_GRINDING_BITS as usize),
            "a proof of work grinds at most the digest's low word"
        );
        Self {
            initial_k,
            level_ks,
            log_inv_rates,
            queries,
            grinding_bits,
            ood_samples,
        }
    }

    /// Variables the L0 lane fold binds, which is also the log of the L0 interleaving.
    pub const fn initial_k(&self) -> usize {
        self.initial_k
    }

    /// Recursive levels after L0, at least one.
    pub const fn level_steps(&self) -> usize {
        self.level_ks.len()
    }

    /// Variables each recursive level folds (L1, ..., L_r).
    pub fn level_ks(&self) -> &[usize] {
        &self.level_ks
    }

    /// Per-level inverse-rate logarithms (L0, L1, ..., L_r).
    pub fn log_inv_rates(&self) -> &[usize] {
        &self.log_inv_rates
    }

    /// Per-level query counts (L0, L1, ..., L_r), from the per-level soundness analysis.
    pub fn queries(&self) -> &[usize] {
        &self.queries
    }

    /// Per-level query-phase grinding bits (L0, L1, ..., L_r).
    ///
    /// Each level grinds after its commitment and before its query positions are sampled.
    pub fn grinding_bits(&self) -> &[usize] {
        &self.grinding_bits
    }

    /// Per-level out-of-domain samples (L0, L1, ..., L_r), taken right after the level's root enters the transcript.
    ///
    /// L0 takes none: the commitment binds only to a list, which every challenge before the opening pays for.
    pub fn ood_samples(&self) -> &[usize] {
        &self.ood_samples
    }
}

/// Level-ladder shape: the per-level inverse-rate logarithms and folds, index 0 being L0.
struct LadderShape {
    log_inv_rates: Vec<usize>,
    k_levels: Vec<usize>,
}

/// Descend the level ladder, folding [`SUBSEQUENT_FOLDING_FACTOR`] variables per
/// level until at most [`RESIDUAL_MAX_LOG`] remain. `next_rate` picks each new
/// level's inverse-rate logarithm from `(new level, previous rate, fold just taken,
/// message dimension the new level carries)`, which is the only thing that separates the
/// production ladder from the test-support one.
fn derive_ladder<E: From<LadderError>>(
    log_n: usize,
    initial_k: usize,
    log_inv_rate: usize,
    mut next_rate: impl FnMut(usize, usize, usize, usize) -> Result<usize, E>,
) -> Result<LadderShape, E> {
    if log_n <= initial_k {
        return Err(LadderError::TooFewVariables { log_n, initial_k }.into());
    }
    let mut shape = LadderShape {
        log_inv_rates: vec![log_inv_rate],
        k_levels: vec![initial_k],
    };
    let mut n_running = log_n - initial_k;
    let mut rate_running = log_inv_rate;
    let mut fold_running = initial_k;
    while n_running > RESIDUAL_MAX_LOG {
        let k = SUBSEQUENT_FOLDING_FACTOR.min(n_running);
        let log_msg_cols_next = n_running - k;
        let rate = next_rate(shape.k_levels.len(), rate_running, fold_running, log_msg_cols_next)?;
        shape.log_inv_rates.push(rate);
        shape.k_levels.push(k);
        n_running -= k;
        rate_running = rate;
        fold_running = k;
    }
    if shape.k_levels.len() < 2 {
        return Err(LadderError::TooFewLevels { log_n }.into());
    }
    Ok(shape)
}

/// Production ladder: the total RS domain loses
/// [`RS_DOMAIN_INITIAL_REDUCTION_FACTOR`] bits after the initial fold, then
/// exactly one bit per subsequent fold, so a fold of `k` variables raises the
/// inverse-rate logarithm by `k - reduction`.
fn derive_ladder_shape(log_n: usize, initial_k: usize, log_inv_rate: usize) -> Result<LadderShape, LadderError> {
    let mut domain_reduction = RS_DOMAIN_INITIAL_REDUCTION_FACTOR;
    derive_ladder(
        log_n,
        initial_k,
        log_inv_rate,
        |level, rate_running, fold_running, _cols| {
            let rate_increase = fold_running
                .checked_sub(domain_reduction)
                .ok_or(LadderError::FoldBelowReduction {
                    level,
                    fold: fold_running,
                    reduction: domain_reduction,
                })?;
            domain_reduction = RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR;
            Ok(rate_running + rate_increase)
        },
    )
}

/// Smallest committed witness, `2^MIN_LOG_N` words, that [`config_for_rate`] configures: the production ladder's floor, with one level of margin.
pub const MIN_LOG_N: usize = 15;
/// Largest committed witness, `2^MAX_LOG_N` words, that [`config_for_rate`] configures.
pub const MAX_LOG_N: usize = 28;

/// Per-level query counts (L0, L1, ...) of the production opening, at `[log_inv_rate - MIN_LOG_INV_RATE][log_n - MIN_LOG_N]`: what the soundness derivation chooses, pinned to it by `the_table_is_the_derivation`.
const WHIR_QUERIES: [[&[usize]; MAX_LOG_N - MIN_LOG_N + 1]; MAX_LOG_INV_RATE - MIN_LOG_INV_RATE + 1] = [
    // Rate 2^-1.
    [
        &[222, 55],
        &[223, 56, 30],
        &[223, 56, 31],
        &[223, 56, 32],
        &[223, 56, 32],
        &[223, 56, 32, 22],
        &[223, 56, 32, 22],
        &[224, 56, 32, 23],
        &[224, 56, 32, 23],
        &[224, 56, 32, 23, 17],
        &[224, 56, 32, 23, 17],
        &[224, 56, 32, 23, 18],
        &[225, 56, 32, 23, 18],
        &[225, 56, 32, 23, 18, 14],
    ],
    // Rate 2^-2.
    [
        &[111, 45],
        &[112, 45, 27],
        &[112, 45, 28],
        &[112, 45, 28],
        &[112, 45, 28],
        &[112, 45, 28, 20],
        &[112, 45, 28, 20],
        &[112, 45, 28, 21],
        &[112, 45, 28, 21],
        &[112, 45, 28, 21, 16],
        &[112, 45, 28, 21, 16],
        &[112, 45, 28, 21, 16],
        &[112, 45, 28, 21, 16],
        &[112, 45, 28, 21, 16, 13],
    ],
    // Rate 2^-3.
    [
        &[75, 37],
        &[75, 37, 24],
        &[75, 37, 25],
        &[75, 38, 25],
        &[75, 38, 25],
        &[75, 38, 25, 18],
        &[75, 38, 25, 19],
        &[75, 38, 25, 19],
        &[75, 38, 25, 19],
        &[75, 38, 25, 19, 15],
        &[75, 38, 25, 19, 15],
        &[75, 38, 25, 19, 15],
        &[75, 38, 25, 19, 15],
        &[75, 38, 25, 19, 15, 13],
    ],
    // Rate 2^-4.
    [
        &[56, 32],
        &[56, 32, 22],
        &[56, 32, 22],
        &[56, 32, 23],
        &[56, 32, 23],
        &[56, 32, 23, 17],
        &[56, 32, 23, 17],
        &[56, 32, 23, 18],
        &[56, 32, 23, 18],
        &[56, 32, 23, 18, 14],
        &[56, 32, 23, 18, 14],
        &[56, 32, 23, 18, 14],
        &[56, 32, 23, 18, 15],
        &[56, 32, 23, 18, 15, 12],
    ],
];

/// The shared prover/verifier config for a `K`-witness of `2^log_n` F64 words at L0 inverse-rate logarithm `log_inv_rate`.
///
/// The production 128-bit Johnson/OOD profile: the ladder, then the tabulated query counts, [`QUERY_GRINDING_BITS`] at every level, and one OOD sample at every level past L0.
///
/// # Errors
///
/// A rate outside `MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE`, or a size outside `MIN_LOG_N..=MAX_LOG_N`.
pub fn config_for_rate(log_n: usize, log_inv_rate: usize) -> Result<ProverConfig, ConfigError> {
    validate_log_inv_rate(log_inv_rate)?;
    if !(MIN_LOG_N..=MAX_LOG_N).contains(&log_n) {
        return Err(ConfigError::SizeOutOfRange { log_n });
    }
    let shape = derive_ladder_shape(log_n, INITIAL_FOLDING_FACTOR, log_inv_rate)
        .expect("the tabulated window always has a ladder");
    let levels = shape.k_levels.len();
    let queries = WHIR_QUERIES[log_inv_rate - MIN_LOG_INV_RATE][log_n - MIN_LOG_N];
    Ok(ProverConfig::new(
        INITIAL_FOLDING_FACTOR,
        shape.k_levels[1..].to_vec(),
        shape.log_inv_rates,
        queries.to_vec(),
        vec![QUERY_GRINDING_BITS; levels],
        std::iter::once(0).chain(std::iter::repeat_n(1, levels - 1)).collect(),
    ))
}

#[cfg(test)]
pub(crate) mod tests;
