// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// CREDIT: https://github.com/bcc-research/bolt-rs, MIT.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Ported from bolt-rs (https://github.com/bcc-research/bolt-rs, `whir_recursive.rs`).

//! The WHIR configuration: the protocol's constants and the per-level parameters of one opening.
//!
//! # Integers only
//!
//! An opening's parameters are built from integers alone: the level ladder and a table of query counts.
//! So neither the prover nor a verifier computes in floating point.
//!
//! # Where the table comes from
//!
//! The table is what the soundness analysis of Annex B (Theorem `thm:rbr`) derives at every size and rate it covers.
//! That analysis runs in floating point, in the test module only.
//!
//! A test checks every table entry against it, so changing a constant it reads fails until the table is regenerated.

use fiat_shamir::MAX_GRINDING_BITS;
use thiserror::Error;

// The production WHIR configuration: Johnson list decoding at rates 2^-1 to 2^-4 and a 128-bit round-by-round design target over F192.
// The L0 root fixes a candidate list; the immutable commitment-time anchor selects within that list separately. The conservative opening ledger still pays its list size, and every later level takes one OOD sample.

/// Round-by-round design target, in bits.
///
/// This parameter targets the ideal-interactive analysis; it is not a proven
/// 128-bit security level for the complete Fiat-Shamir protocol or concrete primitives.
pub const SECURITY_BITS: usize = 128;

/// Bits a challenge drawn after the commitment loses to the commitment's list.
///
/// Level 0 takes no per-opening out-of-domain sample. Its root fixes a list of
/// up to `L_0 = 1/(2 eta_0 sqrt(rho_0))` polynomials (Johnson bound).
///
/// The commitment-time anchor separately selects an immutable identity within
/// that list. The conservative opening ledger still pays the list-size union bound.
///
/// The value is `ceil(log2 L_0)` at its largest over every configured size and rate.
/// A test pins it to the derivation.
pub const L0_LIST_BITS: usize = 12;

/// The default L0 inverse-rate logarithm: `rho_0 = 2^-LOG_INV_RATE_0`, rate 1/2.
pub const LOG_INV_RATE_0: usize = 1;

/// The smallest supported L0 inverse-rate logarithm: rate `2^-1`.
pub const MIN_LOG_INV_RATE: usize = 1;
/// The largest supported L0 inverse-rate logarithm: rate `2^-4`.
pub const MAX_LOG_INV_RATE: usize = 4;

/// Why no configuration exists for a witness size and a rate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum ConfigError {
    /// An L0 rate outside the supported range.
    #[error("log_inv_rate {log_inv_rate} is not in {MIN_LOG_INV_RATE}..={MAX_LOG_INV_RATE}")]
    RateOutOfRange {
        /// The requested L0 inverse-rate logarithm.
        log_inv_rate: usize,
    },
    /// A witness size outside the tabulated range.
    #[error("log_n {log_n} is not in {MIN_LOG_N}..={MAX_LOG_N}")]
    SizeOutOfRange {
        /// The log of the requested witness size, in words.
        log_n: usize,
    },
}

/// Why the level ladder has no shape for a witness size.
///
/// No size inside the tabulated window reaches this error.
/// The test-only derivation and its fallback ladder take any size, and can.
///
/// `level` counts from L0, the commitment's own code.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub(crate) enum LadderError {
    /// No variable is left after the initial fold.
    #[error("log_n {log_n} does not exceed the initial fold {initial_k}")]
    TooFewVariables {
        /// The log of the witness size, in words.
        log_n: usize,
        /// Variables the initial fold binds.
        initial_k: usize,
    },
    /// The witness is too small for two fold levels.
    #[error("log_n {log_n} gives fewer than two fold levels")]
    TooFewLevels {
        /// The log of the witness size, in words.
        log_n: usize,
    },
    /// A fold smaller than the RS domain reduction it pays for.
    #[error("level {level} folds {fold} variables, below the RS domain reduction {reduction}")]
    FoldBelowReduction {
        /// The level whose rate the fold sets.
        level: usize,
        /// Variables the previous level folds.
        fold: usize,
        /// Bits the total RS domain loses at that step.
        reduction: usize,
    },
}

/// Check that an L0 inverse-rate logarithm is in the supported range.
///
/// # Errors
///
/// Returns the rate when it lies outside `MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE`.
pub(crate) fn validate_log_inv_rate(log_inv_rate: usize) -> Result<(), ConfigError> {
    if !(MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE).contains(&log_inv_rate) {
        return Err(ConfigError::RateOutOfRange { log_inv_rate });
    }
    Ok(())
}

/// Proof-of-work bits each level grinds before its query positions are sampled.
///
/// The query count then only has to close the remaining `SECURITY_BITS - QUERY_GRINDING_BITS` bits.
pub const QUERY_GRINDING_BITS: usize = 17;

const _: () = assert!(QUERY_GRINDING_BITS <= MAX_GRINDING_BITS as usize);

/// Variables the L0 lane fold binds: the log of the L0 interleaving, so a leaf holds `2^6` lanes.
pub const INITIAL_FOLDING_FACTOR: usize = 6;
/// Variables each recursive level folds.
pub const SUBSEQUENT_FOLDING_FACTOR: usize = 4;

/// Bits the total Reed-Solomon domain loses after the initial fold.
///
/// A fold of `k` variables raises the inverse-rate logarithm by `k` minus this reduction.
/// With the six-variable initial fold, the first recursive level's inverse-rate logarithm is `6 - 3 = 3` above L0's.
pub const RS_DOMAIN_INITIAL_REDUCTION_FACTOR: usize = 3;

/// Bits the total Reed-Solomon domain loses after each subsequent fold.
///
/// This is WHIR's recursive-domain schedule, held fixed rather than tuned.
pub const RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR: usize = 1;

const _: () = assert!(RS_DOMAIN_INITIAL_REDUCTION_FACTOR <= INITIAL_FOLDING_FACTOR);
const _: () = assert!(RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR <= SUBSEQUENT_FOLDING_FACTOR);

/// Folding stops once at most this many variables remain.
///
/// The residual polynomial `yr`, at most `2^RESIDUAL_MAX_LOG` values, is then sent in the clear.
pub const RESIDUAL_MAX_LOG: usize = 5;

/// One WHIR opening's shape and per-level soundness parameters.
///
/// The prover and the verifier read exactly the same numbers.
///
/// It is built only in this crate, from the query table, and checked once at construction.
/// Both sides then index its per-level vectors without checking them again.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Config {
    /// Variables the L0 lane fold binds.
    initial_k: usize,
    /// Variables each recursive level folds, L1 first.
    level_ks: Vec<usize>,
    /// Inverse-rate logarithm of each level's code, L0 first.
    log_inv_rates: Vec<usize>,
    /// Query count of each level, L0 first.
    queries: Vec<usize>,
    /// Proof-of-work bits of each level's query phase, L0 first.
    grinding_bits: Vec<usize>,
    /// Out-of-domain samples of each level, L0 first.
    ood_samples: Vec<usize>,
}

impl Config {
    /// A config of `level_ks.len()` recursive levels after the lane fold.
    ///
    /// # Panics
    ///
    /// - If the lane fold binds no variable, or there is no recursive level.
    /// - If a per-level vector does not cover L0 to the last level.
    /// - If L0 takes an OOD sample, or a level grinds more bits than the digest's low word holds.
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
        // The per-opening L0 oracle takes no additional OOD sample. Its immutable commitment-time anchor is handled separately with a weight restricted to the occupied lane prefix.
        assert_eq!(ood_samples[0], 0, "L0 takes no per-opening OOD sample");
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

    /// Per-level query counts (L0, L1, ..., L_r), from the soundness analysis.
    pub fn queries(&self) -> &[usize] {
        &self.queries
    }

    /// Per-level query-phase grinding bits (L0, L1, ..., L_r).
    ///
    /// Each level grinds right before its query positions are sampled.
    /// That is after the next level's root and OOD claims, or after the residual at the last level.
    pub fn grinding_bits(&self) -> &[usize] {
        &self.grinding_bits
    }

    /// Per-level out-of-domain samples (L0, L1, ..., L_r).
    ///
    /// Each later-level sample is drawn right after that level's root enters the transcript.
    /// L0 takes no additional sample: its immutable commitment-time anchor is
    /// handled separately by the typed stack wrapper, restricted to occupied lanes.
    pub fn ood_samples(&self) -> &[usize] {
        &self.ood_samples
    }
}

/// Level-ladder shape: the per-level inverse-rate logarithms and folds, index 0 being L0.
struct LadderShape {
    /// Inverse-rate logarithm of each level's code, L0 first.
    log_inv_rates: Vec<usize>,
    /// Variables each level folds, the lane fold first.
    k_levels: Vec<usize>,
}

/// Descend the level ladder, `SUBSEQUENT_FOLDING_FACTOR` variables a level, until `RESIDUAL_MAX_LOG` or fewer remain.
///
/// `next_rate` picks each new level's inverse-rate logarithm from four integers:
///
/// ```text
///     (new level, previous rate, fold just taken, message dimension the new level carries)
/// ```
///
/// It is the only thing that separates the production ladder from the test-support one.
///
/// # Errors
///
/// - A ladder error when nothing is left after the lane fold, or when fewer than two levels result.
/// - Whatever `next_rate` returns.
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

/// The production ladder.
///
/// The total RS domain loses `RS_DOMAIN_INITIAL_REDUCTION_FACTOR` bits after the initial fold, then one bit a fold.
/// So a fold of `k` variables raises the inverse-rate logarithm by `k - reduction`.
///
/// # Errors
///
/// Returns a ladder error for a size with no ladder, or a fold below the reduction it pays for.
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

/// Log of the smallest configured witness, in words: the production ladder's floor, with one level of margin.
pub const MIN_LOG_N: usize = 15;
/// Log of the largest configured witness, in words.
pub const MAX_LOG_N: usize = 28;

/// Per-level query counts (L0, L1, ...) of the production opening.
///
/// The entry for a rate and a size is at `[log_inv_rate - MIN_LOG_INV_RATE][log_n - MIN_LOG_N]`.
/// Each entry is what the soundness derivation chooses, and a test pins it to that derivation.
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

/// The configuration prover and verifier share for a witness of `2^log_n` words of `K` at L0 rate `2^-log_inv_rate`.
///
/// The Johnson/OOD profile with a 128-bit design target: the ladder, tabulated query counts, [`QUERY_GRINDING_BITS`] at every level, and one OOD sample at every level past L0. The immutable commitment anchor is handled separately.
///
/// # Errors
///
/// Returns a rate outside `MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE`, or a size outside `MIN_LOG_N..=MAX_LOG_N`.
pub fn config_for_rate(log_n: usize, log_inv_rate: usize) -> Result<Config, ConfigError> {
    validate_log_inv_rate(log_inv_rate)?;
    if !(MIN_LOG_N..=MAX_LOG_N).contains(&log_n) {
        return Err(ConfigError::SizeOutOfRange { log_n });
    }
    let shape = derive_ladder_shape(log_n, INITIAL_FOLDING_FACTOR, log_inv_rate)
        .expect("the tabulated window always has a ladder");
    let levels = shape.k_levels.len();
    let queries = WHIR_QUERIES[log_inv_rate - MIN_LOG_INV_RATE][log_n - MIN_LOG_N];
    Ok(Config::new(
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
