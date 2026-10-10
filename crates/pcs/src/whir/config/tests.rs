// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// CREDIT: https://github.com/bcc-research/bolt-rs, MIT.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Ported from bolt-rs (https://github.com/bcc-research/bolt-rs,
// `whir_recursive.rs`).

//! The floating-point soundness derivation of the WHIR parameters, run only in tests.
//!
//! It is the source of truth for the integer query table the production configuration reads.
//! A test pins that table to it entry by entry, and prints the replacement rows when they differ.
//!
//! # Specification
//!
//! The analysis is Theorem `thm:rbr` of the PCS annex (`doc/leanvm/body/b-polynomial-commitment-scheme.tex`).
//! Each row of its error table becomes one check at every level:
//!
//! - batching challenge: `(J - 1) L / |F|`, one challenge per level whose powers batch the level's claims.
//! - fold challenge: `2 L / |F| + eps`, with `eps` the MCA error of `thm:mca-johnson`.
//!   The `2 L / |F|` part is checked with the algebraic terms, and `eps` as the proximity gap.
//! - OOD challenge: `binom(L, 2) mu / |F|`, at every level past L0.
//! - query message: `(1 - gamma)^t`, plus the query grinding bits.
//!
//! The fold-challenge bound relies on the mutual correlated agreement result the annex cites (BCHKS25, Theorem 4.6).
//!
//! # Why each term is checked alone
//!
//! The target is round-by-round (RBR) soundness: every entry must clear the security target on its own.
//! The Fiat-Shamir error per random-oracle query is then the maximum of the entries, not their sum.

#![expect(
    clippy::float_arithmetic,
    clippy::cast_precision_loss,
    reason = "The soundness analysis is real-valued; it only runs in tests, which pin the integer table to it."
)]
use super::{
    Config, ConfigError, INITIAL_FOLDING_FACTOR, L0_LIST_BITS, LOG_INV_RATE_0, LadderError, MAX_LOG_INV_RATE,
    MAX_LOG_N, MIN_LOG_INV_RATE, MIN_LOG_N, MIN_LOG_N_HIDING, QUERY_GRINDING_BITS, RS_DOMAIN_INITIAL_REDUCTION_FACTOR,
    RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR, SECURITY_BITS, WHIR_QUERIES, WHIR_QUERIES_HIDING, config_for_rate,
    config_for_rate_hiding, derive_ladder, derive_ladder_shape, validate_log_inv_rate,
};
use primitives::field::F64;
use std::fmt::Write;
use thiserror::Error;

/// Why the derivation found no sound configuration, or why one it was handed is unsound.
///
/// Levels count from L0, the commitment's own code.
#[derive(Clone, Copy, Debug, PartialEq, Error)]
#[non_exhaustive]
pub(crate) enum DerivationError {
    /// The rate is out of range.
    #[error(transparent)]
    Config(#[from] ConfigError),
    /// The level ladder rules the size out.
    #[error(transparent)]
    Ladder(#[from] LadderError),
    /// A witness smaller than one packed word.
    #[error("witness log size {m} is below the packed-word log size {packing}", packing = F64::DEGREE.ilog2() as usize)]
    WitnessBelowPacking { m: usize },
    /// No parameter choice at this level reaches the soundness target.
    #[error("no level {level} parameters reach the soundness target at rate 2^-{log_inv_rate}")]
    NoFeasibleLevel { level: usize, log_inv_rate: usize },
    /// The witness size and the packing disagree.
    #[error("packed-witness log size {log_n} is inconsistent with witness log size {m}")]
    PackingMismatch { log_n: usize, m: usize },
    /// The levels do not fold exactly the witness's variables.
    #[error("the levels and the residual cover {covered} variables, and the witness has {log_n}")]
    FoldSum { covered: usize, log_n: usize },
    /// The configuration has no level.
    #[error("the configuration has no level")]
    NoLevels,
    /// L0 does not fold and interleave the initial fold's variables.
    #[error("L0 must fold and interleave {initial_k} variables")]
    L0Fold { initial_k: usize },
    /// A level at rate one, which is no code.
    #[error("level {level} has rate one")]
    RateOne { level: usize },
    /// A level with an empty message.
    #[error("level {level} has no message columns")]
    EmptyMessage { level: usize },
    /// A level's message and interleaving do not split its input.
    #[error("level {level} splits {dim} variables, and its input has {expected}")]
    LevelDimension { level: usize, dim: usize, expected: usize },
    /// A level's rate is not the one its domain reduction gives.
    #[error("level {level} has log_inv_rate {log_inv_rate}, and its domain reduction gives {expected}")]
    RateLadder {
        level: usize,
        log_inv_rate: usize,
        expected: usize,
    },
    /// A Johnson slack outside `(0, 1 - sqrt(rho))`.
    #[error("level {level} has eta {eta}, outside (0, {max})")]
    EtaOutOfRange { level: usize, eta: f64, max: f64 },
    /// OOD samples where none belong (L0), or none where some must (later levels).
    #[error("level {level} has {samples} OOD samples: L0 takes none, later levels at least one")]
    OodSamples { level: usize, samples: usize },
    /// The OOD binding falls short of the target.
    #[error("level {level}: OOD binding gives {bits:.2} bits, below {target}")]
    OodSoundness { level: usize, bits: f64, target: usize },
    /// The queries do not cover what grinding leaves.
    #[error("level {level}: queries give {bits:.2} bits, below {target}")]
    QuerySoundness { level: usize, bits: f64, target: usize },
    /// The proximity gap falls short of the target.
    #[error("level {level}: the proximity gap gives {bits:.2} bits, below {target}")]
    ProximityGap { level: usize, bits: f64, target: usize },
    /// The list-unioned algebraic checks fall short of the target.
    #[error("level {level}: the algebraic checks give {bits:.2} bits, below {target}")]
    AlgebraicSoundness { level: usize, bits: f64, target: usize },
    /// A level targets fewer bits than the whole configuration.
    #[error("level {level} targets {bits} bits, below the global {global}")]
    LevelTarget { level: usize, bits: usize, global: usize },
    /// The levels leave a residual of another size than the configured one.
    #[error("the levels leave {dim} variables, and the residual has {yr_log_n}")]
    ResidualMismatch { dim: usize, yr_log_n: usize },
}

/// Largest BCHKS25 theorem parameter `m` the per-level slack search tries.
///
/// # Why this value
///
/// At every configured size the proximity-gap target fails far below it, which ends the search.
/// The generous cap keeps the search deterministic even if the sizes grow.
const JOHNSON_ETA_SEARCH_MAX_M: usize = 4096;

/// Bits the query phase closes on its own at every level of the ad-hoc test shapes.
///
/// It is the policy of 100 bits from queries alone, with no grinding.
const UDR_TARGET_BITS: f64 = 100.0;

/// Number of queries reaching 100 bits in the unique-decoding regime, at rate `2^-log_inv_rate`.
///
/// The radius is `gamma = delta / 2 = (1 - rho) / 2`, and each query closes `log_2(1 / (1 - gamma))` bits.
/// Within the unique-decoding radius the prover is pinned to one codeword, so no list union bound applies.
///
/// Since `gamma < 1/2`, a query closes less than one bit.
/// So even the lowest rates need slightly more than 100 queries.
///
/// # Panics
///
/// Panics at `log_inv_rate = 0`: rate one is no code and has no soundness.
fn udr_queries(log_inv_rate: usize) -> usize {
    assert!(log_inv_rate > 0, "log_inv_rate=0 (rate 1) has no soundness");
    let per_q = udr_per_query_bits_asymptotic(log_inv_rate);
    // Round up, so the queries reach at least the target.
    (UDR_TARGET_BITS / per_q).ceil() as usize
}

/// An ad-hoc WHIR configuration for the PCS tests, built without the per-level soundness derivation.
///
/// `log_n` is the packed witness's log size, six variables below the Boolean witness's.
/// Each later level lowers the rate by at least one bit, and every level's queries must fit its block length.
///
/// # Why it exists
///
/// The small PCS tests use sizes below the production derivation's feasibility floor.
/// Production configurations always come from the per-level-sound derivation.
///
/// # Errors
///
/// Fails when some level cannot fit its queries, for example when `log_n` is too small for the rate.
pub(crate) fn default_config(
    log_n: usize,
    log_batch_size: usize,
    log_inv_rate: usize,
) -> Result<Config, DerivationError> {
    // The lane fold binds the commitment's interleaving, one variable per bit of the batch size.
    let initial_k = log_batch_size;
    // L0's block, `2^(log_n - initial_k + log_inv_rate)` positions, must hold its queries.
    if log_n > initial_k && (1usize << (log_n - initial_k + log_inv_rate)) < udr_queries(log_inv_rate) {
        return Err(DerivationError::NoFeasibleLevel { level: 0, log_inv_rate });
    }
    // Each new level takes the smallest rate strictly below the previous one whose block holds its queries.
    let shape = derive_ladder(
        log_n,
        initial_k,
        log_inv_rate,
        |level, rate_running, _fold, cols_next| {
            let mut next_rate = rate_running + 1;
            while (1usize << (cols_next + next_rate)) < udr_queries(next_rate) {
                next_rate += 1;
                // Give up past rate `2^-20`: no test size needs a code that sparse.
                if next_rate > 20 {
                    return Err(DerivationError::NoFeasibleLevel {
                        level,
                        log_inv_rate: next_rate,
                    });
                }
            }
            Ok(next_rate)
        },
    )?;

    // Queries only, with no grinding and no OOD sample at any level.
    let n_levels = shape.log_inv_rates.len();
    let queries = shape.log_inv_rates.iter().map(|&r| udr_queries(r)).collect();
    Ok(Config::new(
        initial_k,
        shape.k_levels[1..].to_vec(),
        shape.log_inv_rates,
        queries,
        vec![0usize; n_levels],
        vec![0usize; n_levels],
        0,
    ))
}

/// The configuration the derivation gives a `2^log_n`-word witness at L0 rate `2^-log_inv_rate`, which the table must hold.
fn derive_config(log_n: usize, log_inv_rate: usize) -> Result<Config, DerivationError> {
    WhirSecurityConfig::derive_config_with_log_inv_rate(log_n + F64::DEGREE.ilog2() as usize, log_inv_rate, 0)?
        .to_config()
}

/// The derivation of a hiding opening: L0's code padded by `k = q_0 + 2` past each lane's power of two, `q_0` its own query count.
///
/// A larger code needs more queries, so `k` starts from the unpadded `q_0 + 2` and grows until the query count it gives keeps it.
fn derive_hiding_security(log_n: usize, log_inv_rate: usize) -> Result<WhirSecurityConfig, DerivationError> {
    let m = log_n + F64::DEGREE.ilog2() as usize;
    let mut padding = WhirSecurityConfig::derive_config_with_log_inv_rate(m, log_inv_rate, 0)?.levels[0].queries + 2;
    loop {
        let cfg = WhirSecurityConfig::derive_config_with_log_inv_rate(m, log_inv_rate, padding)?;
        let next = cfg.levels[0].queries + 2;
        if next == padding {
            return Ok(cfg);
        }
        assert!(next > padding, "the padded query count grows with the padding");
        padding = next;
    }
}

/// The configuration the hiding table must hold.
fn derive_hiding_config(log_n: usize, log_inv_rate: usize) -> Result<Config, DerivationError> {
    derive_hiding_security(log_n, log_inv_rate)?.to_config()
}

/// A configuration for a `2^log_n`-word witness in the PCS tests.
///
/// It is the production derivation at the default L0 rate where that is feasible, and an ad-hoc shape below.
///
/// # Panics
///
/// Panics when no ad-hoc shape fits `log_n` either.
pub(crate) fn test_config_for(log_n: usize) -> Config {
    if let Ok(config) = derive_config(log_n, LOG_INV_RATE_0) {
        return config;
    }
    // Below the production floor: prefer the widest lane fold, then the highest rate, that fits.
    for log_batch_size in (1..=5).rev() {
        for log_inv_rate in 1..=4 {
            if let Ok(config) = default_config(log_n, log_batch_size, log_inv_rate) {
                return config;
            }
        }
    }
    panic!("no feasible whir config at log_n = {log_n}");
}

// Security configuration schema
//
// An auditable per-level specification: query count, grinding bits, Johnson slack, and the analysis behind them.
//
// Every level works at the Johnson radius minus a slack: `gamma = 1 - sqrt(rho) - eta`.
//
// The proximity gap is MCA up to the Johnson bound (BCHKS25 Thm 4.6, `thm:mca-johnson` in the PCS annex).
// Its exceptional set is `a = O_rho(n / eta^5)`.
//
// The slack search keeps `log_2(q / a)` above the target on its own.
// So the fold challenges need no grinding.
//
// How each level handles its list (WHIR, ePrint 2024/1586, Theorem 7.5):
//
// - L0 takes no OOD sample, so its root binds the prover only to a list of up to `L_0` polynomials.
//   Every challenge drawn between the root and the opening pays a union bound over that list.
// - L1 and later take explicit multilinear OOD samples, which pin one codeword of the level's list.
//   Their query phases pay no union bound, and the query counts below include none.
//
// Grinding lands after a level's Merkle root is observed and before its query positions are drawn.

/// Parameters of one level of the WHIR ladder.
///
/// L0 is the commitment itself, reused rather than committed again.
/// L1 and later are the opening's own commitments, and the residual sent in the clear is described apart.
#[derive(Clone, Debug)]
struct WhirLevelConfig {
    /// Log of the code's inverse rate: a codeword is `2^log_inv_rate` times longer than its message.
    log_inv_rate: usize,
    /// Log of the message's field columns, so that `log_msg_cols + log_inv_rate` is the log of the block length.
    log_msg_cols: usize,
    /// Coefficients a hiding commitment adds past each lane's `2^log_msg_cols`: nonzero only at L0 of a hiding opening.
    padding: usize,
    /// Log of lane width per Merkle leaf at this level. For L0 = `initial_k`;
    /// for L_i (i ≥ 1) = the previous level's `k`.
    log_num_interleaved: usize,
    /// Number of sumcheck folds this level takes: the lane fold at L0, the level fold past it.
    k: usize,
    /// Slack below the Johnson radius: `gamma = 1 - sqrt(rho) - eta`.
    eta: f64,
    /// Number of codeword positions this level opens, which bounds the query term `(1 - gamma)^queries`.
    queries: usize,
    /// Proof-of-work bits ground after this level's commitment and before its query positions are drawn.
    ///
    /// Each bit replaces about `1 / log_2(1 / (1 - gamma))` queries at this level.
    grinding_bits: usize,
    /// Out-of-domain samples taken right after this level's commitment enters the transcript.
    ///
    /// Each binds the prover to one codeword of the interleaved list through a multilinear evaluation claim.
    /// It is 0 at L0, which is only list binding, and at least 1 at every later level.
    ood_samples: usize,
    /// Security target this level guarantees, with grinding counted.
    target_security_bits: usize,
}

/// The residual block sent in the clear after the last fold level.
///
/// It has no commitment and no queries, so its only parameter is its size.
#[derive(Clone, Debug)]
struct FinalBlockConfig {
    /// Log of the number of extension-field values sent in the clear.
    ///
    /// The last level's sumcheck stops at this many variables instead of folding to one.
    yr_log_n: usize,
}

/// The complete security specification of one WHIR opening, for one witness size.
///
/// # Invariants
///
/// - The lane fold, the later folds and the residual cover the `log_n` witness variables exactly.
/// - Each level's input splits into its message columns and its lanes, and its rate follows the domain reduction.
/// - Each level's slack `eta` is finite and inside `(0, 1 - sqrt(rho))` for the level's reduced rate.
/// - L0 takes no OOD sample, and every later level takes at least one.
/// - Each level's proximity gap, OOD binding and algebraic checks reach its target.
/// - Each level's queries reach its target minus its grinding bits.
#[derive(Clone, Debug)]
struct WhirSecurityConfig {
    /// Log of the witness's bit count.
    m: usize,
    /// Log of the committed witness's packed-word count.
    log_n: usize,
    /// Variables the L0 lane fold binds.
    ///
    /// It must match the commitment's interleaving, so that L0 is the commitment and is not committed again.
    initial_k: usize,
    /// Round-by-round security target, in bits.
    ///
    /// Every error term attached to a verifier challenge must clear it on its own.
    /// It does not bound the sum of every interactive failure probability by `2^-target_security_bits`.
    target_security_bits: usize,
    /// Per-level parameters, in order L0, L1, L2, ...
    levels: Vec<WhirLevelConfig>,
    /// The residual block.
    final_block: FinalBlockConfig,
}

/// Log of the extension-field size the analysis uses: `q = |F| = 2^192`.
const ANALYSIS_LOG_Q: f64 = 192.0;

/// A level's Reed-Solomon code: block length `2^(log_msg_cols + log_inv_rate)`, dimension `2^log_msg_cols + padding`.
#[derive(Clone, Copy, Debug)]
struct Code {
    log_inv_rate: usize,
    log_msg_cols: usize,
    padding: usize,
}

impl Code {
    const fn plain(log_inv_rate: usize, log_msg_cols: usize) -> Self {
        Self {
            log_inv_rate,
            log_msg_cols,
            padding: 0,
        }
    }

    /// Base-two logarithm of the block length.
    const fn log_block_len(self) -> usize {
        self.log_msg_cols + self.log_inv_rate
    }
}

/// BCHKS25 parameter `rho = k/n` for an RS code of dimension `k + 1`.
/// Our message has `2^log_msg_cols + padding` coefficients (degree strictly below that
/// value), so `k = 2^log_msg_cols + padding - 1`. This differs perceptibly from the
/// nominal code rate at the small recursive levels.
fn reduced_rate(code: Code) -> f64 {
    let dimension = (code.log_msg_cols as f64).exp2() + code.padding as f64;
    (dimension - 1.0) / (code.log_block_len() as f64).exp2()
}

/// `log_2(a)` for the MCA error `a / |F|` up to the Johnson bound (`thm:mca-johnson`, BCHKS25 Theorem 4.6).
///
/// The code has reduced rate `rho`, block length `n`, slack `eta` and radius `gamma = 1 - sqrt(rho) - eta`:
///
/// ```text
///     a = [2 (m + 1/2)^5 + 3 (m + 1/2) gamma rho] / (3 rho^(3/2)) * n + (m + 1/2) / sqrt(rho)
///     m = max(ceil(sqrt(rho) / eta), 3)
/// ```
///
/// # Why it bounds every fold
///
/// The theorem is stated for a two-row word, and the same error bounds the fold of a `2^l`-row word.
/// The code is linear over the fold challenge's field, so MCA is invariant under row interleaving (Jo, 2026/891).
///
/// Lemma `lem:fold-list` of the PCS annex states both hypotheses.
#[expect(
    clippy::suboptimal_flops,
    reason = "Keep the rounding of the protocol parameter formulas unchanged."
)]
fn paper_thm_ca_johnson_log_a(code: Code, eta: f64) -> f64 {
    let rho = reduced_rate(code);
    let sqrt_rho = rho.sqrt();
    let gamma = 1.0 - sqrt_rho - eta;
    // BCHKS25 Thm 4.6: m = ⌈√ρ/(1−√ρ−γ)⌉ = ⌈√ρ/η⌉, floored at 3.
    let m_param = johnson_m_param(code, eta);
    let half = m_param + 0.5;
    let half5 = half.powi(5);
    // The bracket over `3 rho^(3/2)`, then scaled by the block length `n`.
    let numerator = 2.0 * half5 + 3.0 * half * gamma * rho;
    let denominator = 3.0 * rho.powf(1.5);
    let n = (code.log_block_len() as f64).exp2();
    let a = (numerator / denominator) * n + half / sqrt_rho;
    a.log2()
}

/// Integer parameter `m = max(⌈√ρ/η⌉, 3)` of BCHKS25 Thm 4.6 (list
/// correlated agreement), represented as `f64` for the bound. Beware: the
/// plain, non-list Thm 1.5 has the factor-two-smaller `⌈√ρ/(2η)⌉`, and
/// Flock's Thm 8 quotes Thm 4.6 with that non-list parameter; the list form
/// costs a factor 2 of slack (see the footnote in the PCS annex
/// Thm `thm:mca-johnson`).
fn johnson_m_param(code: Code, eta: f64) -> f64 {
    let sqrt_rho = reduced_rate(code).sqrt();
    ((sqrt_rho / eta).ceil() as usize).max(3) as f64
}

/// Per-query log₂(1/(1−γ)) under the Johnson regime: each query closes
/// `log_2(1/(1-γ))` bits of soundness against a γ-far adversary.
fn paper_per_query_bits(code: Code, eta: f64) -> f64 {
    let rho = reduced_rate(code);
    let gamma = 1.0 - rho.sqrt() - eta;
    (1.0 / (1.0 - gamma)).log2()
}

/// Bits one query closes in the unique-decoding regime, at radius `gamma = delta / 2` with `delta = 1 - rho`.
///
/// It uses the nominal rate, and backs only the ad-hoc test shapes.
fn udr_per_query_bits_asymptotic(log_inv_rate: usize) -> f64 {
    let rho = (-(log_inv_rate as f64)).exp2();
    let gamma = (1.0 - rho) / 2.0;
    (1.0 / (1.0 - gamma)).log2()
}

/// `log_2` of the Johnson list-size bound for an interleaved Reed-Solomon word at radius `1 - sqrt(rho) - eta`.
///
/// The bound is `L <= 1 / (2 eta sqrt(rho))` whatever the interleaving (`thm:johnson-interleaved`).
///
/// # Why the interleaving does not enter
///
/// Interleaving keeps the relative distance `delta = 1 - rho` and only enlarges the alphabet.
/// This form of the Johnson bound uses only the distance and the radius, so it holds with no `L_base^r` blow-up.
///
/// The interleaved bound of Gopalan, Guruswami and Raghavendra, `C(b + r, r) L_base^r` (their Thm 2.5), is not needed.
/// It only matters past the Johnson radius `1 - sqrt(rho)`, toward `delta`.
///
/// The general GGR (Gopalan-Guruswami-Raghavendra, Thm 2.5) interleaved bound
/// `L_int ≤ C(b+r, r)·L_base^r` is only needed to push the list-decoding
/// radius *past* the Johnson bound toward `δ`. WHIR deliberately sits at
/// `θ = 1 − √ρ − η`, strictly below the Johnson radius by slack `η > 0`, so
/// that regime never applies and the plain Johnson bound is both correct and
/// far tighter (it dominates GGR throughout the regime RS can reach).
fn johnson_interleaved_list_log2(code: Code, eta: f64) -> f64 {
    debug_assert!(eta > 0.0, "η must be > 0 to stay strictly below the Johnson radius");
    let rho = reduced_rate(code);
    let sqrt_rho = rho.sqrt();
    let l_base = 1.0 / (2.0 * eta * sqrt_rho);
    l_base.log2()
}

/// Bits of the worst list-unioned algebraic check at one level.
///
/// It covers the batch row of `thm:rbr`, `(J - 1) L / |F|`, and the `2 L / |F|` part of its fold row.
/// A degree-`d` identity test unioned over a Johnson list of size `L` fails with probability at most `d L / |F|`.
///
/// # The degree `d`
///
/// - At L0: the total degree of the ring switch's GF(2^64)-to-GF(2^192) batching map.
/// - Past L0: `prev_queries + ood_samples`, the batch polynomial's degree in the level's single `lambda`.
/// - At least 2, the degree of a quadratic sumcheck round, which is the fold row's `2 L / |F|`.
///
/// - at L0, the total degree of the GF64-to-GF192 ring-switch batching map, whose challenges are drawn before L0's batch against claims on the committed polynomial, so they union over L0's list alone (the PCS annex, after `thm:rbr`);
///   L0's own `J_0 - 1` is set by the outer protocol's claim pool, a few hundred claims, orders below that degree;
/// - past L0, `J - 1 = prev_queries + ood_samples`, the batch polynomial's degree in the level's single lambda.
///   The claims it batches are the ones the PREVIOUS level's query phase raised (`thm:rbr`: `J_i = n_{i-1} + 2`, one per query plus the residual and the OOD claim), so this level's own query count is the wrong quantity: query counts fall with depth, so using it would understate the degree;
///   the ring switch is no term here, since this level's oracle and list come after its challenges;
/// - 2 for quadratic sumcheck.
fn johnson_algebraic_bits_for(level: usize, code: Code, eta: f64, prev_queries: usize, ood_samples: usize) -> f64 {
    let log2_l = johnson_interleaved_list_log2(code, eta);
    let batch_degree = if level == 0 {
        crate::ring_switch::tests::RING_SWITCH_SOUNDNESS_DEGREE
    } else {
        prev_queries + ood_samples
    };
    // Why: the sumcheck rounds have degree 2, which covers the fold row's `2 L / |F|`.
    let degree = batch_degree.max(2);
    // `log_2(|F| / (d L))`.
    ANALYSIS_LOG_Q - (degree as f64).log2() - log2_l
}

/// Bits of the worst list-unioned algebraic check at one configured level.
///
/// `prev_queries` is the previous level's query count, and 0 at L0.
fn johnson_algebraic_bits(level: usize, config: &WhirLevelConfig, prev_queries: usize) -> f64 {
    johnson_algebraic_bits_for(level, config.code(), config.eta, prev_queries, config.ood_samples)
}

/// The query count of the level before level `i`, whose claims level `i` batches, or 0 at L0.
const fn prev_queries_at(levels: &[WhirLevelConfig], i: usize) -> usize {
    if i == 0 { 0 } else { levels[i - 1].queries }
}

/// Bits of a level's OOD binding, for a multilinear of `mu_vars = log_msg_cols + log_num_interleaved` variables.
///
/// # With samples (`ood_samples = s >= 1`)
///
/// This is `lem:ood` and the OOD row of `thm:rbr`, `binom(L, 2) mu / |F|`, generalized to `s` samples.
/// The bad event is two distinct list members agreeing on all `s` random points of `F^mu`.
///
/// Each point catches a difference except with probability `mu / |F|` (Schwartz-Zippel, total degree at most `mu`).
/// A union over the pairs, `binom(L, 2) <= L^2 / 2`, gives:
///
/// ```text
///     bits = s (192 - log_2 mu) - (2 log_2 L - 1)
/// ```
///
/// # Without samples (`ood_samples = 0`, L0)
///
/// The protocol takes no OOD sample at commitment, so the PCS is only list binding (the PCS annex, opening paragraph).
/// This term then stands for a degree-`mu` identity test drawn before the opening.
///
/// That test must hold against every list member, a union over the list rather than over pairs:
///
/// ```text
///     bits = 192 - log_2 L - log_2 mu
/// ```
#[expect(
    clippy::suboptimal_flops,
    reason = "Keep the rounding of the protocol parameter formulas unchanged."
)]
fn paper_ood_bits(code: Code, eta: f64, mu_vars: usize, ood_samples: usize) -> f64 {
    let log2_l = johnson_interleaved_list_log2(code, eta);
    let log2_mu = (mu_vars as f64).log2();
    if ood_samples == 0 {
        ANALYSIS_LOG_Q - log2_l - log2_mu
    } else {
        ood_samples as f64 * (ANALYSIS_LOG_Q - log2_mu) - (2.0 * log2_l - 1.0)
    }
}

/// The slack, query count and OOD sample count the per-level search picks.
///
/// The search minimizes queries.
/// Ties keep the smallest theorem parameter `m`, which has the largest slack and so the smallest list bound.
struct OptimizedJohnsonLevel {
    /// Slack below the Johnson radius.
    eta: f64,
    /// Queries closing the target left after grinding.
    queries: usize,
    /// OOD samples: none at L0, the fewest that reach the target past it.
    ood_samples: usize,
}

/// The smallest slack whose theorem parameter `ceil(sqrt(rho) / eta)` is exactly `m`.
///
/// A smaller slack would raise `m` and worsen the proximity-gap bound.
/// For a fixed `m` this boundary gives the largest radius, so the most bits per query.
#[expect(
    clippy::while_float,
    reason = "Advance by one ULP until the rounded theorem parameter satisfies the integer bound."
)]
fn johnson_eta_for_m(code: Code, m: usize) -> f64 {
    debug_assert!(m >= 3);
    let sqrt_rho = reduced_rate(code).sqrt();
    let mut eta = sqrt_rho / m as f64;
    while johnson_m_param(code, eta) > m as f64 {
        eta = f64::from_bits(eta.to_bits() + 1);
    }
    debug_assert_eq!(johnson_m_param(code, eta), m as f64);
    eta
}

/// Choose one level's Johnson slack by a search over the theorem parameter `m`.
///
/// A candidate must reach the proximity-gap target with no fold grinding, and every other non-grindable term too.
/// The search uses the exact reduced rate and the list form of the BCHKS25 parameter.
///
/// # Errors
///
/// Fails when no `m` reaches the target with queries that fit the level's block.
fn optimize_johnson_level(
    level: usize,
    code: Code,
    log_num_interleaved: usize,
    target_bits: usize,
    query_grinding_bits: usize,
    prev_queries: usize,
) -> Result<OptimizedJohnsonLevel, DerivationError> {
    let target = target_bits as f64;
    // Grinding closes some bits, and the queries close the rest (at least one bit).
    let query_target = target_bits.saturating_sub(query_grinding_bits).max(1) as f64;
    let mu = code.log_msg_cols + log_num_interleaved;
    let block_len = 1usize << code.log_block_len();
    let log_inv_rate = code.log_inv_rate;
    let mut best: Option<OptimizedJohnsonLevel> = None;

    for m in 3..=JOHNSON_ETA_SEARCH_MAX_M {
        let eta = johnson_eta_for_m(code, m);
        let max_eta = 1.0 - reduced_rate(code).sqrt();
        if eta >= max_eta {
            continue;
        }

        let eps_pg = ANALYSIS_LOG_Q - paper_thm_ca_johnson_log_a(code, eta);
        // At the theorem-parameter boundaries a grows monotonically with m;
        // no later candidate can recover once the proximity-gap target fails.
        if eps_pg + 1e-12 < target {
            break;
        }

        let per_q = paper_per_query_bits(code, eta);
        if !per_q.is_finite() || per_q <= 0.0 {
            continue;
        }
        let queries = (query_target / per_q).ceil() as usize;
        if queries > block_len {
            continue;
        }

        // OOD: none at L0, else the fewest samples (up to 8) that reach the target.
        let ood_samples = if level == 0 {
            0
        } else {
            match (1..=8usize).find(|&s| paper_ood_bits(code, eta, mu, s) + 1e-12 >= target) {
                Some(samples) => samples,
                None => continue,
            }
        };
        let eps_ood = paper_ood_bits(code, eta, mu, ood_samples);
        if eps_ood + 1e-12 < target
            || johnson_algebraic_bits_for(level, code, eta, prev_queries, ood_samples) + 1e-12 < target
        {
            continue;
        }

        let candidate = OptimizedJohnsonLevel {
            eta,
            queries,
            ood_samples,
        };
        // Keep strictly fewer queries only, so a tie stays with the smaller `m`.
        if best.as_ref().is_none_or(|current| candidate.queries < current.queries) {
            best = Some(candidate);
        }
    }

    best.ok_or(DerivationError::NoFeasibleLevel { level, log_inv_rate })
}

impl WhirLevelConfig {
    /// The level's code.
    const fn code(&self) -> Code {
        Code {
            log_inv_rate: self.log_inv_rate,
            log_msg_cols: self.log_msg_cols,
            padding: self.padding,
        }
    }

    /// Proximity-gap and per-query soundness bits this level delivers:
    ///   eps_pg_bits    = log₂(q/a) under the Johnson threshold-a formula
    ///   eps_query_bits = Q · log₂(1/(1−γ))
    fn paper_predicted_bits(&self) -> (f64, f64) {
        // Why: fold row of `thm:rbr`, MCA part, the same at every round whatever the interleaving (`lem:fold-list`).
        let log_a = paper_thm_ca_johnson_log_a(self.code(), self.eta);
        let eps_pg = ANALYSIS_LOG_Q - log_a;
        // Per-query soundness WITHOUT a list union bound: the OOD binding (see
        // `paper_ood_bits`) pins the prover to a single codeword of the
        // interleaved list before queries are drawn.
        let per_q = paper_per_query_bits(self.code(), self.eta);
        let eps_query = self.queries as f64 * per_q;
        (eps_pg, eps_query)
    }

    /// Bits of the OOD binding this level delivers, over its `log_msg_cols + log_num_interleaved` variables.
    fn paper_predicted_ood_bits(&self) -> f64 {
        let mu = self.log_msg_cols + self.log_num_interleaved;
        paper_ood_bits(self.code(), self.eta, mu, self.ood_samples)
    }
}

impl WhirSecurityConfig {
    /// Check that the configuration is internally consistent and meets its analysis.
    ///
    /// # Errors
    ///
    /// Returns the first violation found.
    fn validate(&self) -> Result<(), DerivationError> {
        // The bit-level size is the packed size plus the six variables of a 64-bit word.
        if self.log_n + F64::DEGREE.ilog2() as usize != self.m {
            return Err(DerivationError::PackingMismatch {
                log_n: self.log_n,
                m: self.m,
            });
        }

        // Shape: the lane fold, the later levels' folds and the residual cover the witness exactly.
        let levels_level_k_sum: usize = self.levels.iter().skip(1).map(|lv| lv.k).sum();
        let yr_log_n = self.final_block.yr_log_n;
        let covered = self.initial_k + levels_level_k_sum + yr_log_n;
        if covered != self.log_n {
            return Err(DerivationError::FoldSum {
                covered,
                log_n: self.log_n,
            });
        }

        // L0 folds and interleaves exactly the lane fold's variables.
        let l0 = self.levels.first().ok_or(DerivationError::NoLevels)?;
        if l0.k != self.initial_k || l0.log_num_interleaved != self.initial_k {
            return Err(DerivationError::L0Fold {
                initial_k: self.initial_k,
            });
        }

        // Per-level checks, tracking the variables each level receives.
        let mut dim_in = self.log_n;
        for (level, lv) in self.levels.iter().enumerate() {
            // A code needs a rate below one and a nonempty message.
            if lv.log_inv_rate == 0 {
                return Err(DerivationError::RateOne { level });
            }
            if lv.log_msg_cols == 0 {
                return Err(DerivationError::EmptyMessage { level });
            }

            // Shape: the message columns and the lanes split the level's input.
            let dim = lv.log_msg_cols + lv.log_num_interleaved;
            if dim != dim_in {
                return Err(DerivationError::LevelDimension {
                    level,
                    dim,
                    expected: dim_in,
                });
            }

            // Folding `k` variables moves the domain's log from `dim_in + rate_i` to `dim_in - k + rate_{i+1}`.
            // That difference is pinned to the initial reduction after L0, and to one bit at every later transition.
            if let Some(next) = self.levels.get(level + 1) {
                let domain_reduction = if level == 0 {
                    RS_DOMAIN_INITIAL_REDUCTION_FACTOR
                } else {
                    RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR
                };
                let expected_next_rate = lv
                    .log_inv_rate
                    .checked_add(lv.k)
                    .and_then(|r| r.checked_sub(domain_reduction))
                    .ok_or(LadderError::FoldBelowReduction {
                        level,
                        fold: lv.k,
                        reduction: domain_reduction,
                    })?;
                if next.log_inv_rate != expected_next_rate {
                    return Err(DerivationError::RateLadder {
                        level: level + 1,
                        log_inv_rate: next.log_inv_rate,
                        expected: expected_next_rate,
                    });
                }
            }

            // eta within the Johnson range for this level's (reduced) rate.
            let max_eta = 1.0 - reduced_rate(lv.code()).sqrt();
            if !lv.eta.is_finite() || lv.eta <= 0.0 || lv.eta >= max_eta {
                return Err(DerivationError::EtaOutOfRange {
                    level,
                    eta: lv.eta,
                    max: max_eta,
                });
            }

            // OOD samples: every level past L0 needs explicit samples.
            // L0 is only list binding, a union that every earlier challenge pays.
            //
            // The query counts past L0 assume single-codeword binding.
            if (level == 0) != (lv.ood_samples == 0) {
                return Err(DerivationError::OodSamples {
                    level,
                    samples: lv.ood_samples,
                });
            }

            // OOD row: the binding clears the target.
            let ood_pred = lv.paper_predicted_ood_bits();
            if ood_pred + 1e-12 < lv.target_security_bits as f64 {
                return Err(DerivationError::OodSoundness {
                    level,
                    bits: ood_pred,
                    target: lv.target_security_bits,
                });
            }

            let (pg_pred, q_pred) = lv.paper_predicted_bits();

            // Query row: the queries cover what grinding leaves.
            if lv.target_security_bits > lv.grinding_bits
                && q_pred + 1e-12 < (lv.target_security_bits - lv.grinding_bits) as f64
            {
                return Err(DerivationError::QuerySoundness {
                    level,
                    bits: q_pred,
                    target: lv.target_security_bits - lv.grinding_bits,
                });
            }

            // Fold row, MCA part: its bad event lives on the fold challenges.
            // The query grinding does not help it and there is no fold grinding, so it reaches the target alone.
            if pg_pred + 1e-12 < lv.target_security_bits as f64 {
                return Err(DerivationError::ProximityGap {
                    level,
                    bits: pg_pred,
                    target: lv.target_security_bits,
                });
            }

            // Batch row and the fold row's `2 L / |F|`: the largest list-unioned identity test is not grindable.
            // It is the ring switch's batching map at L0, and the claim batch past it.
            let algebraic = johnson_algebraic_bits(level, lv, prev_queries_at(&self.levels, level));
            if algebraic + 1e-12 < lv.target_security_bits as f64 {
                return Err(DerivationError::AlgebraicSoundness {
                    level,
                    bits: algebraic,
                    target: lv.target_security_bits,
                });
            }

            // No level may aim lower than the whole configuration.
            if lv.target_security_bits < self.target_security_bits {
                return Err(DerivationError::LevelTarget {
                    level,
                    bits: lv.target_security_bits,
                    global: self.target_security_bits,
                });
            }

            // The next level receives what this level's folds leave.
            dim_in -= lv.k;
        }

        // The last level leaves exactly the residual.
        if dim_in != yr_log_n {
            return Err(DerivationError::ResidualMismatch { dim: dim_in, yr_log_n });
        }

        // Round-by-round soundness (`thm:rbr`): the loop checked each verifier-challenge transition against the target.
        // The Fiat-Shamir error per random-oracle query is their maximum.
        //
        // Ordinary interactive soundness may additionally union-bound over the transitions.
        Ok(())
    }

    /// Derive the production security config at witness size `m` for an
    /// explicit L0 rate `2^-log_inv_rate`: Johnson list decoding with OOD
    /// binding and [`SECURITY_BITS`] bits per round under **round-by-round
    /// soundness**, i.e. every verifier-challenge error term (pg + fold
    /// grinding, query + query grinding, OOD, and algebraic checks) clears the
    /// target individually.
    ///
    /// L0's code is padded by `padding` coefficients past each lane's power of two, a hiding commitment's; every deeper level commits an unpadded fold.
    fn derive_config_with_log_inv_rate(m: usize, log_inv_rate: usize, padding: usize) -> Result<Self, DerivationError> {
        validate_log_inv_rate(log_inv_rate)?;
        let target_bits = SECURITY_BITS;
        let query_grind: usize = QUERY_GRINDING_BITS;
        // Pack the bits into 64-bit words.
        let log_n = m
            .checked_sub(F64::DEGREE.ilog2() as usize)
            .ok_or(DerivationError::WitnessBelowPacking { m })?;
        let initial_k = INITIAL_FOLDING_FACTOR;

        // The ladder's geometry does not depend on the slack.
        // The per-level search below checks the exact block-length feasibility, and picks the slack and queries.
        let shape = derive_ladder_shape(log_n, initial_k, log_inv_rate)?;
        let n_levels = shape.log_inv_rates.len();

        // Why no union-bound margin over the whole transcript: the target is 128-bit RBR soundness.
        // That is what the Fiat-Shamir analysis requires, not 128-bit interactive soundness over summed transitions.
        let mut levels = Vec::with_capacity(n_levels);
        let mut cols = log_n;
        for i in 0..n_levels {
            let rate = shape.log_inv_rates[i];
            // Each level's lanes are the variables it folds, so its message keeps the rest.
            let ilv = shape.k_levels[i];
            cols -= ilv;
            // The claims this level batches come from the previous level's queries.
            let prev_queries = prev_queries_at(&levels, i);
            let code = Code {
                padding: if i == 0 { padding } else { 0 },
                ..Code::plain(rate, cols)
            };
            let optimized = optimize_johnson_level(i, code, ilv, target_bits, query_grind, prev_queries)?;

            levels.push(WhirLevelConfig {
                log_inv_rate: rate,
                log_msg_cols: cols,
                padding: code.padding,
                log_num_interleaved: ilv,
                k: shape.k_levels[i],
                eta: optimized.eta,
                queries: optimized.queries,
                grinding_bits: query_grind,
                ood_samples: optimized.ood_samples,
                target_security_bits: target_bits,
            });
        }

        // What the last level's folds leave is the residual sent in the clear.
        let cfg = Self {
            m,
            log_n,
            initial_k,
            target_security_bits: target_bits,
            levels,
            final_block: FinalBlockConfig { yr_log_n: cols },
        };
        cfg.validate()?;
        Ok(cfg)
    }

    /// The configuration prover and verifier share: the level shape and counts, without the analysis fields.
    ///
    /// # Errors
    ///
    /// Fails when the configuration does not validate.
    fn to_config(&self) -> Result<Config, DerivationError> {
        self.validate()?;
        Ok(Config::new(
            self.initial_k,
            self.levels.iter().skip(1).map(|lv| lv.k).collect(),
            self.levels.iter().map(|lv| lv.log_inv_rate).collect(),
            self.levels.iter().map(|lv| lv.queries).collect(),
            self.levels.iter().map(|lv| lv.grinding_bits).collect(),
            self.levels.iter().map(|lv| lv.ood_samples).collect(),
            self.levels[0].padding,
        ))
    }
}

#[test]
fn johnson_bound_uses_theorem_parameter_and_reduced_rate() {
    // BCHKS25 Thm 4.6 (list correlated agreement) uses
    // m = ceil(sqrt(rho) / eta). The factor-two-smaller ceil(sqrt(rho) / (2 eta))
    // belongs to the plain, non-list Thm 1.5; Flock's Thm 8 quotes Thm 4.6
    // with that non-list parameter, which would overstate eps_pg by ~5 bits.
    assert_eq!(johnson_m_param(Code::plain(1, 16), 0.02), 36.0);

    // A message of dimension 16 has maximum degree 15, so the theorem's
    // reduced rate at block length 512 is 15/512, not the nominal 1/32.
    assert_eq!(reduced_rate(Code::plain(5, 4)), 15.0 / 512.0);
}

#[test]
fn production_profile_is_128_bit_johnson_with_query_grinding() {
    // Fixture state: every configured rate, at witness sizes 2^22 to 2^28 words.
    let mut min_pg_bits = f64::INFINITY;
    for log_inv_rate in MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE {
        for m in 22 + F64::DEGREE.ilog2() as usize..=28 + F64::DEGREE.ilog2() as usize {
            let cfg = WhirSecurityConfig::derive_config_with_log_inv_rate(m, log_inv_rate, 0).unwrap();
            assert_eq!(cfg.target_security_bits, 128);
            assert_eq!(cfg.levels[0].log_inv_rate, log_inv_rate);
            assert_eq!(cfg.levels[0].ood_samples, 0);
            for (i, level) in cfg.levels.iter().enumerate() {
                let (pg_bits, query_bits) = level.paper_predicted_bits();
                let ood_bits = level.paper_predicted_ood_bits();
                let algebraic_bits = johnson_algebraic_bits(i, level, prev_queries_at(&cfg.levels, i));
                min_pg_bits = min_pg_bits.min(pg_bits);
                // Invariant: every `thm:rbr` term clears 128 bits, the queries with their grinding.
                assert_eq!(level.grinding_bits, QUERY_GRINDING_BITS);
                assert!(query_bits + level.grinding_bits as f64 >= 128.0);
                assert!(pg_bits >= 128.0);
                assert!(ood_bits >= 128.0);
                assert!(algebraic_bits >= 128.0);
                // Invariant: one OOD sample suffices past L0.
                if i > 0 {
                    assert_eq!(level.ood_samples, 1);
                }
            }
        }
    }
    // Invariant: the slack search spends the proximity gap down to less than one bit above the target.
    assert!(
        (128.0..129.0).contains(&min_pg_bits),
        "eta search should use, but not exceed, the one-bit PG margin: {min_pg_bits}"
    );
}

#[test]
fn l0_list_bits_bound_every_l0_list() {
    // Every configured size and rate, hiding or not: its L0 list, which every challenge before the opening is unioned over.
    // The padded code has the larger rate, and the list bound its own slack.
    let plain = (MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE)
        .flat_map(|log_inv_rate| (MIN_LOG_N..=MAX_LOG_N).map(move |log_n| (log_inv_rate, log_n, false)));
    let hiding = (MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE)
        .flat_map(|log_inv_rate| (MIN_LOG_N_HIDING..=MAX_LOG_N).map(move |log_n| (log_inv_rate, log_n, true)));
    let largest = plain
        .chain(hiding)
        .map(|(log_inv_rate, log_n, hides)| {
            let cfg = if hides {
                derive_hiding_security(log_n, log_inv_rate)
            } else {
                WhirSecurityConfig::derive_config_with_log_inv_rate(
                    log_n + F64::DEGREE.ilog2() as usize,
                    log_inv_rate,
                    0,
                )
            };
            let cfg = cfg.unwrap_or_else(|e| panic!("rate 2^-{log_inv_rate}, log_n {log_n}, hiding {hides}: {e}"));
            let l0 = &cfg.levels[0];
            johnson_interleaved_list_log2(l0.code(), l0.eta)
        })
        .fold(f64::NEG_INFINITY, f64::max);

    // Invariant: the constant is the largest list's bits rounded up, so it bounds every list and wastes no bit.
    assert_eq!(
        largest.ceil() as usize,
        L0_LIST_BITS,
        "L0_LIST_BITS must be {}",
        largest.ceil()
    );
}

/// A query table's rows as `config.rs` writes them, from size `2^min_log_n`, with `queries(log_inv_rate, log_n)` in each entry.
fn table_rows(min_log_n: usize, queries: impl Fn(usize, usize) -> Vec<usize>) -> String {
    let mut rows = String::new();
    // One block per rate, one line per size, in the source's own formatting.
    for log_inv_rate in MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE {
        writeln!(rows, "    // Rate 2^-{log_inv_rate}.\n    [").unwrap();
        for log_n in min_log_n..=MAX_LOG_N {
            let row: Vec<String> = queries(log_inv_rate, log_n).iter().map(usize::to_string).collect();
            writeln!(rows, "        &[{}],", row.join(", ")).unwrap();
        }
        writeln!(rows, "    ],").unwrap();
    }
    rows
}

#[test]
fn the_table_is_the_derivation() {
    // Invariant: every table entry is what the derivation gives, field by field.
    // The table also serves no size or rate outside the configured window.
    let derived = |log_inv_rate: usize, log_n: usize| {
        derive_config(log_n, log_inv_rate).unwrap_or_else(|e| panic!("rate 2^-{log_inv_rate}, log_n {log_n}: {e}"))
    };
    let rows = table_rows(MIN_LOG_N, |log_inv_rate, log_n| {
        derived(log_inv_rate, log_n).queries().to_vec()
    });
    let tabulated = table_rows(MIN_LOG_N, |log_inv_rate, log_n| {
        WHIR_QUERIES[log_inv_rate - MIN_LOG_INV_RATE][log_n - MIN_LOG_N].to_vec()
    });
    assert!(
        tabulated == rows,
        "WHIR_QUERIES is stale, replace its rows in crates/pcs/src/whir/config/mod.rs with:\n{rows}"
    );
    // Fixture state: one rate past each end of the window, and sizes from 0 to 8 past the largest.
    for log_inv_rate in MIN_LOG_INV_RATE - 1..=MAX_LOG_INV_RATE + 1 {
        for log_n in 0..=MAX_LOG_N + 8 {
            let tabulated = config_for_rate(log_n, log_inv_rate);
            // The rate is checked before the size, so an out-of-range rate wins.
            if !(MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE).contains(&log_inv_rate) {
                assert_eq!(tabulated, Err(ConfigError::RateOutOfRange { log_inv_rate }));
            } else if !(MIN_LOG_N..=MAX_LOG_N).contains(&log_n) {
                assert_eq!(tabulated, Err(ConfigError::SizeOutOfRange { log_n }));
            } else {
                // Inside the window the whole configuration, not only the queries, is the derived one.
                assert_eq!(
                    tabulated,
                    Ok(derived(log_inv_rate, log_n)),
                    "rate 2^-{log_inv_rate}, log_n {log_n}"
                );
            }
        }
    }
}

/// The hiding table is the derivation with L0's code padded at its fixed point `k = q_0 + 2`, and the configuration pads by that `k`.
/// A stale table fails with the rows to paste over it.
#[test]
fn the_hiding_table_is_the_derivation() {
    let derived = |log_inv_rate: usize, log_n: usize| {
        derive_hiding_config(log_n, log_inv_rate)
            .unwrap_or_else(|e| panic!("hiding, rate 2^-{log_inv_rate}, log_n {log_n}: {e}"))
    };
    let configs: Vec<Vec<Config>> = (MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE)
        .map(|log_inv_rate| {
            (MIN_LOG_N_HIDING..=MAX_LOG_N)
                .map(|log_n| derived(log_inv_rate, log_n))
                .collect()
        })
        .collect();
    let at = |log_inv_rate: usize, log_n: usize| &configs[log_inv_rate - MIN_LOG_INV_RATE][log_n - MIN_LOG_N_HIDING];
    let rows = table_rows(MIN_LOG_N_HIDING, |log_inv_rate, log_n| {
        at(log_inv_rate, log_n).queries().to_vec()
    });
    let tabulated = table_rows(MIN_LOG_N_HIDING, |log_inv_rate, log_n| {
        WHIR_QUERIES_HIDING[log_inv_rate - MIN_LOG_INV_RATE][log_n - MIN_LOG_N_HIDING].to_vec()
    });
    assert!(
        tabulated == rows,
        "WHIR_QUERIES_HIDING is stale, replace its rows in crates/pcs/src/whir/config.rs with:\n{rows}"
    );
    for log_inv_rate in MIN_LOG_INV_RATE - 1..=MAX_LOG_INV_RATE + 1 {
        for log_n in 0..=MAX_LOG_N + 8 {
            let tabulated = config_for_rate_hiding(log_n, log_inv_rate);
            if !(MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE).contains(&log_inv_rate) {
                assert_eq!(tabulated, Err(ConfigError::RateOutOfRange { log_inv_rate }));
            } else if !(MIN_LOG_N_HIDING..=MAX_LOG_N).contains(&log_n) {
                assert_eq!(tabulated, Err(ConfigError::HidingSizeOutOfRange { log_n }));
            } else {
                let derived = at(log_inv_rate, log_n);
                assert_eq!(
                    derived.padding(),
                    derived.queries()[0] + 2,
                    "the padding is at its fixed point"
                );
                assert_eq!(
                    tabulated.as_ref(),
                    Ok(derived),
                    "hiding, rate 2^-{log_inv_rate}, log_n {log_n}"
                );
            }
        }
    }
}

/// `K` dimensions a hiding opening reveals after the lane fold, three per `E` scalar: the running claim `a`, the round messages, the out-of-domain answers, level 0's folded query values, every later level's opened rows, and the residual.
fn revealed_dimensions(log_n: usize, config: &Config) -> usize {
    let (queries, ks) = (config.queries(), config.level_ks());
    let residual = log_n - config.initial_k() - ks.iter().sum::<usize>();
    // `a`, then the message of the round after the lane fold.
    let mut scalars = 1 + 2;
    // Each committed level's out-of-domain answers, each with its intro message.
    scalars += 3 * config.ood_samples()[1..].iter().sum::<usize>();
    // Level 0's folded query values and their intro message.
    scalars += queries[0] + 2;
    // Each later level: its fold rounds, its opened rows (a fold's worth of elements each) and their intro message.
    for (i, &k) in ks.iter().enumerate() {
        scalars += 2 * k + (queries[i + 1] << k) + 2;
    }
    // The residual, and the closing rounds but the last, which the residual answers.
    scalars += (1 << residual) + 2 * residual.saturating_sub(1);
    3 * scalars
}

/// One random lane of `2^m` uniform words masks every functional the opening reveals after the lane fold only while they span at most half its dimensions (VEIL's Lemma 4.7, adapted), which is what bounds the hiding opening below at `2^MIN_LOG_N_HIDING` words.
#[test]
fn a_hiding_opening_reveals_at_most_half_a_lane() {
    for log_inv_rate in MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE {
        for log_n in MIN_LOG_N_HIDING..=MAX_LOG_N {
            let config = config_for_rate_hiding(log_n, log_inv_rate).unwrap();
            let lane = 1usize << (log_n - config.initial_k());
            let revealed = revealed_dimensions(log_n, &config);
            assert!(
                2 * revealed <= lane,
                "rate 2^-{log_inv_rate}, log_n {log_n}: {revealed} dimensions revealed, lane of {lane}"
            );
        }
    }
    // Below the hiding floor the same opening would reveal more than half a lane.
    let config = config_for_rate(MIN_LOG_N_HIDING - 1, MIN_LOG_INV_RATE).unwrap();
    assert!(2 * revealed_dimensions(MIN_LOG_N_HIDING - 1, &config) > 1 << (MIN_LOG_N_HIDING - 1 - config.initial_k()));
}
