// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// CREDIT: https://github.com/bcc-research/bolt-rs, MIT.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Ported from bolt-rs (https://github.com/bcc-research/bolt-rs,
// `whir_recursive.rs`).

//! Configuration and round-by-round soundness analysis of the affine-combiner WHIR opening.
//!
//! The fold is the equal-degree affine combiner `G + (alpha + beta X)(F + theta G)` of [CYWZ26, preprint], and its
//! mutual correlated agreement is the finite bound of their Lemma 4.1 (`affine_mca`). Per verifier message, with
//! `q = |E|` and `ell` a Johnson list at the threshold the message is analysed at:
//!
//! - `theta` of a fold round: `ell / q`, after [`FOLD_GRINDING_BITS`];
//! - `(gamma, alpha, beta)` of a fold round: `eps_aff + 2 ell / q`, after [`FOLD_GRINDING_BITS`];
//! - batching `lambda` entering a level: `(J - 1) ell / q`, after [`BATCH_GRINDING_BITS`];
//! - OOD points entering a later level: [`OOD_SAMPLES`] independent points, `C(ell, 2) (mu / q)^2`, with no grind;
//! - the level-0 OOD sample after the commitment (`crate::ood`): one point, `C(ell, 2) mu / q` with `mu = log_n`, after
//!   [`OOD_GRINDING_BITS`];
//! - queries: `((A_end - 1) / n)^t`, after [`QUERY_GRINDING_BITS`];
//! - tail sumcheck rounds: `2 / q`, after the grind of a degree-2 round (`fiat_shamir::grinding_bits(2)`).
//!
//! Round-by-round soundness means every entry individually clears [`SECURITY_BITS`]: the Fiat-Shamir error per
//! random-oracle query is the maximum of the entries, not their sum. Every entry but the queries' is compared with
//! its budget exactly, as an integer count of `1 / q` (of `1 / q^2` for the OOD points).

mod affine_mca;

/// Round-by-round soundness target (bits): every verifier message's error, after its grind, is at most
/// `2^-SECURITY_BITS` (`fiat_shamir::SECURITY_BITS`).
pub const SECURITY_BITS: usize = fiat_shamir::SECURITY_BITS as usize;

/// L0 code rate index: `rho_0 = 2^-LOG_INV_RATE_0` (rate 1/2).
pub const LOG_INV_RATE_0: usize = 1;

/// CLI-selectable L0 rates are `2^-r` for `r = 1, 2, 3, 4`.
pub const MIN_LOG_INV_RATE: usize = 1;
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

/// Per-level query-phase proof-of-work budget. These bits are ground after the
/// level commitment and before its query positions are sampled, so the query
/// count only needs to close the remaining `SECURITY_BITS - 17` bits.
pub const QUERY_GRINDING_BITS: u32 = 17;

/// Grinding before each fold round's `theta` and before its `(gamma, alpha, beta)`: the least for which the fold
/// rounds never cost a query.
pub const FOLD_GRINDING_BITS: u32 = 9;

/// Grinding before each level's batching challenge `lambda` and the stacked opening's outer batching challenge: the
/// least for which the batching terms never cost a query.
pub const BATCH_GRINDING_BITS: u32 = 14;

/// Grinding before the level-0 OOD sample: the least for which its term never costs a query.
pub const OOD_GRINDING_BITS: u32 = 15;

/// Out-of-domain points after each commitment past level 0, drawn as one verifier message: two independent points
/// square the OOD term, which then needs no grind.
pub const OOD_SAMPLES: usize = 2;

pub const INITIAL_FOLDING_FACTOR: usize = 6;
pub const SUBSEQUENT_FOLDING_FACTOR: usize = 4;

/// Logarithmic reduction of the total Reed--Solomon domain after the initial
/// fold. With the production six-variable initial fold, `3` changes the
/// inverse-rate logarithm by `6 - 3 = 3` at the first recursive level.
pub const RS_DOMAIN_INITIAL_REDUCTION_FACTOR: usize = 3;

/// After each subsequent fold, shrink the total Reed--Solomon domain by one
/// bit. This mirrors WHIR's recursive-domain schedule; unlike the initial
/// reduction, it is deliberately fixed rather than a tuning parameter.
const RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR: usize = 1;

const _: () = assert!(RS_DOMAIN_INITIAL_REDUCTION_FACTOR <= INITIAL_FOLDING_FACTOR);
const _: () = assert!(RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR <= SUBSEQUENT_FOLDING_FACTOR);

/// Folding stops once at most this many variables remain: the residual
/// polynomial (`yr`, at most `2^RESIDUAL_MAX_LOG` coefficients) is sent in
/// clear instead of committed and folded further.
pub const RESIDUAL_MAX_LOG: usize = 5;

// The recursion guest rotates the terminal point left by the lane fold to index it
// by witness coordinate, and the residual segment is what the last lane challenges
// rotate past, so the residual may never be longer than that fold
// (`rec_aggregation`'s placeholder emitter re-checks this per derived candidate).
const _: () = assert!(RESIDUAL_MAX_LOG <= INITIAL_FOLDING_FACTOR);

/// Shape plus per-level soundness parameters for one WHIR opening. Prover
/// and verifier read exactly the same numbers.
#[derive(Clone, Debug)]
pub struct ProverConfig {
    pub log_inv_rates: Vec<usize>,
    pub level_steps: usize,
    pub initial_k: usize,
    pub(crate) level_ks: Vec<usize>,
    /// Per-level query counts (L0, L1, ..., L_r). Length = level_steps + 1.
    /// [`WhirSecurityConfig::derive_config_with_log_inv_rate`] fills these
    /// from the per-level soundness analysis.
    pub queries: Vec<usize>,
    /// Per-level **query-phase** PoW grinding bits (L0, L1, ..., L_r), ground
    /// post-commit/pre-queries. Length = level_steps + 1. Each bit here
    /// substitutes for ~1/log₂(1/(1−γ)) queries at that level.
    pub grinding_bits: Vec<u32>,
    /// Per-commit-level out-of-domain points (L0, ..., L_r), drawn together right
    /// after the level's Merkle root and high part enter the transcript. `[0]` must be 0:
    /// L0's OOD sample is the caller's, right after its root (`crate::ood`).
    /// Length = level_steps + 1.
    pub ood_samples: Vec<usize>,
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
    /// Log message columns entering each level's fold (`log_n - initial_k`,
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

/// Soundness (in bits) the query phase must close on its own at every level
/// (the "100 bits from queries always" policy).
#[cfg(test)]
const UDR_TARGET_BITS: f64 = 100.0;

/// Number of queries for 100-bit soundness in the **unique-decoding regime**
/// at rate `2^(-log_inv_rate)`: `γ = δ/2 = (1−ρ)/2`, per-query soundness
/// `log₂(1/(1−γ))` (see [`udr_per_query_bits`]). Within the unique decoding
/// radius the prover is pinned to a single codeword, so there is no list and
/// no union-bound term: queries close the full target by themselves.
/// Per-query soundness saturates below 1 bit (`γ < 1/2`), so slimmer codes
/// approach `UDR_TARGET_BITS` queries from above.
#[cfg(test)]
pub fn udr_queries(log_inv_rate: usize) -> usize {
    assert!(log_inv_rate > 0, "log_inv_rate=0 (rate 1) has no soundness");
    let per_q = udr_per_query_bits_asymptotic(log_inv_rate);
    (UDR_TARGET_BITS / per_q).ceil() as usize
}

/// Per-query bits at the unique-decoding radius `(1 - rho) / 2`.
#[cfg(test)]
fn udr_per_query_bits_asymptotic(log_inv_rate: usize) -> f64 {
    let rho = (-(log_inv_rate as f64)).exp2();
    let gamma = (1.0 - rho) / 2.0;
    (1.0 / (1.0 - gamma)).log2()
}

/// Build an ad-hoc WHIR config from the raw PCS shape, WITHOUT the
/// per-level soundness derivation of
/// [`WhirSecurityConfig::derive_config_with_log_inv_rate`].
/// `log_n` is the packed-witness log size (= `m - LOG_PACKING`).
///
/// Strategy: the production ladder's folds ([`SUBSEQUENT_FOLDING_FACTOR`]) with
/// **decreasing rate** (the smallest step down that fits each level's queries)
/// until the residual is at most [`RESIDUAL_MAX_LOG`], asserting
/// `block_len ≥ udr_queries(rate)` at every level. Returns `Err` when no
/// feasible config exists (e.g. `log_n` too small for the chosen rate).
///
/// Test-support only: the small F64 PCS tests exercise sizes below the
/// production derivation's feasibility floor, where they fall back to this
/// shape. Production callers use the audited, per-level-sound path.
#[cfg(test)]
pub fn default_config(log_n: usize, log_batch_size: usize, log_inv_rate: usize) -> Result<ProverConfig, String> {
    let initial_k = log_batch_size;
    if log_n > initial_k && (1usize << (log_n - initial_k + log_inv_rate)) < udr_queries(log_inv_rate) {
        return Err("L0 block_len < udr_queries: log_n too small for chosen rate".into());
    }
    // Smallest rate strictly above the previous one that still fits the level's
    // query count inside its block length.
    let shape = derive_ladder(log_n, initial_k, log_inv_rate, |rate_running, _fold, cols_next| {
        let mut next_rate = rate_running + 1;
        while (1usize << (cols_next + next_rate)) < udr_queries(next_rate) {
            next_rate += 1;
            if next_rate > 20 {
                return Err("could not find feasible recursive rate (level too deep)".into());
            }
        }
        Ok(next_rate)
    })?;

    let n_levels = shape.log_inv_rates.len();
    Ok(ProverConfig {
        queries: shape.log_inv_rates.iter().map(|&r| udr_queries(r)).collect(),
        log_inv_rates: shape.log_inv_rates,
        level_steps: shape.k_levels.len() - 1,
        initial_k,
        level_ks: shape.k_levels[1..].to_vec(),
        grinding_bits: vec![0; n_levels],
        ood_samples: vec![0usize; n_levels],
    })
}

/// Shared config for a `2^log_n`-word witness, preferring the production profile at [`LOG_INV_RATE_0`] and falling back to [`default_config`] below its feasibility floor.
#[cfg(test)]
pub(crate) fn test_config_for(log_n: usize) -> ProverConfig {
    if let Ok(config) = crate::whir::config_for_rate(log_n, LOG_INV_RATE_0) {
        return config;
    }
    for log_batch_size in (1..=5).rev() {
        for log_inv_rate in 1..=4 {
            if let Ok(config) = default_config(log_n, log_batch_size, log_inv_rate) {
                return config;
            }
        }
    }
    panic!("no feasible whir config at log_n = {log_n}");
}

/// Level-ladder shape: per-level dims (index 0 = L0) plus the residual.
struct LadderShape {
    log_inv_rates: Vec<usize>,
    log_msg_cols: Vec<usize>,
    k_levels: Vec<usize>,
    yr_log_n: usize,
}

/// Descend the level ladder, folding [`SUBSEQUENT_FOLDING_FACTOR`] variables per
/// level until at most [`RESIDUAL_MAX_LOG`] remain. `next_rate` picks each new
/// level's inverse-rate logarithm from `(previous rate, fold just taken, message
/// dimension the new level carries)`, which is the only thing that separates the
/// production ladder from the test-support one.
fn derive_ladder(
    log_n: usize,
    initial_k: usize,
    log_inv_rate: usize,
    mut next_rate: impl FnMut(usize, usize, usize) -> Result<usize, String>,
) -> Result<LadderShape, String> {
    if log_n <= initial_k {
        return Err("log_n must be > initial_k".into());
    }
    let mut shape = LadderShape {
        log_inv_rates: vec![log_inv_rate],
        log_msg_cols: vec![log_n - initial_k],
        k_levels: vec![initial_k],
        yr_log_n: 0,
    };
    let mut n_running = log_n - initial_k;
    let mut rate_running = log_inv_rate;
    let mut fold_running = initial_k;
    while n_running > RESIDUAL_MAX_LOG {
        let k = SUBSEQUENT_FOLDING_FACTOR.min(n_running);
        let log_msg_cols_next = n_running - k;
        let rate = next_rate(rate_running, fold_running, log_msg_cols_next)?;
        shape.log_inv_rates.push(rate);
        shape.log_msg_cols.push(log_msg_cols_next);
        shape.k_levels.push(k);
        n_running -= k;
        rate_running = rate;
        fold_running = k;
    }
    if shape.k_levels.len() < 2 {
        return Err("log_n too small: needs at least 2 fold levels".into());
    }
    shape.yr_log_n = n_running;
    Ok(shape)
}

/// Production ladder: the total RS domain loses
/// [`RS_DOMAIN_INITIAL_REDUCTION_FACTOR`] bits after the initial fold, then
/// exactly one bit per subsequent fold, so a fold of `k` variables raises the
/// inverse-rate logarithm by `k - reduction`.
fn derive_ladder_shape(log_n: usize, initial_k: usize, log_inv_rate: usize) -> Result<LadderShape, String> {
    let mut domain_reduction = RS_DOMAIN_INITIAL_REDUCTION_FACTOR;
    derive_ladder(log_n, initial_k, log_inv_rate, |rate_running, fold_running, _cols| {
        let rate_increase = fold_running.checked_sub(domain_reduction).ok_or_else(|| {
            format!("folding factor {fold_running} is smaller than RS domain reduction {domain_reduction}")
        })?;
        domain_reduction = RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR;
        Ok(rate_running + rate_increase)
    })
}

// ===================================================================
// Security analysis
// ===================================================================
//
// Per level: block length `n`, honest lane degree `d_0 = 2^log_msg_cols - 1`, `k` fold rounds. Round `j = 1..=k` is
// analysed against degree `d_j = d_0 + j` at threshold `A_j = A_end - (k - j)` (one coordinate of agreement lost per
// round), and the level starts at `A_0 = A_end - k`. `A_end` is the integer the search picks per level, the smallest
// that clears every term below, which minimises the queries `((A_end - 1) / n)^t`. `ell(A, d)` is the Johnson list of
// Lemma 3.11 [CYWZ26, preprint] (`affine_mca::johnson_list(n, A, d)`).

/// `log2 |E|` for the soundness analysis.
pub const ANALYSIS_LOG_Q: f64 = LOG_Q_BITS as f64;
const LOG_Q_BITS: usize = 128;

/// Upper bound on the claims the stacked opening batches (the ring-switched claim and the committed columns'
/// point claims), `J_0` of the outer batching term.
pub const MAX_STACKED_CLAIMS: usize = 1 << 9;

/// The grinding before each verifier message the analysis covers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Grinding {
    pub fold: usize,
    pub batch: usize,
    /// Before the level-0 OOD sample; later levels' OOD points take none.
    pub ood: usize,
    pub query: usize,
}

const PRODUCTION_GRINDING: Grinding = Grinding {
    fold: FOLD_GRINDING_BITS as usize,
    batch: BATCH_GRINDING_BITS as usize,
    ood: OOD_GRINDING_BITS as usize,
    query: QUERY_GRINDING_BITS as usize,
};

/// The grind of each tail sumcheck round, of degree two.
const TAIL_GRINDING_BITS: usize = fiat_shamir::grinding_bits(2) as usize;

/// One level of the ladder and the parameters its analysis was derived under.
#[derive(Clone, Debug)]
pub struct WhirLevelConfig {
    /// Code rate `2^-log_inv_rate`.
    pub log_inv_rate: usize,
    /// Log of the coefficients per lane; `log_msg_cols + log_inv_rate = log2(n)`.
    pub log_msg_cols: usize,
    /// Fold rounds at this level, the log of the lanes per Merkle leaf.
    pub k: usize,
    /// The agreement threshold `A_end` at the level's last fold round.
    pub(crate) agreement: u128,
    /// Lemma 4.1's witness for each fold round `j = 1..=k`.
    pub(crate) rounds: Vec<affine_mca::AffineWitness>,
    /// Query count `t`, with `((A_end - 1) / n)^t <= 2^-(target - query grind)`.
    pub queries: usize,
}

impl WhirLevelConfig {
    fn block_len(&self) -> u128 {
        1 << (self.log_msg_cols + self.log_inv_rate)
    }

    fn honest_degree(&self) -> u128 {
        (1 << self.log_msg_cols) - 1
    }

    /// Slack above the Johnson radius at the level's last round, `A_end / n - sqrt(d_k / n)`.
    pub fn eta(&self) -> f64 {
        let n = self.block_len() as f64;
        self.agreement as f64 / n - ((self.honest_degree() + self.k as u128) as f64 / n).sqrt()
    }

    /// `ell(A_0, d_0)`, the list the level's batching and OOD terms union over.
    pub fn list_bound(&self) -> Option<u128> {
        let start = self.agreement.checked_sub(self.k as u128)?;
        affine_mca::johnson_list(self.block_len(), start, self.honest_degree())
    }
}

/// The final residual sent in the clear at the end of the last level.
#[derive(Clone, Debug)]
pub struct FinalBlockConfig {
    /// Variables of the tail sumcheck on the final lane's low part.
    pub yr_log_n: usize,
}

/// Complete security spec for one WHIR opening of a `log_n`-variable witness.
#[derive(Clone, Debug)]
pub struct WhirSecurityConfig {
    /// `log_n + LOG_PACKING`.
    pub m: usize,
    pub log_n: usize,
    /// L0's lane fold, the `log_batch_size` the L0 commitment used.
    pub initial_k: usize,
    /// Round-by-round target: every error term clears it after its grinding.
    pub(crate) target_security_bits: usize,
    pub(crate) grinding: Grinding,
    pub levels: Vec<WhirLevelConfig>,
    pub final_block: FinalBlockConfig,
}

/// The largest count `c` with `c / q <= 2^-(target - grind)`.
fn budget(grind: usize, target: usize) -> u128 {
    let bits = LOG_Q_BITS.saturating_sub(target.saturating_sub(grind));
    if bits >= 128 { u128::MAX } else { 1 << bits }
}

/// Fails unless the error `count / q^2` is at most `2^-target`, exactly; `None` is a count past `u128`.
fn require_count_squared(count: Option<u128>, target: usize, what: impl FnOnce() -> String) -> Result<(), String> {
    let bits = (2 * LOG_Q_BITS).saturating_sub(target);
    match count {
        Some(count) if bits >= 128 || count <= 1 << bits => Ok(()),
        _ => Err(format!("{}: {count:?} / q^2 > 2^{bits} / q^2", what())),
    }
}

/// Fails unless the error `count / q` is at most `2^-(target - grind)`, exactly; `None` is a count past `u128`.
fn require_count(
    count: Option<u128>,
    grind: usize,
    target: usize,
    what: impl FnOnce() -> String,
) -> Result<(), String> {
    let budget = budget(grind, target);
    match count {
        Some(count) if count <= budget => Ok(()),
        _ => Err(format!("{}: {count:?} / q > {budget} / q", what())),
    }
}

/// Where a level sits in the opening, for the terms that depend on it.
#[derive(Clone, Copy)]
enum Position {
    /// L0: the outer batching over the stacked claims and the ring-switch map; the caller's OOD sample.
    First,
    /// A later level, batching the previous level's `queries` claims, the OOD claims and the running claim.
    After { prev_queries: usize },
}

/// The terms that depend only on `ell(A_0, d_0)`: batching (`(J - 1) ell / q`), then OOD. Past L0 the OOD term is
/// [`OOD_SAMPLES`] independent points' (`C(ell, 2) (mu / q)^2`, Lemma lem:ood per point). At L0 it is the
/// commitment's OOD sample's (`crate::ood`, `C(ell, 2) mu / q`): its point has `mu` coordinates, and after it every
/// outer challenge faces a single list member.
fn check_list_terms(
    n: u128,
    d0: u128,
    a0: u128,
    mu: usize,
    position: Position,
    g: &Grinding,
    target: usize,
) -> Result<(), String> {
    let ell = affine_mca::johnson_list(n, a0, d0).ok_or("level-start threshold below the Johnson radius")?;
    let degree = match position {
        Position::First => MAX_STACKED_CLAIMS - 1 + crate::ring_switch::RING_SWITCH_ERROR_NUMERATOR,
        Position::After { prev_queries } => prev_queries + OOD_SAMPLES,
    };
    require_count((degree as u128).checked_mul(ell), g.batch, target, || {
        format!("batching (degree {degree}, list {ell})")
    })?;
    let pairs = ell.checked_mul(ell.saturating_sub(1)).map(|p| p / 2);
    let mu = mu as u128;
    match position {
        Position::First => require_count(pairs.and_then(|p| p.checked_mul(mu)), g.ood, target, || {
            format!("level-0 OOD (list {ell}, {mu} variables)")
        }),
        Position::After { .. } => {
            const _: () = assert!(OOD_SAMPLES == 2, "the OOD term is checked for two points");
            require_count_squared(pairs.and_then(|p| p.checked_mul(mu * mu)), target, || {
                format!("OOD (list {ell}, {mu} variables)")
            })
        }
    }
}

/// The fold round errors for round `j` against its witness.
fn check_fold_round(
    n: u128,
    d: u128,
    a: u128,
    w: &affine_mca::AffineWitness,
    g: &Grinding,
    target: usize,
) -> Result<(), String> {
    let ell = affine_mca::johnson_list(n, a - 1, d).ok_or("theta threshold below the Johnson radius")?;
    require_count(Some(ell), g.fold, target, || "theta".into())?;
    match affine_mca::combiner_within(n, d, a, w, budget(g.fold, target)) {
        Some(true) => Ok(()),
        Some(false) => Err("(gamma, alpha, beta) over its budget".into()),
        None => Err("the fold round's witness does not hold".into()),
    }
}

/// A witness for every fold round of a level ending at `a_end`, when every round clears the target.
fn fold_witnesses(
    n: u128,
    d0: u128,
    k: usize,
    a_end: u128,
    g: &Grinding,
    target: usize,
) -> Option<Vec<affine_mca::AffineWitness>> {
    let mut rounds = Vec::with_capacity(k);
    for j in 1..=k as u128 {
        let (d, a) = (d0 + j, a_end.checked_sub(k as u128 - j)?);
        // The cheap `theta` term first: it already rules out thresholds below the Johnson radius.
        let ell = affine_mca::johnson_list(n, a - 1, d)?;
        require_count(Some(ell), g.fold, target, String::new).ok()?;
        let (w, _) = affine_mca::find_witness(n, d, a)?;
        check_fold_round(n, d, a, &w, g, target).ok()?;
        rounds.push(w);
    }
    Some(rounds)
}

/// Queries closing `target - grind` bits when a query passes with probability `(a_end - 1) / n`: a word whose
/// candidate's encoding left the list agrees with it on at most `a_end - 1` positions.
fn query_count(n: u128, a_end: u128, grind: usize, target: usize) -> usize {
    let per_query = -((a_end - 1) as f64 / n as f64).log2();
    let bits = target.saturating_sub(grind) as f64;
    let mut queries = (bits / per_query).ceil() as usize;
    while (queries as f64) * per_query < bits {
        queries += 1;
    }
    queries
}

/// The smallest `A_end` (hence the fewest queries) for which every term of the level clears the target.
fn search_level(
    log_msg_cols: usize,
    log_inv_rate: usize,
    k: usize,
    position: Position,
    g: &Grinding,
    target: usize,
) -> Result<(u128, Vec<affine_mca::AffineWitness>), String> {
    let n: u128 = 1 << (log_msg_cols + log_inv_rate);
    let d0: u128 = (1 << log_msg_cols) - 1;
    let mu = log_msg_cols + k;
    let feasible = |a_end: u128| {
        check_list_terms(n, d0, a_end - k as u128, mu, position, g, target).ok()?;
        fold_witnesses(n, d0, k, a_end, g, target)
    };
    let (mut lo, mut hi) = ((n * (d0 + k as u128)).isqrt() + 1, n);
    if feasible(hi).is_none() {
        return Err(format!(
            "no threshold clears {target} bits at n = 2^{}",
            log_msg_cols + log_inv_rate
        ));
    }
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if feasible(mid).is_some() {
            hi = mid
        } else {
            lo = mid + 1
        }
    }
    Ok((hi, feasible(hi).expect("the bisection ends on a feasible threshold")))
}

impl WhirSecurityConfig {
    /// Check the shape, then every error term from the stored thresholds and witnesses.
    pub fn validate(&self) -> Result<(), String> {
        if self.log_n + crate::LOG_PACKING != self.m {
            return Err(format!(
                "log_n ({}) + LOG_PACKING ({}) != m ({})",
                self.log_n,
                crate::LOG_PACKING,
                self.m
            ));
        }
        let l0 = self.levels.first().ok_or_else(|| "empty levels".to_string())?;
        if l0.k != self.initial_k {
            return Err(format!("L0 must fold initial_k ({}) lanes", self.initial_k));
        }
        let target = self.target_security_bits;
        let g = &self.grinding;
        let mut dim_in = self.log_n;
        for (i, lv) in self.levels.iter().enumerate() {
            let at = |what: String| format!("L{i}: {what}");
            if lv.log_inv_rate == 0 || lv.log_msg_cols == 0 {
                return Err(at("rate-one code or empty lanes".into()));
            }
            if lv.log_msg_cols + lv.k != dim_in {
                return Err(at(format!("shape does not consume the input dimension {dim_in}")));
            }
            if let Some(next) = self.levels.get(i + 1) {
                let reduction = if i == 0 {
                    RS_DOMAIN_INITIAL_REDUCTION_FACTOR
                } else {
                    RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR
                };
                if Some(next.log_inv_rate) != (lv.log_inv_rate + lv.k).checked_sub(reduction) {
                    return Err(at(format!(
                        "next rate does not reduce the RS domain by {reduction} bit(s)"
                    )));
                }
            }
            let (n, d0, k) = (lv.block_len(), lv.honest_degree(), lv.k as u128);
            if lv.rounds.len() != lv.k || lv.agreement > n || lv.agreement <= k {
                return Err(at("malformed thresholds".into()));
            }
            let position = if i == 0 {
                Position::First
            } else {
                Position::After {
                    prev_queries: self.levels[i - 1].queries,
                }
            };
            check_list_terms(n, d0, lv.agreement - k, dim_in, position, g, target).map_err(at)?;
            for (j, w) in (1..=k).zip(&lv.rounds) {
                check_fold_round(n, d0 + j, lv.agreement - (k - j), w, g, target)
                    .map_err(|e| at(format!("round {j}: {e}")))?;
            }
            let queries_log2 = lv.queries as f64 * ((lv.agreement - 1) as f64 / n as f64).log2();
            if queries_log2 > -(target.saturating_sub(g.query) as f64) {
                return Err(at(format!("queries: 2^{queries_log2:.2}")));
            }
            if lv.queries as u128 > n {
                return Err(at("more queries than positions".into()));
            }
            dim_in -= lv.k;
        }
        if dim_in != self.final_block.yr_log_n {
            return Err(format!(
                "levels leave {dim_in} variables, not yr_log_n ({})",
                self.final_block.yr_log_n
            ));
        }
        // Each tail sumcheck round: a degree-2 polynomial, then its grind.
        require_count(Some(2), TAIL_GRINDING_BITS, target, || "tail round".into())
    }

    /// Derive the production config at witness size `m` and L0 rate `2^-log_inv_rate`: every round-by-round error
    /// term clears [`SECURITY_BITS`] after its grinding, with the fewest queries per level.
    pub fn derive_config_with_log_inv_rate(m: usize, log_inv_rate: usize) -> Result<Self, String> {
        Self::derive_with(m, log_inv_rate, PRODUCTION_GRINDING)
    }

    pub(crate) fn derive_with(m: usize, log_inv_rate: usize, grinding: Grinding) -> Result<Self, String> {
        validate_log_inv_rate(log_inv_rate)?;
        let target = SECURITY_BITS;
        let log_n = m
            .checked_sub(crate::LOG_PACKING)
            .ok_or_else(|| format!("m ({m}) < LOG_PACKING ({})", crate::LOG_PACKING))?;
        let initial_k = INITIAL_FOLDING_FACTOR;
        let shape = derive_ladder_shape(log_n, initial_k, log_inv_rate)?;
        let mut levels: Vec<WhirLevelConfig> = Vec::with_capacity(shape.log_inv_rates.len());
        for i in 0..shape.log_inv_rates.len() {
            let (rate, cols, k) = (shape.log_inv_rates[i], shape.log_msg_cols[i], shape.k_levels[i]);
            let position = match levels.last() {
                None => Position::First,
                Some(prev) => Position::After {
                    prev_queries: prev.queries,
                },
            };
            let (agreement, rounds) =
                search_level(cols, rate, k, position, &grinding, target).map_err(|e| format!("L{i}: {e}"))?;
            levels.push(WhirLevelConfig {
                log_inv_rate: rate,
                log_msg_cols: cols,
                k,
                agreement,
                rounds,
                queries: query_count(1 << (cols + rate), agreement, grinding.query, target),
            });
        }
        let cfg = Self {
            m,
            log_n,
            initial_k,
            target_security_bits: target,
            grinding,
            levels,
            final_block: FinalBlockConfig {
                yr_log_n: shape.yr_log_n,
            },
        };
        cfg.validate()?;
        Ok(cfg)
    }

    /// The shared prover/verifier config: the level shape, queries, grinding and OOD samples. Only a config at the
    /// production target and grinding, which the prover and the verifiers hardcode.
    pub fn to_config(&self) -> Result<ProverConfig, String> {
        self.validate()?;
        if self.grinding != PRODUCTION_GRINDING || self.target_security_bits != SECURITY_BITS {
            return Err("the target or grinding differs from the production constants".into());
        }
        Ok(ProverConfig {
            log_inv_rates: self.levels.iter().map(|lv| lv.log_inv_rate).collect(),
            level_steps: self.levels.len() - 1,
            initial_k: self.initial_k,
            level_ks: self.levels.iter().skip(1).map(|lv| lv.k).collect(),
            queries: self.levels.iter().map(|lv| lv.queries).collect(),
            grinding_bits: vec![QUERY_GRINDING_BITS; self.levels.len()],
            ood_samples: (0..self.levels.len())
                .map(|i| if i == 0 { 0 } else { OOD_SAMPLES })
                .collect(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::pretty_integer;

    const STACKED_LOGS: std::ops::RangeInclusive<usize> = 15..=28;

    /// Every admitted shape's query counts, `None` where no threshold clears the target.
    fn queries_with(grinding: Grinding) -> Vec<Option<Vec<usize>>> {
        let mut table = vec![];
        for rate in MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE {
            for log_n in STACKED_LOGS {
                let cfg = WhirSecurityConfig::derive_with(log_n + crate::LOG_PACKING, rate, grinding).ok();
                table.push(cfg.map(|cfg| cfg.levels.iter().map(|lv| lv.queries).collect()));
            }
        }
        table
    }

    /// Every admitted shape derives and validates, at the target, with the production grinding.
    #[test]
    fn every_admitted_shape_validates() {
        for rate in MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE {
            for log_n in STACKED_LOGS {
                let cfg =
                    WhirSecurityConfig::derive_config_with_log_inv_rate(log_n + crate::LOG_PACKING, rate).unwrap();
                assert_eq!(cfg.target_security_bits, SECURITY_BITS);
                assert_eq!(cfg.levels[0].log_inv_rate, rate);
                cfg.to_config().unwrap();
            }
        }
    }

    /// The fold, batching and OOD grinding are the least that leave every query count where unlimited grinding would.
    #[test]
    fn fold_batch_and_ood_grinding_are_the_least_that_cost_no_queries() {
        let unlimited = Grinding {
            fold: SECURITY_BITS,
            batch: SECURITY_BITS,
            ood: SECURITY_BITS,
            ..PRODUCTION_GRINDING
        };
        let best = queries_with(unlimited);
        assert_eq!(queries_with(PRODUCTION_GRINDING), best);
        for less in [
            Grinding {
                batch: PRODUCTION_GRINDING.batch - 1,
                ..PRODUCTION_GRINDING
            },
            Grinding {
                ood: PRODUCTION_GRINDING.ood - 1,
                ..PRODUCTION_GRINDING
            },
            Grinding {
                fold: PRODUCTION_GRINDING.fold - 1,
                ..PRODUCTION_GRINDING
            },
        ] {
            assert_ne!(queries_with(less), best, "{less:?} costs no queries either");
        }
    }

    /// The prover and the verifiers hardcode the grinding, so a config derived with other grinding is no config.
    #[test]
    fn to_config_rejects_other_grinding() {
        let more = Grinding {
            query: PRODUCTION_GRINDING.query + 1,
            ..PRODUCTION_GRINDING
        };
        let cfg = WhirSecurityConfig::derive_with(20 + crate::LOG_PACKING, 1, more).unwrap();
        assert!(cfg.to_config().is_err());
    }

    /// A tampered threshold or witness fails validation.
    #[test]
    fn validation_rejects_a_lowered_threshold() {
        let cfg = WhirSecurityConfig::derive_config_with_log_inv_rate(20 + crate::LOG_PACKING, 1).unwrap();
        for i in 0..cfg.levels.len() {
            let mut lowered = cfg.clone();
            lowered.levels[i].agreement -= 1;
            assert!(lowered.validate().is_err(), "L{i}");
            let mut fewer = cfg.clone();
            fewer.levels[i].queries -= 1;
            assert!(fewer.validate().is_err(), "L{i}");
        }
    }

    /// Parameter-report helper:
    /// `WHIR_LOG_INV_RATE=2 WHIR_NUM_VARS=22 cargo test --release -p pcs print_whir_query_counts -- --ignored --nocapture`
    #[test]
    #[ignore = "manual parameter report; configure it through environment variables"]
    fn print_whir_query_counts() {
        let env_usize = |name: &str| {
            std::env::var(name)
                .unwrap_or_else(|_| panic!("missing {name}"))
                .parse::<usize>()
                .unwrap_or_else(|_| panic!("{name} must be a non-negative integer"))
        };
        let log_inv_rate = env_usize("WHIR_LOG_INV_RATE");
        let num_vars = env_usize("WHIR_NUM_VARS");
        let start = std::time::Instant::now();
        let cfg =
            WhirSecurityConfig::derive_config_with_log_inv_rate(num_vars + crate::LOG_PACKING, log_inv_rate).unwrap();
        let elapsed = start.elapsed();
        println!(
            "num_vars={}, rate=1/{}, derived in {elapsed:?}",
            pretty_integer(num_vars),
            pretty_integer(1usize << log_inv_rate)
        );
        for (level, lv) in cfg.levels.iter().enumerate() {
            println!(
                "L{level}: rate=1/{}, queries={}, eta={:.3e}, list={}, m={:?}",
                pretty_integer(1usize << lv.log_inv_rate),
                lv.queries,
                lv.eta(),
                lv.list_bound().unwrap(),
                lv.rounds.iter().map(|w| w.m).collect::<Vec<_>>(),
            );
        }
    }
}
