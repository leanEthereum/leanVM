// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// CREDIT: https://github.com/bcc-research/bolt-rs, MIT.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Ported from bolt-rs (https://github.com/bcc-research/bolt-rs,
// `whir_recursive.rs`).

//! Field-independent configuration and soundness analysis for WHIR.
//!
//! Source of truth: `doc/leanvm/body/b-polynomial-commitment-scheme.tex`, annex B of
//! the spec ("The polynomial commitment scheme"), Theorem `thm:rbr`. Its
//! per-verifier-message error table maps onto the per-level checks in
//! [`WhirSecurityConfig::validate`]:
//!
//! - batching challenges -> `johnson_algebraic_bits` (one challenge per level,
//!   powers of it over the level's claim list, as in the doc),
//! - fold challenge `s_j` -> `2 L/|F| + 2^(l-j) eps`: the MCA part via
//!   `paper_johnson_log_a` (worst round `j = 1`), the `2 L/|F|` part
//!   under `johnson_algebraic_bits`,
//! - OOD challenge -> `paper_ood_bits`,
//! - query message -> `(1 - gamma)^t`, plus [`QUERY_GRINDING_BITS`].
//!
//! Round-by-round (RBR) soundness means every entry individually clears
//! [`SECURITY_BITS`]: the Fiat--Shamir error per random-oracle query is the
//! MAX of the entries, not their sum.

// ===================================================================
// Config
// ===================================================================

// The production WHIR configuration: rate-1/2 Johnson list decoding with
// OOD binding and 128-bit round-by-round soundness over F192.

/// Round-by-round soundness target (bits): every verifier-challenge transition
/// must have conditional failure probability at most `2^-SECURITY_BITS`.
pub const SECURITY_BITS: usize = 128;

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
pub const QUERY_GRINDING_BITS: usize = 17;

/// Maximum BCHKS25 integer parameter considered by the per-level eta search.
/// Production configurations hit the proximity-gap boundary far below this;
/// the generous cap makes the optimizer deterministic even if sizes expand.
const JOHNSON_ETA_SEARCH_MAX_M: usize = 4096;

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
/// and verifier read exactly the same numbers, hence the single struct and the
/// [`VerifierConfig`] alias.
#[derive(Clone, Debug)]
pub struct ProverConfig {
    pub log_inv_rates: Vec<usize>,
    pub level_steps: usize,
    pub initial_k: usize,
    pub level_ks: Vec<usize>,
    /// Per-level query counts (L0, L1, ..., L_r). Length = level_steps + 1.
    /// [`WhirSecurityConfig::derive_config_with_log_inv_rate`] fills these
    /// from the per-level soundness analysis.
    pub queries: Vec<usize>,
    /// Per-level **query-phase** PoW grinding bits (L0, L1, ..., L_r), ground
    /// post-commit/pre-queries. Length = level_steps + 1. Each bit here
    /// substitutes for ~1/log₂(1/(1−γ)) queries at that level.
    pub grinding_bits: Vec<usize>,
    /// Per-commit-level out-of-domain samples (L0, ..., L_r), taken right
    /// after the level's Merkle root enters the transcript. `[0]` must be 0:
    /// L0 is bound by the opening's own (post-commit, random-point)
    /// evaluation claim. Length = level_steps + 1.
    pub ood_samples: Vec<usize>,
}

pub type VerifierConfig = ProverConfig;

/// The per-level shape table a [`VerifierConfig`] implies for a
/// `log_n`-variable opening: the numbers every consumer of the multilevel
/// protocol (the verifier itself, recursion harnesses) otherwise re-derives.
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
/// bottom out near `UDR_TARGET_BITS` queries: 243 at rate 1/2, 148 at 1/4,
/// 121 at 1/8, 110 at 1/16, 105 at 1/32.
#[cfg(test)]
pub fn udr_queries(log_inv_rate: usize) -> usize {
    assert!(log_inv_rate > 0, "log_inv_rate=0 (rate 1) has no soundness");
    let per_q = udr_per_query_bits_asymptotic(log_inv_rate);
    (UDR_TARGET_BITS / per_q).ceil() as usize
}

/// Build an ad-hoc WHIR config from the raw PCS shape, WITHOUT the
/// per-level soundness derivation of
/// [`WhirSecurityConfig::derive_config_with_log_inv_rate`].
/// `log_n` is the packed-witness log size (= `m - LOG_PACKING`).
///
/// Strategy: 3-bit recursive folds (`k_i = 3`) with **decreasing rate** (one
/// rate step per level) until the residual is small (`≤ 5` bits), asserting
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
        grinding_bits: vec![0usize; n_levels],
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
    log_num_interleaved: Vec<usize>,
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
        log_num_interleaved: vec![initial_k],
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
        shape.log_num_interleaved.push(k);
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
// Security configuration schema
// ===================================================================
//
// Auditable, per-level spec for a WHIR instance: query count, grinding
// bits, slack-from-Johnson, and the proximity-gap analysis the parameters were
// derived under.
//
// That analysis is always the Johnson radius with explicit slack `eta`
// (gamma = (1 - sqrt(rho)) - eta) WITH out-of-domain binding (`doc/leanvm/body/b-polynomial-commitment-scheme.tex`,
// Thm `thm:rbr`). The MCA theorem (`thm:mca-johnson` = BCHKS25 Thm 4.6) gives
// the proximity-gap exceptional set `a = O_rho(n / eta^5)`, and the eta search
// keeps `log2(q/a)` above the target on its own rather than grinding the fold
// challenges for it. Binding to a
// single codeword of the (Johnson-bounded) interleaved list is via
// `ood_samples` explicit multilinear OOD evaluations, except at L0, where the
// opening's own post-commit random evaluation claim plays the OOD role (union
// over the list, `L*mu/q`), so `ood_samples = 0`. Plain Johnson without OOD
// binding would be unsound at these parameters: the query phase would pay a
// union bound over the interleaved list (19 to 52 bits here) that the query
// counts do not include.
//
// Grinding always lands after the level's Merkle root is observed and before
// its query positions are sampled, the standard FRI/STARK placement.

/// Parameters for a single level in the multilevel WHIR ladder.
/// L0 = the upstream `pcs::commit` output (reused, not re-committed);
/// L1 .. L_{r−1} are the level commits; the final residual `yr` block
/// is described separately in [`FinalBlockConfig`].
#[derive(Clone, Debug)]
pub struct WhirLevelConfig {
    /// PCS rate at this level: codeword expansion factor = 2^log_inv_rate.
    pub log_inv_rate: usize,
    /// Message dimension at this level (log of the number of field columns in
    /// the codeword). `log_msg_cols + log_inv_rate = log_2(block_len)`.
    pub log_msg_cols: usize,
    /// Log of lane width per Merkle leaf at this level. For L0 = `initial_k`;
    /// for L_i (i ≥ 1) = the previous level's `k`.
    pub log_num_interleaved: usize,
    /// Number of sumcheck folds taken at this level. For L0 = `initial_k`
    /// (the lane fold); for L_i (i ≥ 1) = the level fold k_{i−1}.
    pub k: usize,
    /// Slack from the Johnson radius: γ = (1 − √ρ) − η.
    pub eta: f64,
    /// Number of codeword position queries opened at this level (the FRI
    /// query phase). Bounds the per-query soundness term `(1−γ)^Q`.
    pub queries: usize,
    /// **Query-phase** PoW grinding bits, ground post-commit/pre-queries.
    /// Each bit substitutes for ~1/log₂(1/(1−γ)) queries at this level.
    pub grinding_bits: usize,
    /// Out-of-domain samples taken right after this level's commit enters
    /// the transcript. Each binds the prover to a single codeword of the
    /// interleaved list via a multilinear evaluation claim.
    /// Must be 0 at L0 (bound by the opening's own post-commit evaluation
    /// claim) and ≥ 1 at deeper levels.
    pub ood_samples: usize,
    /// Security target this level guarantees, post-grinding.
    pub target_security_bits: usize,
}

/// Descriptor for the final-residual block (`yr`) sent in the clear at the
/// end of the last fold level. It has no commit and no queries, so the
/// only meaningful parameter is its dimension.
#[derive(Clone, Debug)]
pub struct FinalBlockConfig {
    /// `log_2(|yr|)`: number of extension-field values sent in the clear. The
    /// last fold level's sumcheck stops at this dim instead of folding to 1.
    pub yr_log_n: usize,
}

/// Complete security spec for one WHIR instance, covering a single
/// `(hash, m)` pair.
///
/// **Validation invariants** (checked by [`Self::validate`]):
/// 1. `initial_k + Σ levels[1..].k + final_block.yr_log_n == log_n`.
/// 2. Each level's proximity-gap bits reach `target_security_bits`.
/// 3. Each level's query soundness reaches `target_security_bits −
///    grinding_bits` (queries cover what grinding doesn't).
/// 4. `eta` is finite and inside the Johnson range for the level's rate.
/// 5. `log_msg_cols`, `log_num_interleaved`, `k` match the
///    level-shape constraint (each level's input dim equals the
///    previous level's `log_msg_cols`).
#[derive(Clone, Debug)]
pub struct WhirSecurityConfig {
    /// Block-encoder log size: m = log₂(witness bit count).
    pub m: usize,
    /// Committed-witness log dimension.
    pub log_n: usize,
    /// L0 lane fold. Must equal the upstream `PcsParams::log_batch_size` so
    /// the L0 commit can be reused without re-committing.
    pub initial_k: usize,
    /// Round-by-round security target (bits): `validate()` asserts that every
    /// error term associated with a verifier challenge clears at least this
    /// much. This is an RBR target, not a claim that the sum of all interactive
    /// failure probabilities is bounded by `2^-target_security_bits`.
    pub target_security_bits: usize,
    /// Identifier of the proximity-gap analysis used. Self-documents which
    /// theorem the per-level parameters were derived from. Example:
    /// `"ben_sasson_2025_thm_4_6"`.
    pub analysis_version: String,
    /// Per-level parameters, in order L0, L1, L2, ....
    pub levels: Vec<WhirLevelConfig>,
    /// Final residual block descriptor.
    pub final_block: FinalBlockConfig,
}

/// Extension-field size used for soundness analysis: `q = 2^192`.
const ANALYSIS_LOG_Q: f64 = 192.0;

/// BCHKS25 parameter `rho = k/n` for an RS code of dimension `k + 1`.
/// Our message has `2^log_msg_cols` coefficients (degree strictly below that
/// value), so `k = 2^log_msg_cols - 1`. This differs perceptibly from the
/// nominal code rate at the small recursive levels.
fn reduced_rate(log_inv_rate: usize, log_msg_cols: usize) -> f64 {
    let dimension = (log_msg_cols as f64).exp2();
    (dimension - 1.0) / ((log_msg_cols + log_inv_rate) as f64).exp2()
}

/// Proximity-gap exceptional set for the list-decoding (Johnson) regime, per
/// `doc/leanvm/body/b-polynomial-commitment-scheme.tex` Thm `thm:mca-johnson` = BCHKS25 Theorem 4.6 (list
/// correlated agreement). For a Reed-Solomon code of (slightly reduced) rate
/// `ρ`, codeword length `n`, and Johnson slack `η` (proximity radius
/// `γ = 1 − √ρ − η`), the MCA error is `a/|F|` with
///
///   `a = [2(m+½)^5 + 3(m+½)·γ·ρ] / (3·ρ^{3/2}) · n + (m+½)/√ρ`,
///
/// where `η = 1 − √ρ − γ` and `m = max(⌈√ρ/η⌉, 3)`. Returns `log₂ a`.
///
/// This is the per-fold-step MCA error, stated for a two-row interleaved word
/// (`C ∈ F^{2×n}`). The ℓ-round lane fold of a `2^ℓ`-interleaved word adds a
/// row-union factor via the PCS annex, Lemma `lem:fold-list`; see
/// [`paper_johnson_log_a`].
fn paper_thm_ca_johnson_log_a(log_inv_rate: usize, eta: f64, log_msg_cols: usize) -> f64 {
    let rho = reduced_rate(log_inv_rate, log_msg_cols);
    let sqrt_rho = rho.sqrt();
    let gamma = 1.0 - sqrt_rho - eta;
    // BCHKS25 Thm 4.6: m = ⌈√ρ/(1−√ρ−γ)⌉ = ⌈√ρ/η⌉, floored at 3.
    let m_param = johnson_m_param(log_inv_rate, log_msg_cols, eta);
    let half = m_param + 0.5;
    let half5 = half.powi(5);
    let numerator = 2.0 * half5 + 3.0 * half * gamma * rho;
    let denominator = 3.0 * rho.powf(1.5);
    let n = ((log_msg_cols + log_inv_rate) as f64).exp2();
    let a = (numerator / denominator) * n + half / sqrt_rho;
    a.log2()
}

/// Integer parameter `m = max(⌈√ρ/η⌉, 3)` of BCHKS25 Thm 4.6 (list
/// correlated agreement), represented as `f64` for the bound. Beware: the
/// plain, non-list Thm 1.5 has the factor-two-smaller `⌈√ρ/(2η)⌉`, and
/// Flock's Thm 8 quotes Thm 4.6 with that non-list parameter; the list form
/// costs a factor 2 of slack (see the footnote in the PCS annex
/// Thm `thm:mca-johnson`).
fn johnson_m_param(log_inv_rate: usize, log_msg_cols: usize, eta: f64) -> f64 {
    let sqrt_rho = reduced_rate(log_inv_rate, log_msg_cols).sqrt();
    ((sqrt_rho / eta).ceil() as usize).max(3) as f64
}

/// Johnson-regime proximity-gap `log₂ a` for a level, including the row-union
/// factor from the PCS annex, Lemma `lem:fold-list` ("Folding preserves lists").
///
/// The base MCA error `ε = a_RLC/|F|` from [`paper_thm_ca_johnson_log_a`] is
/// stated for a two-row interleaved word (one fold step). Folding a
/// `2^ℓ`-interleaved word (ℓ = `log_num_interleaved`) over its ℓ lane-fold
/// rounds pays a row union: `thm:rbr`'s fold row is `2L/|F| + 2^{ℓ-j}·ε` at
/// round `j`, so the worst round (`j = 1`) pays the factor `2^{ℓ-1}` =
/// (interleaving factor)/2 (the `2L/|F|` part is checked separately, under
/// [`johnson_algebraic_bits`]). We bind the per-level grinding to that worst
/// round, returning `log₂(2^{ℓ-1}·a_RLC) = log₂ a_RLC + (ℓ-1)`.
///
/// `ℓ ≤ 1` (`L ≤ 2`) means no row union; the `(ℓ-1)` penalty clamps to 0.
fn paper_johnson_log_a(log_inv_rate: usize, eta: f64, log_msg_cols: usize, log_num_interleaved: usize) -> f64 {
    let base = paper_thm_ca_johnson_log_a(log_inv_rate, eta, log_msg_cols);
    // Row-union factor 2^{ℓ-1} (worst round i=1 of the ℓ-round lane fold),
    // ℓ = log_num_interleaved. In bits: (ℓ-1), clamped ≥ 0.
    let row_union_penalty = (log_num_interleaved as f64 - 1.0).max(0.0);
    base + row_union_penalty
}

/// Per-query log₂(1/(1−γ)) under the Johnson regime: each query closes
/// `log_2(1/(1-γ))` bits of soundness against a γ-far adversary.
fn paper_per_query_bits(log_inv_rate: usize, log_msg_cols: usize, eta: f64) -> f64 {
    let rho = reduced_rate(log_inv_rate, log_msg_cols);
    let gamma = 1.0 - rho.sqrt() - eta;
    (1.0 / (1.0 - gamma)).log2()
}

/// Unique-decoding-regime per-query soundness at `γ = δ/2` (`δ = 1 − ρ`).
/// Test-support only, backing [`udr_queries`] and the ad-hoc
/// [`default_config`] shape used by small F64 PCS tests.
#[cfg(test)]
fn udr_per_query_bits_asymptotic(log_inv_rate: usize) -> f64 {
    let rho = (-(log_inv_rate as f64)).exp2();
    let gamma = (1.0 - rho) / 2.0;
    (1.0 / (1.0 - gamma)).log2()
}

/// Johnson-bound list size of the *interleaved* RS code at radius
/// `θ = 1 − √ρ − η`, in log₂. Independent of the interleaving factor.
///
/// Interleaving preserves relative distance (`V^{⊙m}` has the base code's
/// distance `δ = 1 − ρ`) and only enlarges the alphabet (to `q^m`). The
/// Johnson bound depends solely on (distance, radius, alphabet size), so the
/// interleaved list size at any radius *below* the Johnson radius `1 − √ρ`
/// is bounded by the very same single-code Johnson list size
///
///   `L_int ≤ L_base ≤ 1/(2·η·√ρ)`,
///
/// with no dependence on `m` and, crucially, no `L_base^r` blow-up.
///
/// The general GGR (Gopalan-Guruswami-Raghavendra, Thm 2.5) interleaved bound
/// `L_int ≤ C(b+r, r)·L_base^r` is only needed to push the list-decoding
/// radius *past* the Johnson bound toward `δ`. WHIR deliberately sits at
/// `θ = 1 − √ρ − η`, strictly below the Johnson radius by slack `η > 0`, so
/// that regime never applies and the plain Johnson bound is both correct and
/// far tighter (it dominates GGR throughout the regime RS can reach).
fn johnson_interleaved_list_log2(log_inv_rate: usize, log_msg_cols: usize, eta: f64) -> f64 {
    debug_assert!(eta > 0.0, "η must be > 0 to stay strictly below the Johnson radius");
    let rho = reduced_rate(log_inv_rate, log_msg_cols);
    let sqrt_rho = rho.sqrt();
    let l_base = 1.0 / (2.0 * eta * sqrt_rho);
    l_base.log2()
}

/// Worst algebraic verifier-challenge transition in the production opening:
/// `thm:rbr`'s batch row (`(J−1)·L/|F|` for the powers-of-lambda batching of
/// the PCS annex, Protocol 1 step 1) and the `2L/|F|` part of its fold row.
/// A degree-`d` identity test unioned over a Johnson list of size `L` fails
/// with probability at most `dL/|F|`. The relevant degrees are:
///
/// - the total degree of the GF64-to-GF192 ring-switch batching map (L0 only,
///   but included at every level so the bound also dominates the claim batch
///   entering the next level's list, whatever its query count);
/// - `J − 1 = prev_queries + ood_samples`, the batch polynomial's degree in the
///   level's single lambda. The claims it batches are the ones the PREVIOUS
///   level's query phase raised (`thm:rbr`: `J_i = n_{i-1} + 2`, one per query
///   plus the residual and the OOD claim), so this level's own query count is
///   the wrong quantity: query counts fall with depth, so using it would
///   understate the degree and overstate the bound. At L0 there is no previous
///   level and `J_0` is set by the outer protocol's claim pool rather than by a
///   query count, so 0 is passed; that pool is a few hundred claims, orders below
///   the ring-switch degree the `max` takes anyway; and
/// - 2 for quadratic sumcheck.
fn johnson_algebraic_bits_for(
    log_inv_rate: usize,
    log_msg_cols: usize,
    eta: f64,
    prev_queries: usize,
    ood_samples: usize,
) -> f64 {
    let log2_l = johnson_interleaved_list_log2(log_inv_rate, log_msg_cols, eta);
    let degree = crate::ring_switch::RING_SWITCH_SOUNDNESS_DEGREE
        .max(prev_queries + ood_samples)
        .max(2);
    ANALYSIS_LOG_Q - (degree as f64).log2() - log2_l
}

/// `prev_queries` is `levels[i-1].queries`, and 0 for `i = 0`.
fn johnson_algebraic_bits(level: &WhirLevelConfig, prev_queries: usize) -> f64 {
    johnson_algebraic_bits_for(
        level.log_inv_rate,
        level.log_msg_cols,
        level.eta,
        prev_queries,
        level.ood_samples,
    )
}

/// The query count the batch at `levels[i]` carries claims from.
fn prev_queries_at(levels: &[WhirLevelConfig], i: usize) -> usize {
    if i == 0 { 0 } else { levels[i - 1].queries }
}

/// OOD binding bits for a level. `mu_vars` is the level's multilinear
/// variable count (`log_msg_cols + log_num_interleaved`).
///
/// - `ood_samples ≥ 1` (explicit samples): the PCS annex, Lemma `lem:ood` /
///   `thm:rbr`'s OOD row `binom(L,2)·μ/|F|`, generalized to `s` samples: the
///   bad event is two distinct list elements agreeing on all `s` random
///   points of `F^μ` (Schwartz-Zippel, total degree ≤ μ), union over pairs:
///   `bits = s·(192 − log₂ μ) − (2·log₂ L_int − 1)`.
/// - `ood_samples = 0` (L0): the protocol takes no OOD sample at commitment,
///   so the PCS itself is only list binding (the PCS annex, opening paragraph). What this
///   term materializes is the OUTER protocol's binding: the opening's own
///   evaluation claim sits at a post-commit random point, so at most one
///   list member matches it except with `L·μ/|F|` (union over the list, not
///   pairs): `bits = 192 − log₂ L_int − log₂ μ`.
fn paper_ood_bits(log_inv_rate: usize, log_msg_cols: usize, eta: f64, mu_vars: usize, ood_samples: usize) -> f64 {
    let log2_l = johnson_interleaved_list_log2(log_inv_rate, log_msg_cols, eta);
    let log2_mu = (mu_vars as f64).log2();
    if ood_samples == 0 {
        ANALYSIS_LOG_Q - log2_l - log2_mu
    } else {
        ood_samples as f64 * (ANALYSIS_LOG_Q - log2_mu) - (2.0 * log2_l - 1.0)
    }
}

/// Result of the WHIR-style per-level Johnson-slack search. The search
/// minimizes queries; ties keep the smallest theorem parameter `m`, which has
/// the largest eta and therefore the smallest list bound.
struct OptimizedJohnsonLevel {
    eta: f64,
    queries: usize,
    ood_samples: usize,
}

/// Eta at the lower boundary for a fixed BCHKS25 theorem parameter
/// `m = ceil(sqrt(rho) / eta)`. Moving eta lower would increase `m` and worsen
/// the proximity-gap bound; this boundary maximizes query soundness for the
/// given `m`. Step upward by an ulp if floating-point division lands just
/// below the intended ceil boundary.
fn johnson_eta_for_m(log_inv_rate: usize, log_msg_cols: usize, m: usize) -> f64 {
    debug_assert!(m >= 3);
    let sqrt_rho = reduced_rate(log_inv_rate, log_msg_cols).sqrt();
    let mut eta = sqrt_rho / m as f64;
    while johnson_m_param(log_inv_rate, log_msg_cols, eta) > m as f64 {
        eta = f64::from_bits(eta.to_bits() + 1);
    }
    debug_assert_eq!(johnson_m_param(log_inv_rate, log_msg_cols, eta), m as f64);
    eta
}

/// Choose eta independently for one recursive level, following leanVM's
/// discrete `m` search but using this implementation's exact reduced rate and
/// corrected BCHKS25 parameter. Candidates must satisfy every non-grindable
/// 128-bit term and the proximity-gap target without fold grinding.
fn optimize_johnson_level(
    level: usize,
    log_inv_rate: usize,
    log_msg_cols: usize,
    log_num_interleaved: usize,
    target_bits: usize,
    query_grinding_bits: usize,
    prev_queries: usize,
) -> Result<OptimizedJohnsonLevel, String> {
    let target = target_bits as f64;
    let query_target = target_bits.saturating_sub(query_grinding_bits).max(1) as f64;
    let mu = log_msg_cols + log_num_interleaved;
    let block_len = 1usize << (log_msg_cols + log_inv_rate);
    let mut best: Option<OptimizedJohnsonLevel> = None;

    for m in 3..=JOHNSON_ETA_SEARCH_MAX_M {
        let eta = johnson_eta_for_m(log_inv_rate, log_msg_cols, m);
        let max_eta = 1.0 - reduced_rate(log_inv_rate, log_msg_cols).sqrt();
        if eta >= max_eta {
            continue;
        }

        let eps_pg = ANALYSIS_LOG_Q - paper_johnson_log_a(log_inv_rate, eta, log_msg_cols, log_num_interleaved);
        // At the theorem-parameter boundaries a grows monotonically with m;
        // no later candidate can recover once the proximity-gap target fails.
        if eps_pg + 1e-12 < target {
            break;
        }

        let per_q = paper_per_query_bits(log_inv_rate, log_msg_cols, eta);
        if !per_q.is_finite() || per_q <= 0.0 {
            continue;
        }
        let queries = (query_target / per_q).ceil() as usize;
        if queries > block_len {
            continue;
        }

        let ood_samples = if level == 0 {
            0
        } else {
            match (1..=8usize).find(|&s| paper_ood_bits(log_inv_rate, log_msg_cols, eta, mu, s) + 1e-12 >= target) {
                Some(samples) => samples,
                None => continue,
            }
        };
        let eps_ood = paper_ood_bits(log_inv_rate, log_msg_cols, eta, mu, ood_samples);
        if eps_ood + 1e-12 < target
            || johnson_algebraic_bits_for(log_inv_rate, log_msg_cols, eta, prev_queries, ood_samples) + 1e-12 < target
        {
            continue;
        }

        let candidate = OptimizedJohnsonLevel {
            eta,
            queries,
            ood_samples,
        };
        if best.as_ref().is_none_or(|current| candidate.queries < current.queries) {
            best = Some(candidate);
        }
    }

    best.ok_or_else(|| {
        format!(
            "L{level}: no eta candidate satisfies {target_bits}-bit Johnson/OOD soundness at rate 1/2^{log_inv_rate}"
        )
    })
}

impl WhirLevelConfig {
    /// Proximity-gap and per-query soundness bits this level delivers:
    ///   eps_pg_bits    = log₂(q/a) under the Johnson threshold-a formula
    ///   eps_query_bits = Q · log₂(1/(1−γ))
    fn paper_predicted_bits(&self) -> (f64, f64) {
        // Fold row of `thm:rbr`, MCA part: the ℓ-round fold of a
        // 2^ℓ-interleaved word (ℓ = log_num_interleaved) pays a row-union
        // factor 2^{ℓ-j} at round j (`lem:fold-list`); the worst round (j=1)
        // gives 2^{ℓ-1}, on top of the base Thm 4.6 MCA error.
        let log_a = paper_johnson_log_a(self.log_inv_rate, self.eta, self.log_msg_cols, self.log_num_interleaved);
        let eps_pg = ANALYSIS_LOG_Q - log_a;
        // Per-query soundness WITHOUT a list union bound: the OOD binding (see
        // `paper_ood_bits`) pins the prover to a single codeword of the
        // interleaved list before queries are drawn.
        let per_q = paper_per_query_bits(self.log_inv_rate, self.log_msg_cols, self.eta);
        let eps_query = self.queries as f64 * per_q;
        (eps_pg, eps_query)
    }

    /// OOD binding bits this level delivers. See `paper_ood_bits`.
    fn paper_predicted_ood_bits(&self) -> f64 {
        let mu = self.log_msg_cols + self.log_num_interleaved;
        paper_ood_bits(self.log_inv_rate, self.log_msg_cols, self.eta, mu, self.ood_samples)
    }
}

impl WhirSecurityConfig {
    /// Validate that the config is internally consistent and matches the
    /// declared analysis. Returns the first violation found, if any.
    pub fn validate(&self) -> Result<(), String> {
        if self.log_n + crate::LOG_PACKING != self.m {
            return Err(format!(
                "log_n ({}) + LOG_PACKING ({}) != m ({})",
                self.log_n,
                crate::LOG_PACKING,
                self.m
            ));
        }

        // Level shape: initial_k + Σ k (L1+) + yr_log_n = log_n.
        let levels_level_k_sum: usize = self.levels.iter().skip(1).map(|lv| lv.k).sum();
        let yr_log_n = self.final_block.yr_log_n;
        if self.initial_k + levels_level_k_sum + yr_log_n != self.log_n {
            return Err(format!(
                "shape mismatch: initial_k ({}) + Σ k ({}) + yr_log_n ({}) = {} ≠ log_n ({})",
                self.initial_k,
                levels_level_k_sum,
                yr_log_n,
                self.initial_k + levels_level_k_sum + yr_log_n,
                self.log_n,
            ));
        }

        // L0 must have k = initial_k and log_num_interleaved = initial_k.
        let l0 = self.levels.first().ok_or_else(|| "empty levels".to_string())?;
        if l0.k != self.initial_k {
            return Err(format!("L0.k ({}) must equal initial_k ({})", l0.k, self.initial_k));
        }
        if l0.log_num_interleaved != self.initial_k {
            return Err(format!(
                "L0.log_num_interleaved ({}) must equal initial_k ({})",
                l0.log_num_interleaved, self.initial_k
            ));
        }

        // Per-level checks.
        let mut dim_in = self.log_n;
        for (i, lv) in self.levels.iter().enumerate() {
            if lv.log_inv_rate == 0 {
                return Err(format!("L{i}: log_inv_rate=0 gives a rate-one code"));
            }
            if lv.log_msg_cols == 0 {
                return Err(format!("L{i}: log_msg_cols must be positive"));
            }

            // Shape: log_msg_cols + log_num_interleaved = dim_in.
            if lv.log_msg_cols + lv.log_num_interleaved != dim_in {
                return Err(format!(
                    "L{i}: log_msg_cols ({}) + log_num_interleaved ({}) ≠ input dim ({dim_in})",
                    lv.log_msg_cols, lv.log_num_interleaved
                ));
            }

            // Folding `lv.k` variables changes the next level's total RS
            // domain logarithm from `dim_in + rate_i` to
            // `dim_in - lv.k + rate_{i+1}`. Pin that difference to the public
            // initial reduction and to one bit at every later transition.
            if let Some(next) = self.levels.get(i + 1) {
                let domain_reduction = if i == 0 {
                    RS_DOMAIN_INITIAL_REDUCTION_FACTOR
                } else {
                    RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR
                };
                let expected_next_rate = lv
                    .log_inv_rate
                    .checked_add(lv.k)
                    .and_then(|r| r.checked_sub(domain_reduction))
                    .ok_or_else(|| format!("L{i}: invalid RS domain reduction {domain_reduction}"))?;
                if next.log_inv_rate != expected_next_rate {
                    return Err(format!(
                        "L{}: log_inv_rate ({}) does not reduce the preceding RS domain by {} bit(s); expected {}",
                        i + 1,
                        next.log_inv_rate,
                        domain_reduction,
                        expected_next_rate,
                    ));
                }
            }

            // eta within the Johnson range for this level's (reduced) rate.
            let max_eta = 1.0 - reduced_rate(lv.log_inv_rate, lv.log_msg_cols).sqrt();
            if !lv.eta.is_finite() || lv.eta <= 0.0 || lv.eta >= max_eta {
                return Err(format!(
                    "L{i}: Johnson eta must be finite and in (0, {max_eta}), got {}",
                    lv.eta
                ));
            }

            // OOD samples: every level past L0 needs explicit samples, while
            // L0 is bound by the opening's own post-commit evaluation claim.
            if i == 0 && lv.ood_samples != 0 {
                return Err(format!(
                    "L0: ood_samples={} but L0 is bound by the opening's \
                     own evaluation claim (must be 0)",
                    lv.ood_samples
                ));
            }
            if i > 0 && lv.ood_samples == 0 {
                return Err(format!(
                    "L{i}: ood_samples ≥ 1 required past L0 (the query \
                     counts assume single-codeword binding)"
                ));
            }

            // OOD binding clears the target.
            let ood_pred = lv.paper_predicted_ood_bits();
            if ood_pred + 1e-12 < lv.target_security_bits as f64 {
                return Err(format!(
                    "L{i}: OOD binding ({ood_pred:.2} bits) < target ({})",
                    lv.target_security_bits
                ));
            }

            let (pg_pred, q_pred) = lv.paper_predicted_bits();

            // Security: queries cover the gap left by grinding.
            if lv.target_security_bits > lv.grinding_bits
                && q_pred + 1e-12 < (lv.target_security_bits - lv.grinding_bits) as f64
            {
                return Err(format!(
                    "L{i}: query soundness ({q_pred:.2} bits) < target ({}) - grinding ({}) = {}",
                    lv.target_security_bits,
                    lv.grinding_bits,
                    lv.target_security_bits - lv.grinding_bits
                ));
            }

            // Per-application proximity gap + fold-challenge grinding must
            // reach target. (The pg bad event lives on the fold challenges,
            // so only the fold grind (done before each fold challenge)
            // boosts it; the query-phase grind does not.)
            if pg_pred + 1e-12 < lv.target_security_bits as f64 {
                return Err(format!(
                    "L{i}: proximity-gap soundness ({pg_pred:.2} bits) < target ({})",
                    lv.target_security_bits
                ));
            }

            // The largest list-unioned algebraic identity test (currently the
            // composed ring-switch batching map) is not grindable and must
            // clear the target.
            let algebraic = johnson_algebraic_bits(lv, prev_queries_at(&self.levels, i));
            if algebraic + 1e-12 < lv.target_security_bits as f64 {
                return Err(format!(
                    "L{i}: list-unioned algebraic soundness ({algebraic:.2} bits) < target ({})",
                    lv.target_security_bits
                ));
            }

            if lv.target_security_bits < self.target_security_bits {
                return Err(format!(
                    "L{i}: target_security_bits ({}) < global target ({})",
                    lv.target_security_bits, self.target_security_bits
                ));
            }

            // Advance dim_in for next level: subtract k (the folds at this level).
            dim_in -= lv.k;
        }

        if dim_in != yr_log_n {
            return Err(format!(
                "after consuming all levels, dim_in ({dim_in}) ≠ yr_log_n ({yr_log_n})"
            ));
        }

        // Round-by-round soundness (doc/leanvm/body/b-polynomial-commitment-scheme.tex, Thm `thm:rbr`): each
        // verifier-challenge transition is checked against
        // `target_security_bits` in the per-level loop above, so the
        // Fiat--Shamir error per random-oracle query is their MAX; ordinary
        // interactive soundness may additionally union-bound over transitions.
        Ok(())
    }

    /// Derive the production security config at witness size `m` for an
    /// explicit L0 rate `2^-log_inv_rate`: Johnson list decoding with OOD
    /// binding and [`SECURITY_BITS`] bits per round under **round-by-round
    /// soundness**, i.e. every verifier-challenge error term (pg + fold
    /// grinding, query + query grinding, OOD, and algebraic checks) clears the
    /// target individually.
    pub fn derive_config_with_log_inv_rate(m: usize, log_inv_rate: usize) -> Result<Self, String> {
        validate_log_inv_rate(log_inv_rate)?;
        let target_bits = SECURITY_BITS;
        let query_grind: usize = QUERY_GRINDING_BITS;
        let log_n = m
            .checked_sub(crate::LOG_PACKING)
            .ok_or_else(|| format!("m ({m}) < LOG_PACKING ({})", crate::LOG_PACKING))?;
        let initial_k = INITIAL_FOLDING_FACTOR;

        // The ladder geometry is independent of eta. Exact block-length
        // feasibility is checked below by the same per-level optimizer that
        // supplies the production eta and query count.
        let shape = derive_ladder_shape(log_n, initial_k, log_inv_rate)?;
        let n_levels = shape.log_inv_rates.len();

        // Round-by-round target: every verifier-challenge error term (pg,
        // query, OOD, and algebraic checks) must individually clear
        // `target_bits`. We do not add a whole-transcript union-bound margin:
        // this configuration targets 128-bit RBR soundness, as required by the
        // Fiat--Shamir analysis, rather than 128-bit interactive soundness after
        // summing every transition probability.
        let mut levels = Vec::with_capacity(n_levels);
        for i in 0..n_levels {
            let rate = shape.log_inv_rates[i];
            let cols = shape.log_msg_cols[i];
            let ilv = shape.log_num_interleaved[i];
            let prev_queries = prev_queries_at(&levels, i);
            let optimized = optimize_johnson_level(i, rate, cols, ilv, target_bits, query_grind, prev_queries)?;

            levels.push(WhirLevelConfig {
                log_inv_rate: rate,
                log_msg_cols: cols,
                log_num_interleaved: ilv,
                k: shape.k_levels[i],
                eta: optimized.eta,
                queries: optimized.queries,
                grinding_bits: query_grind,
                ood_samples: optimized.ood_samples,
                target_security_bits: target_bits,
            });
        }

        let analysis_version = "bchks25_thm_4_6_exact_reduced_rate_row_union_optimized_eta";
        let cfg = Self {
            m,
            log_n,
            initial_k,
            target_security_bits: target_bits,
            analysis_version: analysis_version.into(),
            levels,
            final_block: FinalBlockConfig {
                yr_log_n: shape.yr_log_n,
            },
        };
        cfg.validate()?;
        Ok(cfg)
    }

    /// Build the shared prover/verifier config, retaining the level shape and dropping security-analysis fields.
    pub fn to_config(&self) -> Result<ProverConfig, String> {
        self.validate()?;
        Ok(ProverConfig {
            log_inv_rates: self.levels.iter().map(|lv| lv.log_inv_rate).collect(),
            level_steps: self.levels.len() - 1,
            initial_k: self.initial_k,
            level_ks: self.levels.iter().skip(1).map(|lv| lv.k).collect(),
            queries: self.levels.iter().map(|lv| lv.queries).collect(),
            grinding_bits: self.levels.iter().map(|lv| lv.grinding_bits).collect(),
            ood_samples: self.levels.iter().map(|lv| lv.ood_samples).collect(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::pretty_integer;

    #[test]
    fn johnson_bound_uses_theorem_parameter_and_reduced_rate() {
        // BCHKS25 Thm 4.6 (list correlated agreement) uses
        // m = ceil(sqrt(rho) / eta). The factor-two-smaller ceil(sqrt(rho) / (2 eta))
        // belongs to the plain, non-list Thm 1.5; Flock's Thm 8 quotes Thm 4.6
        // with that non-list parameter, which would overstate eps_pg by ~5 bits.
        assert_eq!(johnson_m_param(1, 16, 0.02), 36.0);

        // A message of dimension 16 has maximum degree 15, so the theorem's
        // reduced rate at block length 512 is 15/512, not the nominal 1/32.
        assert_eq!(reduced_rate(5, 4), 15.0 / 512.0);
    }

    #[test]
    fn production_profile_is_128_bit_johnson_with_query_grinding() {
        let mut min_pg_bits = f64::INFINITY;
        for log_inv_rate in MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE {
            for m in 22 + crate::LOG_PACKING..=28 + crate::LOG_PACKING {
                let cfg = WhirSecurityConfig::derive_config_with_log_inv_rate(m, log_inv_rate).unwrap();
                assert_eq!(cfg.target_security_bits, 128);
                assert_eq!(cfg.levels[0].log_inv_rate, log_inv_rate);
                assert_eq!(cfg.levels[0].ood_samples, 0);
                for (i, level) in cfg.levels.iter().enumerate() {
                    let (pg_bits, query_bits) = level.paper_predicted_bits();
                    let ood_bits = level.paper_predicted_ood_bits();
                    let algebraic_bits = johnson_algebraic_bits(level, prev_queries_at(&cfg.levels, i));
                    min_pg_bits = min_pg_bits.min(pg_bits);
                    assert_eq!(level.grinding_bits, QUERY_GRINDING_BITS);
                    assert!(query_bits + level.grinding_bits as f64 >= 128.0);
                    assert!(pg_bits >= 128.0);
                    assert!(ood_bits >= 128.0);
                    assert!(algebraic_bits >= 128.0);
                    if i > 0 {
                        assert_eq!(level.ood_samples, 1);
                    }
                }
            }
        }
        assert!(
            (128.0..129.0).contains(&min_pg_bits),
            "eta search should use, but not exceed, the one-bit PG margin: {min_pg_bits}"
        );
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
        let cfg =
            WhirSecurityConfig::derive_config_with_log_inv_rate(num_vars + crate::LOG_PACKING, log_inv_rate).unwrap();

        println!(
            "num_vars={}, rate=1/{}",
            pretty_integer(num_vars),
            pretty_integer(1usize << log_inv_rate)
        );
        for (level, params) in cfg.levels.iter().enumerate() {
            let eta = params.eta;
            println!(
                "L{}: rate=1/{}, queries={}, eta={eta:.12e}, m={}",
                pretty_integer(level),
                pretty_integer(1usize << params.log_inv_rate),
                pretty_integer(params.queries),
                pretty_integer(johnson_m_param(params.log_inv_rate, params.log_msg_cols, eta) as usize),
            );
        }
    }
}
