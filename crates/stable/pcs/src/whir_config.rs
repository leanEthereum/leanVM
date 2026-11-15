//! The shape of the WHIR opening: its level ladder, its query counts and its grinds, all the verifier's
//! (`verifier::derive_config`, Annex B's `sec:pcs-params`), so the prover opens exactly the shapes the verifier accepts:
//! a stack of `2^log_n` words with `log_n` in `MIN_STACKED_LOG..=MAX_STACKED_LOG`, at every rate.

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

/// Level 0's fold count, which is also the number of lanes a level-0 leaf holds, `2^INITIAL_FOLDING_FACTOR`.
pub const INITIAL_FOLDING_FACTOR: usize = 6;

/// Validate a production WHIR inverse-rate logarithm.
pub fn validate_log_inv_rate(log_inv_rate: usize) -> Result<(), String> {
    if !(MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE).contains(&log_inv_rate) {
        return Err(format!(
            "log_inv_rate must be in {MIN_LOG_INV_RATE}..={MAX_LOG_INV_RATE}, got {log_inv_rate}"
        ));
    }
    Ok(())
}

/// One WHIR opening's shape, level by level.
#[derive(Clone, Debug)]
pub struct ProverConfig {
    /// Each level's `log_inv_rate`.
    pub log_inv_rates: Vec<usize>,
    /// Each level's fold count, [`INITIAL_FOLDING_FACTOR`] first.
    pub folds: Vec<usize>,
    /// Each level's query count.
    pub queries: Vec<usize>,
}

/// The per-level shape table a [`ProverConfig`] implies for a `log_n`-variable opening.
#[derive(Clone, Debug)]
pub struct LevelShapes {
    /// Fold count per level.
    pub ks: Vec<usize>,
    /// Log message columns after each level's folds.
    pub log_msg_cols: Vec<usize>,
    /// Each level's block length: its message columns times its inverse rate.
    pub block_len: Vec<usize>,
    /// The variables left after every fold, which the tail sumcheck takes.
    pub yr_log_n: usize,
}

impl ProverConfig {
    /// See [`LevelShapes`].
    pub fn level_shapes(&self, log_n: usize) -> LevelShapes {
        let log_msg_cols: Vec<usize> = self
            .folds
            .iter()
            .scan(log_n, |vars, &k| {
                *vars -= k;
                Some(*vars)
            })
            .collect();
        let block_len = log_msg_cols
            .iter()
            .zip(&self.log_inv_rates)
            .map(|(&c, &r)| 1 << (c + r))
            .collect();
        LevelShapes {
            ks: self.folds.clone(),
            yr_log_n: *log_msg_cols.last().expect("at least one level"),
            log_msg_cols,
            block_len,
        }
    }
}

/// The configuration for a `2^log_n`-word stack at level-0 rate `2^-log_inv_rate`.
pub fn config_for_rate(log_n: usize, log_inv_rate: usize) -> Result<ProverConfig, String> {
    validate_log_inv_rate(log_inv_rate)?;
    let config = verifier::derive_config(log_n, log_inv_rate)
        .map_err(|_| format!("no WHIR configuration at log_n = {log_n}, rate {log_inv_rate}"))?;
    assert_eq!(config.folds[0], INITIAL_FOLDING_FACTOR);
    Ok(ProverConfig {
        log_inv_rates: config.log_inv_rates,
        folds: config.folds,
        queries: config.queries.to_vec(),
    })
}
