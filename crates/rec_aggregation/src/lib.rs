pub mod aggregation;
/// The BLAKE2s hash chain, proven end to end. A `src` module rather than its own
/// test binary so it shares the process, and so the slow flock circuit build,
/// with the other workloads.
#[cfg(test)]
mod hash_chain;
#[cfg(any(test, feature = "signers-cache"))]
pub mod signers_cache;

pub use aggregation::{
    AggregateVerifyError, AggregationError, ClaimSelection, DA_LOG_CELL, DA_LOG_K, DA_MAX_ROWS, EthereumProof,
    LeanSphincsClaim, LeanXmssClaim, MAX_DA_ROOTS, MAX_KEYS, MAX_RECURSIONS, SignatureClaims, aggregate,
    aggregate_with_stats, warm_up,
};
pub use verifier::VerifierError;
