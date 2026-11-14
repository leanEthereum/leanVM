//! Recursive aggregation of signature claims and LeanDA blobs, on either prover: everything here is generic over
//! [`isa::Prover`], which each prover tree implements.

pub mod aggregation;
/// The Keccak hash chain, proven end to end. A `src` module rather than its own
/// test binary so it shares the process with the other workloads.
#[cfg(test)]
mod hash_chain;
mod protocol;
#[cfg(any(test, feature = "signers-cache"))]
pub mod signers_cache;
mod wire;

pub use aggregation::{
    AggregateClaims, AggregateError, AggregateProof, LeanSphincsClaim, LeanXmssClaim, MAX_LOG_INV_RATE, MAX_RECURSIONS,
    MIN_LOG_INV_RATE, OutputClaims, aggregate, aggregate_with_stats, warm_up,
};

/// A proof of any program as the `verifier` crate takes it: the stacked bytecode it is about, and the proof's one
/// encoding.
pub mod vm {
    pub use crate::protocol::bytecode_table;
    pub use crate::wire::{from_bytes, to_bytes};
}
