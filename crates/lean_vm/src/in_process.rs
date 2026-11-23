//! Proving and verifying, and LeanDA's encoding.

use crate::{AggregateClaims, OutputClaims};
use ::lean_sphincs::{LeanSphincsPublicKey, LeanSphincsSignature};
use ::lean_xmss::{LeanXmssPublicKey, LeanXmssSignature};
pub use aggregation::{AggregateError, AggregateProof};
use isa::Prover;

#[cfg(feature = "experimental_prover")]
type P = experimental_dispatch::ExperimentalProver;
#[cfg(not(feature = "experimental_prover"))]
type P = stable_lean_vm_core::StableProver;

// TODO: make leanDA a self-contained dependency, so that it can move to lib.rs
pub mod lean_da {
    pub use ::lean_da::{
        BLOB_SYMBOLS, Blob, BlobCountError, BlobMatrix, CELL_SYMBOLS, CELLS_PER_ROW, Codeword, DA_MAX_ROWS,
        MERKLE_PATH_LEN, Symbol, verify_cell,
    };
}

/// Call this function before generating / verifying proofs: it starts the prover's thread pool, with `threads` threads
/// (0: one per core), and builds the aggregation program.
///
/// # Panics
/// If the pool already runs with another thread count.
pub fn setup(threads: usize) {
    P::set_num_threads(threads);
    P::init();
    aggregation::unified_guest();
}

/// Aggregate leanXMSS and leanSPHINCS signatures, blobs and the claims of child proofs.
///
/// - `children`: at most [`MAX_RECURSIONS`](crate::MAX_RECURSIONS), each with its claims.
/// - `raw_lean_xmss`, `raw_lean_sphincs`: `(public_key, message, signature)`, in any order.
/// - `blobs`: the encoded blobs, if any ([`lean_da::BlobMatrix::build`]).
/// - `output`: which covered claims the proof attests.
/// - `log_inv_rate`: the code rate's log, in [`MIN_LOG_INV_RATE`](crate::MIN_LOG_INV_RATE)..=
///   [`MAX_LOG_INV_RATE`](crate::MAX_LOG_INV_RATE); higher gives a smaller proof but slower proving.
///
/// # Errors
///
/// [`AggregateError`] says why there is no proof.
///
/// Calls run one at a time: a second waits for the first.
///
/// # WARNING
/// - Signatures and children must be valid (children checked with [`AggregateProof::verify`]): otherwise proving fails.
pub fn aggregate(
    children: &[(AggregateClaims, AggregateProof)],
    raw_lean_xmss: Vec<(LeanXmssPublicKey, ::lean_xmss::Message, LeanXmssSignature)>,
    raw_lean_sphincs: Vec<(LeanSphincsPublicKey, ::lean_sphincs::Message, LeanSphincsSignature)>,
    blobs: Option<&lean_da::BlobMatrix>,
    output: OutputClaims,
    log_inv_rate: usize,
) -> Result<(AggregateClaims, AggregateProof), AggregateError> {
    aggregation::aggregate::<P>(children, raw_lean_xmss, raw_lean_sphincs, blobs, output, log_inv_rate)
        .map(|(claims, proof, _)| (claims, proof))
}
