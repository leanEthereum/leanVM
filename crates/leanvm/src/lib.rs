//! leanVM aggregates:
//! - leanXMSS signature (stateful, for the consensus layer)
//! - leanSPHINCS (stateless, for the execution layer)
//! - leanDA (PQ blobs)
//!
//! Proving runs the stable prover, plain portable code, or with the `experimental-prover` feature the optimized one.
//! Both give the same proofs, byte for byte, and verifying needs neither.
//!
//! Example: [`crates/leanvm/tests/api.rs`](https://github.com/leanEthereum/leanVM/blob/main/crates/leanvm/tests/api.rs).

use ::lean_sphincs::{LeanSphincsPublicKey, LeanSphincsSignature};
use ::lean_xmss::{LeanXmssPublicKey, LeanXmssSignature};
use isa::Prover;
pub use rec_aggregation::{
    AggregateClaims, AggregateError, AggregateProof, LeanSphincsClaim, LeanXmssClaim, MAX_LOG_INV_RATE, MAX_RECURSIONS,
    MIN_LOG_INV_RATE, OutputClaims,
};

#[cfg(feature = "experimental-prover")]
type P = experimental_leanvm_core::ExperimentalProver;
#[cfg(not(feature = "experimental-prover"))]
type P = stable_leanvm_core::StableProver;

pub mod lean_da {
    pub use ::lean_da::{
        BLOB_SYMBOLS, Blob, BlobCountError, BlobMatrix, CELL_SYMBOLS, CELLS_PER_ROW, Codeword, DA_MAX_ROWS,
        MERKLE_PATH_LEN, Symbol, verify_cell,
    };
}

pub mod lean_xmss {
    pub use lean_xmss::{
        LOG_LIFETIME, LeafIndex, LeanXmssExpandedSecretKey, LeanXmssPublicKey, LeanXmssSignature,
        MAX_CACHED_BOTTOM_TREES, MESSAGE_LEN, Message, PUB_KEY_SIZE, SECRET_KEY_LEN, SIG_SIZE, SecretKey, key_gen,
        sign, verify,
    };
}

pub mod lean_sphincs {
    pub use lean_sphincs::{
        LOG_LIFETIME, LeanSphincsPublicKey, LeanSphincsSignature, MESSAGE_LEN, Message, PUB_KEY_SIZE, SECRET_KEY_LEN,
        SIG_SIZE, SecretKey, key_gen, sign, verify,
    };
}

/// Call once before [`aggregate`] or [`AggregateProof::verify`]: it starts the prover's thread pool and builds the
/// aggregation program.
pub fn setup() {
    P::init();
    rec_aggregation::warm_up::<P>();
}

/// Aggregate leanXMSS and leanSPHINCS signatures, blobs and the claims of child proofs.
///
/// - `children`: at most [`MAX_RECURSIONS`], each with its claims.
/// - `raw_lean_xmss`, `raw_lean_sphincs`: `(public_key, message, signature)`, in any order.
/// - `blobs`: the encoded blobs, if any ([`lean_da::BlobMatrix::build`]).
/// - `output`: which covered claims the proof attests.
/// - `log_inv_rate`: the code rate's log, in [`MIN_LOG_INV_RATE`]..=[`MAX_LOG_INV_RATE`]; higher gives a smaller proof
///   but slower proving.
///
/// # Errors
///
/// [`AggregateError`] says why there is no proof.
///
/// # WARNING
/// - Signatures and children must be valid (children checked with [`AggregateProof::verify`]): otherwise proving fails.
/// - Do not run two `aggregate` calls at once in one process, and call [`setup`] once before the first.
pub fn aggregate(
    children: &[(AggregateClaims, AggregateProof)],
    raw_lean_xmss: Vec<(LeanXmssPublicKey, lean_xmss::Message, LeanXmssSignature)>,
    raw_lean_sphincs: Vec<(LeanSphincsPublicKey, lean_sphincs::Message, LeanSphincsSignature)>,
    blobs: Option<&lean_da::BlobMatrix>,
    output: OutputClaims,
    log_inv_rate: usize,
) -> Result<(AggregateClaims, AggregateProof), AggregateError> {
    rec_aggregation::aggregate::<P>(children, raw_lean_xmss, raw_lean_sphincs, blobs, output, log_inv_rate)
}
