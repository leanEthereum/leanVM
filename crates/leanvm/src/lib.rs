//! leanVM aggregates:
//! - leanXMSS signature (stateful, for the consensus layer)
//! - leanSPHINCS (stateless, for the execution layer)
//! - leanDA (PQ blobs)
//!
//! Two provers give the same proofs, byte for byte: [`Stable`], plain portable code, and `Experimental`, the
//! optimized one, behind the `experimental-prover` feature. What proves takes one as its type parameter; verifying
//! needs neither.
//!
//! Example: [`crates/leanvm/tests/api.rs`](https://github.com/leanEthereum/leanVM/blob/main/crates/leanvm/tests/api.rs).

#[cfg(feature = "experimental-prover")]
pub use experimental_leanvm_core::Experimental;
pub use isa::Prover;
pub use rec_aggregation::{
    AggregateClaims, AggregateError, AggregateProof, LeanSphincsClaim, LeanXmssClaim, MAX_LOG_INV_RATE, MAX_RECURSIONS,
    MIN_LOG_INV_RATE, OutputClaims, aggregate,
};
pub use stable_leanvm_core::Stable;

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

/// Call once, with the prover that will run, before [`aggregate`], [`lean_da::BlobMatrix::build`] or
/// [`AggregateProof::verify`]: it starts the prover's thread pool and builds the aggregation program.
pub fn setup<P: Prover>() {
    P::init();
    rec_aggregation::warm_up::<P>();
}
