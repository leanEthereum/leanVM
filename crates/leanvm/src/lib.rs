//! leanVM aggregates:
//! - leanXMSS signature (stateful, for the consensus layer)
//! - leanSPHINCS (stateless, for the execution layer)
//! - leanDA (PQ blobs)
//!
//! Example: [`crates/leanvm/tests/api.rs`](https://github.com/leanEthereum/leanVM/blob/main/crates/leanvm/tests/api.rs).

pub use rec_aggregation::{
    AggregateProveError, AggregateVerifyError, EthereumClaims, EthereumProof, LeanSphincsClaim, LeanXmssClaim,
    MAX_RECURSIONS, StarkProveError, StarkVerifyError, aggregate,
};

pub use leanvm_core::pcs::{MAX_LOG_INV_RATE, MIN_LOG_INV_RATE};

pub mod lean_da {
    pub use ::lean_da::{
        Blob, BlobCountError, CELLS_PER_ROW, Codeword, DA_MAX_ROWS, DaWitness, MERKLE_PATH_LEN, Symbol, verify_cell,
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

/// Call once before [`aggregate`] or [`EthereumProof::verify`].
pub fn setup() {
    parallel::init();
    rec_aggregation::warm_up();
}
