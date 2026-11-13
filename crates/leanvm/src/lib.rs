//! leanVM aggregates:
//! - leanXMSS signature (stateful, for the consensus layer)
//! - leanSPHINCS (stateless, for the execution layer)
//! - leanDA (PQ blobs)
//!
//! Example: [`crates/leanvm/tests/api.rs`](https://github.com/leanEthereum/leanVM/blob/main/crates/leanvm/tests/api.rs).

pub use rec_aggregation::{
    AggregateVerifyError, AggregationError, EthereumClaims, EthereumProof, LeanSphincsClaim, LeanXmssClaim,
    MAX_RECURSIONS, SnarkProveError, SnarkVerifyError, aggregate,
};

pub use leanvm_core::pcs::{MAX_LOG_INV_RATE, MIN_LOG_INV_RATE};

pub mod lean_da {
    pub use ::lean_da::{
        BLOB_SYMBOLS, BlobSizeError, CELL_SYMBOLS, CELLS_PER_ROW, CODEWORD_SYMBOLS, DA_LOG_CELL, DA_LOG_K, DA_MAX_ROWS,
        DaWitness, commit,
    };
}

pub mod lean_xmss {
    pub use signatures::lean_xmss::{
        LOG_LIFETIME, LeafIndex, LeanXmssPublicKey, LeanXmssSecretKey, LeanXmssSignError, LeanXmssSignature,
        LeanXmssVerifyError, MAX_CACHED_BOTTOM_TREES, MESSAGE_LEN, Message, PUB_KEY_SIZE, SEED_LEN, SIG_SIZE, Seed,
        key_gen, key_gen_from_seed, sign, verify,
    };
}

pub mod lean_sphincs {
    pub use signatures::lean_sphincs::{
        LeanSphincsPublicKey, LeanSphincsSecretKey, LeanSphincsSignError, LeanSphincsSignature, LeanSphincsVerifyError,
        MESSAGE_LEN, Message, PUB_KEY_SIZE, SEED_LEN, SIG_SIZE, Seed, key_gen, key_gen_from_seed, sign, verify,
    };
}

/// Call once before [`aggregate`] or [`EthereumProof::verify`].
///
/// A proof's buffers are ordinary heap allocations, freed before it returns, so
/// proving speed depends on the process's global allocator. One that keeps freed
/// pages mapped serves the next proof from them with no page fault: jemalloc with
/// dirty pages that never decay, which the `leanvm` CLI installs. glibc's default
/// is the slow case, since it unmaps a large block on free.
pub fn setup() {
    parallel::init();
    rec_aggregation::warm_up();
}
