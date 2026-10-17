//! leanVM proves leanXMSS and leanSPHINCS signature claims and LeanDA blob well-formedness.
//!
//! Release only: the zkDSL compiler [`setup_verifier`] runs overflows the debug stack.
//!
//! End to end in [`crates/leanvm/tests/api.rs`](https://github.com/leanEthereum/leanVM/blob/main/crates/leanvm/tests/api.rs).

pub use rec_aggregation::{
    AggregateVerifyError, AggregationError, ClaimSelection, DA_LOG_CELL, DA_LOG_K, DA_MAX_ROWS, EthereumProof,
    LeanSphincsClaim, LeanXmssClaim, MAX_DA_ROOTS, MAX_KEYS, MAX_RECURSIONS, SignatureClaims, VerifierError, aggregate,
};

pub use leanvm_core::{
    cpu::{ExecError, Fault, ProveError},
    pcs::{MAX_LOG_INV_RATE, MIN_LOG_INV_RATE},
};

/// LeanDA commitments. Blob symbols are `u64` words read in little-endian byte order.
pub mod lean_da {
    pub use ::lean_da::{
        BLOB_SYMBOLS, CELL_SYMBOLS, CELLS_PER_ROW, CODEWORD_SYMBOLS, DA_LOG_CELL, DA_LOG_K, DA_MAX_ROWS, DaCommitment,
        DaWitness, commit,
    };
}

pub mod lean_xmss {
    /// The SSZ traits [`LeanXmssPublicKey`] and [`LeanXmssSignature`] implement: import
    /// them to call `as_ssz_bytes` and `from_ssz_bytes`.
    pub use signatures::lean_xmss::{Decode, DecodeError, Encode};
    pub use signatures::lean_xmss::{
        Digest, LOG_LIFETIME, LayerSignature, LeafIndex, LeanXmssPublicKey, LeanXmssSecretKey, LeanXmssSignError,
        LeanXmssSignature, LeanXmssVerifyError, MESSAGE_LEN, Message, PUB_KEY_SIZE, PUB_KEY_SSZ_LEN, PublicParam,
        SEED_LEN, SIG_SIZE, SIGNATURE_SSZ_LEN, Seed, key_gen, key_gen_from_seed, sign, verify,
    };
}

pub mod lean_sphincs {
    pub use signatures::lean_sphincs::{
        Digest, ForestOpening, H, LeanSphincsPublicKey, LeanSphincsSecretKey, LeanSphincsSignError,
        LeanSphincsSignature, LeanSphincsVerifyError, MASTER_SECRET_LEN, MESSAGE_LEN, MasterSecret, Message,
        PUB_KEY_SIZE, PublicParam, SECRET_KEY_SIZE, SIG_SIZE, SubtreeOpening, TreeOpening, key_gen, key_gen_from_seed,
        sign, verify,
    };
}

pub use rand;

/// Call once before verifying an [`EthereumProof`]. Idempotent, and
/// [`setup_prover`] does it for you.
pub fn setup_verifier() {
    leanvm_core::init_prover();
    rec_aggregation::warm_up();
}

/// Call once before [`aggregate`].
///
/// A proof's buffers are ordinary heap allocations, freed before it returns, so
/// proving speed depends on the process's global allocator. One that keeps freed
/// pages mapped serves the next proof from them with no page fault: jemalloc with
/// dirty pages that never decay, which the `leanvm` CLI installs. glibc's default
/// is the slow case, since it unmaps a large block on free.
pub fn setup_prover() {
    setup_verifier();
}
