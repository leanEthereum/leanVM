//! leanVM proves XMSS and SPHINCS signature claims and LeanDA blob well-formedness.
//!
//! Release only: the zkDSL compiler [`setup_verifier`] runs overflows the debug stack.
//!
//! End to end in [`tests/api.rs`](https://github.com/leanEthereum/leanVM/blob/main/tests/api.rs).

pub use rec_aggregation::{
    AggregateVerifyError, AggregationError, ClaimSelection, DA_LOG_CELL, DA_LOG_K, DA_MAX_ROWS, EthereumProof,
    MAX_DA_ROOTS, MAX_EPOCHS, MAX_KEYS, MAX_RECURSIONS, SignatureClaims, SphincsClaim, XmssClaimGroup, aggregate,
};

pub use lean_vm::{
    cpu::CpuError,
    pcs::{MAX_LOG_INV_RATE, MIN_LOG_INV_RATE},
};

/// LeanDA commitments. Blob symbols are `u64` words read in little-endian byte order.
pub mod lean_da {
    pub use ::lean_da::{
        BLOB_SYMBOLS, CELL_SYMBOLS, CELLS_PER_ROW, CODEWORD_SYMBOLS, DA_LOG_CELL, DA_LOG_K, DA_MAX_ROWS, DaCommitment,
        DaWitness, commit,
    };
}

pub mod xmss {
    /// The SSZ traits [`XmssPublicKey`] and [`XmssSignature`] implement: import
    /// them to call `as_ssz_bytes` and `from_ssz_bytes`.
    pub use ::xmss::{Decode, DecodeError, Encode};
    pub use ::xmss::{
        Digest, Epoch, LOG_LIFETIME, MESSAGE_LEN, Message, PUB_KEY_SIZE, PUB_KEY_SSZ_LEN, PublicParam, SIG_SIZE,
        SIGNATURE_SSZ_LEN, WotsSignature, XmssKeyGenError, XmssPublicKey, XmssSecretKey, XmssSignError, XmssSignature,
        XmssVerifyError, key_gen, key_gen_from_seed, sign, verify,
    };
}

pub mod sphincs {
    pub use ::sphincs::{
        Digest, FtsOpening, MESSAGE_LEN, Message, PUB_KEY_SIZE, PublicParam, SECRET_KEY_SIZE, SIG_SIZE,
        SphincsPublicKey, SphincsSecretKey, SphincsSignError, SphincsSignature, SphincsVerifyError, key_gen,
        key_gen_from, key_gen_from_seed, sign, verify,
    };
}

pub use rand;

/// Call once before verifying an [`EthereumProof`]. Idempotent, and
/// [`setup_prover`] does it for you.
pub fn setup_verifier() {
    lean_vm::init_prover_pool();
    rec_aggregation::warm_up();
}

/// Call once before [`aggregate`].
///
/// There is one arena per process, so only one [`aggregate`] call may run at a
/// time in a process: to aggregate in parallel, use separate processes.
pub fn setup_prover() {
    zk_alloc::enable_arena();
    setup_prover_without_arena();
}

/// [`setup_prover`] for a machine with small memory.
pub fn setup_prover_without_arena() {
    setup_verifier();
}
