//! leanVM aggregates:
//! - leanXMSS signature (stateful, for the consensus layer)
//! - leanSPHINCS (stateless, for the execution layer)
//! - leanDA (PQ blobs)
//!
//! By default it proves and verifies in this process, on the stable prover, or with the `experimental_prover` feature
//! on the experimental one (the same proofs, byte for byte). With the `sidecar` feature, it proves and verifies only
//! through the sidecar (`bins/leanvm-sidecar`), with `sidecar::Client` and proofs as their bytes, and runs no prover
//! itself.
//!
//! Example: [`crates/lean_vm/tests/api.rs`](https://github.com/leanEthereum/leanVM/blob/main/crates/lean_vm/tests/api.rs).

#[cfg(all(feature = "sidecar", feature = "experimental_prover"))]
compile_error!(
    "`experimental_prover` picks the prover of this process, and with `sidecar` this process does not prove: build the \
     sidecar with `--features experimental_prover` instead"
);

pub use claims::{AggregateClaims, LeanSphincsClaim, LeanXmssClaim, OutputClaims};
pub use verifier::{MAX_LOG_INV_RATE, MIN_LOG_INV_RATE};

#[cfg(not(feature = "sidecar"))]
mod prover;
#[cfg(not(feature = "sidecar"))]
pub use prover::{AggregateError, AggregateProof, MAX_RECURSIONS, aggregate, lean_da, setup};

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

#[cfg(feature = "sidecar")]
pub use ::sidecar;
