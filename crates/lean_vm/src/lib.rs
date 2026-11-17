//! leanVM aggregates:
//! - leanXMSS signature (stateful, for the consensus layer)
//! - leanSPHINCS (stateless, for the execution layer)
//! - leanDA (PQ blobs)
//!
//! With the default `prover` feature, it proves and verifies here: proving runs the stable prover, or with the
//! `experimental_prover` feature the experimental one, and both give the same proofs, byte for byte. Without it, it
//! builds no prover, and proves and verifies through the sidecar, [`sidecar::Client`]: the same claims and
//! signatures, proofs as their bytes.
//!
//! Example: [`crates/lean_vm/tests/api.rs`](https://github.com/leanEthereum/leanVM/blob/main/crates/lean_vm/tests/api.rs).

pub use claims::{AggregateClaims, LeanSphincsClaim, LeanXmssClaim, OutputClaims};
pub use verifier::{MAX_LOG_INV_RATE, MIN_LOG_INV_RATE};

#[cfg(feature = "prover")]
mod prover;
#[cfg(feature = "prover")]
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

/// Proving and verifying in another process, the sidecar (`bins/leanvm-sidecar`), which keeps the prover's memory,
/// threads and warm state out of this one. A client built without the `prover` feature verifies only there, so not
/// while its sidecar is down.
#[cfg(unix)]
pub mod sidecar {
    pub use ::sidecar::{Blob, Client, Rejection, SidecarError};
}
