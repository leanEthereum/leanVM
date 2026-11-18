//! leanVM aggregates:
//! - leanXMSS signature (stateful, for the consensus layer)
//! - leanSPHINCS (stateless, for the execution layer)
//! - leanDA (PQ blobs)
//!
//! Two modes, one or the other:
//! - `prover`, the default: proves and verifies in this process, on the stable prover, or with `experimental_prover`
//!   the experimental one (the same proofs, byte for byte).
//! - `sidecar`, with `default-features = false`: builds no prover, and proves and verifies through the sidecar
//!   (`bins/leanvm-sidecar`) with `sidecar::Client`, proofs as their bytes.
//!
//! Example: [`crates/lean_vm/tests/api.rs`](https://github.com/leanEthereum/leanVM/blob/main/crates/lean_vm/tests/api.rs).

#[cfg(all(feature = "prover", feature = "sidecar"))]
compile_error!("`prover` and `sidecar` are two modes: pick one (`sidecar` with `default-features = false`)");

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

#[cfg(feature = "sidecar")]
pub use ::sidecar;
