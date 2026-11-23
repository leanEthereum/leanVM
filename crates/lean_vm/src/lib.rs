//! leanVM aggregates:
//! - leanXMSS signature (stateful, for the consensus layer)
//! - leanSPHINCS (stateless, for the execution layer)
//! - leanDA (PQ blobs)
//!
//! Where proofs are made and checked:
//! - by default, in this process, on the stable prover;
//! - with the `experimental_prover` feature, in this process, on the experimental prover (the same proofs);
//! - with the `sidecar` feature, in a second process, the sidecar, which you launch with
//!   `cargo run --release -p leanvm-sidecar -- --socket <path>` (`bins/leanvm-sidecar`): this process sends it proving
//!   and verification requests through `sidecar::Client`.
//!
//! Example: [`crates/lean_vm/tests/api.rs`](https://github.com/leanEthereum/leanVM/blob/main/crates/lean_vm/tests/api.rs).

#[cfg(all(feature = "sidecar", feature = "experimental_prover"))]
compile_error!(
    "`experimental_prover` picks the prover of this process, and with `sidecar` this process does not prove: build the \
     sidecar with `--features experimental_prover` instead"
);

pub use aggregation::MAX_RECURSIONS;
pub use claims::{AggregateClaims, LeanSphincsClaim, LeanXmssClaim, OutputClaims};
pub use verifier::{MAX_LOG_INV_RATE, MIN_LOG_INV_RATE};

#[cfg(not(feature = "sidecar"))]
mod in_process;
#[cfg(not(feature = "sidecar"))]
pub use in_process::{AggregateError, AggregateProof, aggregate, lean_da, setup};

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

pub mod lean_vrf {
    pub use lean_vrf::{VRF_TREE_DEPTH, VrfKey, VrfProof, verify_vrf_proof};
}

#[cfg(feature = "sidecar")]
pub use ::sidecar;
