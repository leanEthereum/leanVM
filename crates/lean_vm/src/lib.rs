//! leanVM aggregates:
//! - leanXMSS signature (stateful, for the consensus layer)
//! - leanSPHINCS (stateless, for the execution layer)
//! - leanDA (PQ blobs)
//!
//! Where proofs are made and checked:
//! - by default, in this process, on the stable prover;
//! - with the `experimental_prover` feature, in this process, on the experimental prover (the same proofs).
//!
//! Example: [`crates/lean_vm/tests/api.rs`](https://github.com/leanEthereum/leanVM/blob/main/crates/lean_vm/tests/api.rs).

pub use aggregation::MAX_RECURSIONS;
pub use claims::{AggregateClaims, LeanSphincsClaim, LeanXmssClaim, OutputClaims};
pub use verifier::{MAX_LOG_INV_RATE, MIN_LOG_INV_RATE};

mod in_process;
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
