//! Recursive aggregation of signature claims and LeanDA blobs, on either prover: everything here is generic over
//! [`isa::Prover`], which each prover tree implements.
//!
//! One bytecode (`guests/lean_ethereum.py`) serves every node of an aggregation tree.
//!
//! A node verifies `n_raw_lean_xmss` leanXMSS signatures, `n_raw_lean_sphincs` leanSPHINCS
//! signatures and `n_children` sub-proofs **of this same bytecode**, and
//! by default publishes the sorted deduplicated union of their signer sets. A claim
//! of either scheme is a `(pubkey, message)` pair; a leanXMSS signature carries its own
//! leaf index, which the statement does not record. Coverage is what carries the
//! security claim: a write-once slot per declared claim, written once by each raw
//! signature and each child claim, plus a final count, so every declared claim is
//! backed by a real signature or a verified child.
//!
//! Those slots are one contiguous region per scheme, so the one range check a write
//! already needs also keeps a signature off the other scheme's declared claims: that
//! is what makes the published split mean which scheme verified which claim, at
//! every level of the tree.
//!
//! A duplicate slot sits outside the prefix the digest hashes, so a claim in one is
//! covered and not published. `aggregate`'s `OutputClaims::Only` rests on that. A slot holds
//! four cells, the pubkey and its message, so the guest reads each signature's message
//! out of the slot it verifies.
//!
//! The bytecode is compiled to a fixed point on its own size
//! ([`unified_guest`]): the recursion placeholders depend on the inner bytecode
//! size, and here the inner bytecode is this one. Its digest does not need a
//! fixed point, riding the statement instead of the code.
//!
//! One fixed polynomial, the stacked bytecode, is too
//! big to evaluate in-circuit, so each node exports one deferred claim on it
//! and batches its children's carried claims with the fresh ones its
//! verifications raise (`doc/leanvm/main.tex` §Deferred evaluation claims). Only
//! the root's is discharged natively, by [`AggregateProof::verify`].
//!
//! `gen_verify` derives the guest's whole witness for a child from the layout
//! of the inner program (the stable prover's `cpu::layout`) and the summary the `verifier`
//! crate reads out of the child's proof.

mod cells;
mod child;
mod claim_pool;
mod coverage;
mod deferred;
mod error;
mod guest;
mod hints;
mod node;
mod placeholders;
mod proof;
#[cfg(any(test, feature = "signers-cache"))]
pub mod signers_cache;
mod statement;
#[cfg(test)]
mod tests;

pub use claims::{AggregateClaims, LeanSphincsClaim, LeanXmssClaim, OutputClaims};
pub use error::AggregateError;
pub use guest::unified_guest;
pub use node::aggregate;
pub use proof::AggregateProof;

/// The maximum number of child proofs one [`aggregate`] call can take.
pub const MAX_RECURSIONS: usize = 16;

pub use verifier::{MAX_LOG_INV_RATE, MIN_LOG_INV_RATE};
