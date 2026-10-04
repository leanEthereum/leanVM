//! A proof of an aggregation tree's node, and its bytes.

use super::Kind;
use crate::DecodeError;
use crate::envelope::Envelope;
use leanvm_core::rec::tree;
use std::fmt::{self, Debug, Formatter};

/// A proof made by one node of a tree, the root's included.
///
/// A first-level node's proof covers leaf proofs.
///
/// A higher node's proof covers tree proofs.
#[derive(Clone, PartialEq, Eq)]
pub struct TreeProof(pub(super) tree::TreeProof);

impl TreeProof {
    /// The header of a tree proof's bytes: the magic `LVMT`, then the tree protocol's version.
    ///
    /// The version is bumped by every change to what a tree proof says.
    const ENVELOPE: Envelope = Envelope::new(*b"LVMT", 1);

    /// The kind of node that made the proof.
    #[must_use]
    pub const fn kind(&self) -> Kind {
        self.0.kind()
    }

    /// The proof's bytes.
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        Self::ENVELOPE.seal(&self.0.to_bytes())
    }

    /// The tree proof these bytes encode.
    ///
    /// # Errors
    ///
    /// - Bytes that are no tree proof.
    /// - A tree proof of another protocol version.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        // The header first: a foreign version is refused before its body is read.
        let body = Self::ENVELOPE.open(bytes)?;
        tree::TreeProof::from_bytes(body)
            .map(Self)
            .ok_or(DecodeError::Malformed)
    }
}

impl Debug for TreeProof {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // The kind is what tells two tree proofs apart at a glance; the rest is field elements.
        f.debug_struct("TreeProof")
            .field("kind", &self.kind())
            .finish_non_exhaustive()
    }
}
