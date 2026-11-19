//! The error type of every fallible operation.

use std::fmt;

#[cfg(feature = "aggregation")]
use lean_vm::AggregateError;

use crate::xmss::LeafIndex;

/// Why a lean-pq operation failed.
///
/// Every variant carries the values a caller needs to log or act on the failure.
///
/// Each message is self-contained: it already includes the upstream reason.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum Error {
    /// A byte encoding does not have its fixed length.
    #[error("{encoding} must be {expected} bytes, got {actual}")]
    InvalidLength {
        /// The encoding that was being decoded.
        encoding: Encoding,
        /// The only length that encoding has.
        expected: usize,
        /// The length that was supplied.
        actual: usize,
    },

    /// A leanXMSS signature does not verify.
    #[error("leanXMSS signature at leaf index {leaf_index} does not verify")]
    XmssVerify {
        /// The leaf index the signature claims.
        leaf_index: LeafIndex,
    },

    /// A leanSPHINCS signature does not verify.
    #[error("leanSPHINCS signature does not verify")]
    SphincsVerify,

    /// A raw leanXMSS signature handed to aggregation does not verify.
    #[cfg(feature = "aggregation")]
    #[error("leanXMSS input {index} (leaf index {leaf_index}) does not verify")]
    InvalidXmssInput {
        /// Position of the input in the leanXMSS list.
        index: usize,
        /// The leaf index the signature claims.
        leaf_index: LeafIndex,
    },

    /// A raw leanSPHINCS signature handed to aggregation does not verify.
    #[cfg(feature = "aggregation")]
    #[error("leanSPHINCS input {index} does not verify")]
    InvalidSphincsInput {
        /// Position of the input in the leanSPHINCS list.
        index: usize,
    },

    /// One aggregation was given more children than one proof can recurse over.
    #[cfg(feature = "aggregation")]
    #[error("aggregation takes at most {max} children, got {count}")]
    TooManyChildren {
        /// The number of children supplied.
        count: usize,
        /// The most children one proof accepts.
        max: usize,
    },

    /// The prover could not produce an aggregate.
    ///
    /// Empty input and too many signers for one proof both land here.
    #[error("aggregation failed: {reason}")]
    #[cfg(feature = "aggregation")]
    Aggregation {
        /// The upstream failure.
        reason: AggregateError,
    },

    /// Bytes handed to [`Aggregate::from_bytes`](crate::Aggregate::from_bytes) are not an
    /// encoded leanVM aggregate proof.
    #[error("malformed aggregate: the bytes are not a leanVM aggregate proof")]
    #[cfg(feature = "aggregation")]
    MalformedAggregate,

    /// An aggregate proof does not prove the claims it was checked against.
    #[error("the aggregate does not prove the given claims")]
    #[cfg(feature = "aggregation")]
    AggregateRejected,
    /// The process was forked after it started the prover pool, so it has the pool but not its
    /// threads, and a proof would never finish.
    #[error("cannot aggregate in a process forked after the prover started: aggregate in the parent, or start the child without forking (Python's `spawn` or `forkserver`)")]
    #[cfg(feature = "aggregation")]
    ForkedAfterSetup,
}

/// A fixed-length byte encoding this crate decodes.
///
/// It names the culprit of a length error.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Encoding {
    /// A 32-byte leanXMSS public key.
    XmssPublicKey,
    /// A 32-byte leanXMSS secret key, its seed.
    XmssSecretKey,
    /// A 2404-byte leanXMSS signature.
    XmssSignature,
    /// A 32-byte leanSPHINCS public key.
    SphincsPublicKey,
    /// A 32-byte leanSPHINCS secret key, its seed.
    SphincsSecretKey,
    /// A 7740-byte leanSPHINCS signature.
    SphincsSignature,
}

impl fmt::Display for Encoding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Human names, as they read inside a length error message.
        f.write_str(match self {
            Self::XmssPublicKey => "leanXMSS public key",
            Self::XmssSecretKey => "leanXMSS secret key",
            Self::XmssSignature => "leanXMSS signature",
            Self::SphincsPublicKey => "leanSPHINCS public key",
            Self::SphincsSecretKey => "leanSPHINCS secret key",
            Self::SphincsSignature => "leanSPHINCS signature",
        })
    }
}
