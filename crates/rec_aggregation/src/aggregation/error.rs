//! Errors of aggregation and verification.

use leanvm_core::cpu::ProveError;
use pcs::whir::{MAX_LOG_INV_RATE, MIN_LOG_INV_RATE};

/// The signature scheme a claim belongs to.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SignatureScheme {
    /// leanXMSS.
    LeanXmss,
    /// leanSPHINCS.
    LeanSphincs,
}

impl std::fmt::Display for SignatureScheme {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::LeanXmss => "leanXMSS",
            Self::LeanSphincs => "leanSPHINCS",
        })
    }
}

/// Why an aggregate was rejected.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum AggregateVerifyError {
    /// The signer set has as many claims as the guest's limit, or more.
    #[error(
        "the signer set holds {xmss} leanXMSS and {lean_sphincs} leanSPHINCS claims, not below the limit of {limit}"
    )]
    TooManySigners {
        /// The leanXMSS claims.
        xmss: usize,
        /// The leanSPHINCS claims.
        lean_sphincs: usize,
        /// The exclusive limit on their sum.
        limit: usize,
    },
    /// A scheme's signer list is not strictly sorted, so one claim could count many times.
    #[error("{scheme} claim {index} is not strictly above the one before it")]
    UnsortedSigners {
        /// The list's scheme.
        scheme: SignatureScheme,
        /// The first claim that is not above its predecessor.
        index: usize,
    },
    /// The deferred claim's point has the wrong number of coordinates.
    #[error("the deferred claim's point has {got} coordinates, the stacked bytecode {expected} variables")]
    PointLength {
        /// The stacked bytecode's variables.
        expected: usize,
        /// The point's coordinates.
        got: usize,
    },
    /// The deferred claim's value is not the stacked bytecode's evaluation at its point.
    #[error("the deferred claim's value is not the bytecode's evaluation at its point")]
    DeferredClaimMismatch,
    /// The bytes are not a valid encoding of an aggregate.
    #[error("not a valid aggregate encoding")]
    MalformedEncoding,
    /// The snark did not verify.
    ///
    /// From aggregation, which does not verify its children, it means a child's proof could not be read.
    #[error("the snark did not verify: {0}")]
    Snark(SnarkVerifyError),
}

/// Why a proof did not verify. Opaque: its message is for debugging.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[error(transparent)]
pub struct SnarkVerifyError(#[from] pub(super) verifier::VerifierError);

/// Why the prover made no proof. Opaque: its message is for debugging.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[error(transparent)]
pub struct SnarkProveError(#[from] pub(super) ProveError);

/// Why aggregation made no aggregate.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum AggregationError {
    /// A child's statement is malformed, or its proof cannot be walked.
    ///
    /// The walk fails on most tampering, the openings having to sit at query positions the transcript draws, so a statement that does not match the proof usually lands here as a Merkle opening error.
    /// Any other child that does not verify fails the guest's run, a proving error.
    #[error("child {child} is invalid: {error}")]
    InvalidChild {
        /// The child's index among the children.
        child: usize,
        /// Why it was refused.
        error: AggregateVerifyError,
    },
    /// No signature claims or DA root to publish.
    #[error("no signature claims or DA root to publish")]
    Empty,
    /// Declared claims the contributions do not cover.
    ///
    /// A claim is a pubkey and a message, so another message is another claim.
    #[error("{uncovered} declared {scheme} claim(s) are not covered by the children and raw signatures")]
    NotCovered {
        /// The declared claims' scheme.
        scheme: SignatureScheme,
        /// How many of them nothing covers.
        uncovered: usize,
    },
    /// A raw signature's layer does not decode to a target-sum encoding, so there is no witness to build for it.
    #[error("a raw {scheme} signature's layer {layer} does not decode to a target-sum encoding")]
    MalformedRawSignature {
        /// The signature's scheme.
        scheme: SignatureScheme,
        /// The layer that does not decode, 0 at the bottom.
        layer: usize,
    },
    /// More children than one node verifies.
    #[error("{children} children, more than the {max} one node verifies")]
    TooManyChildren {
        /// The children given.
        children: usize,
        /// The most one node takes.
        max: usize,
    },
    /// As many claim slots as the guest's limit or more, the duplicate slots counted.
    #[error("{slots} claim slots, duplicates included, not below the limit of {limit}")]
    TooManyClaims {
        /// The slots the coverage table needs.
        slots: usize,
        /// The exclusive limit.
        limit: usize,
    },
    /// The payload is not a whole number of blobs, or has more blobs than one commitment takes.
    #[error("{symbols} blob symbols are not a whole number of {blob_symbols}-symbol blobs, at most {max_blobs}")]
    InvalidBlobSize {
        /// The payload's length in symbols.
        symbols: usize,
        /// The symbols in one blob.
        blob_symbols: usize,
        /// The most blobs one commitment takes.
        max_blobs: usize,
    },
    /// The requested DA commitment is not a child's.
    #[error("the requested blob commitment is not carried by any child")]
    BlobNotCovered,
    /// A node with blobs was asked to publish a DA commitment other than their matrix's.
    #[error("a node with blobs publishes their matrix's root")]
    BlobsUnpublished,
    /// `log_inv_rate` is outside the range the WHIR configuration accepts.
    #[error("log_inv_rate {log_inv_rate} is outside {MIN_LOG_INV_RATE}..={MAX_LOG_INV_RATE}")]
    InvalidRate {
        /// The rate asked for, as a log.
        log_inv_rate: usize,
    },
    /// A child's committed witness falls outside the opening arms the guest was compiled with.
    ///
    /// Small aggregates are padded up to the floor, so this means a child too big: more signatures than one node can hold.
    #[error("child {child} commits 2^{log_committed} words, outside the guest's opening arms 2^{min}..=2^{max}")]
    ChildOutOfRange {
        /// The child's index among the children.
        child: usize,
        /// Its committed size, as a log.
        log_committed: usize,
        /// The smallest arm, as a log.
        min: usize,
        /// The largest arm, as a log.
        max: usize,
    },
    /// A child's bus side or proof stream is larger than the guest's fixed buffers.
    #[error(
        "child {child} has a bus side of size 2^{log_side} and a stream of {stream_len} scalars: the guest holds at most 2^{max_log_side} and {max_stream_len}"
    )]
    ChildOverCapacity {
        /// The child's index among the children.
        child: usize,
        /// Its widest bus side, as a log.
        log_side: usize,
        /// Its proof stream's length in scalars.
        stream_len: usize,
        /// The widest side the guest holds, as a log.
        max_log_side: usize,
        /// The longest stream the guest holds.
        max_stream_len: usize,
    },
    /// The prover made no proof of this node.
    ///
    /// The guest rejects its input (a forged signature fails the guest's run), or its witness is larger than any verifier accepts (too many signatures for one proof).
    #[error("proving failed: {0}")]
    ProofError(SnarkProveError),
}
