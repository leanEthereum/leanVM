//! Errors of aggregation and verification.

use lean_da::DA_MAX_ROWS;
use leanvm_core::cpu::ProveError;
use pcs::whir::{MAX_LOG_INV_RATE, MIN_LOG_INV_RATE};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AggregateVerifyError {
    /// The signer set is unsorted or holds a duplicate.
    MalformedSignerSet,
    /// A deferred claim's point has the wrong number of coordinates, or its value is not the bytecode's evaluation there.
    MalformedClaim,
    /// The bytes are not a valid encoding of an aggregate.
    MalformedEncoding,
    /// The snark did not verify. From [`aggregate`](super::aggregate), which does not verify its children, it means a child's proof could not be read.
    Snark(StarkVerifyError),
}

/// Why a proof did not verify. Opaque: its message is for debugging.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StarkVerifyError(pub(super) verifier::VerifierError);

impl std::fmt::Display for StarkVerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl std::error::Error for StarkVerifyError {}

/// Why the prover made no proof. Opaque: its message is for debugging.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StarkProveError(pub(super) ProveError);

impl std::fmt::Display for StarkProveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl std::error::Error for StarkProveError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AggregateProveError {
    /// A child's statement is malformed, or its proof cannot be walked. The walk fails on most tampering, the openings having to sit at query positions the transcript draws, so a statement that does not match the proof usually lands here as a Merkle opening error. Any other child that does not verify is a [`Self::ProofError`]: the guest's run fails on it.
    InvalidChild(AggregateVerifyError),
    /// No signature claims or DA root to publish.
    Empty,
    /// A declared claim is not one the contributions cover. A claim is a pubkey and a
    /// message, so another message is another claim.
    NotCovered,
    /// A raw signature's randomness does not decode to a target-sum encoding,
    /// so there is no witness to build for it.
    MalformedRawSignature,
    /// More than [`MAX_RECURSIONS`](super::MAX_RECURSIONS) children.
    TooLarge,
    /// More than [`DA_MAX_ROWS`] blobs.
    InvalidBlobCount { blobs: usize },
    /// The requested DA commitment is not a child's.
    BlobNotCovered,
    /// A node with blobs was asked to publish a DA commitment other than their matrix's.
    BlobsUnpublished,
    /// `log_inv_rate` is outside the range the WHIR configuration accepts.
    InvalidRate { log_inv_rate: usize },
    /// A child's proof outgrows the guest's baked buffers (`MU_CAP`, `STREAM_CAP`).
    ChildOutOfRange { log_committed: usize },
    /// The prover made no proof of this node: the guest rejects its input (a
    /// forged signature fails the guest's run), or its witness is larger than any
    /// verifier accepts (too many signatures for one proof).
    ProofError(StarkProveError),
}

impl std::fmt::Display for AggregateVerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedSignerSet => write!(f, "malformed signer set"),
            Self::MalformedClaim => write!(f, "malformed deferred claim"),
            Self::MalformedEncoding => write!(f, "not a valid aggregate encoding"),
            Self::Snark(e) => write!(f, "the snark did not verify: {e}"),
        }
    }
}

impl std::error::Error for AggregateVerifyError {}

impl From<lean_da::BlobCountError> for AggregateProveError {
    fn from(error: lean_da::BlobCountError) -> Self {
        Self::InvalidBlobCount { blobs: error.blobs }
    }
}

impl std::fmt::Display for AggregateProveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidChild(_) => write!(f, "invalid child aggregate"),
            Self::Empty => write!(f, "no signature claims or DA root to publish"),
            Self::NotCovered => write!(f, "a declared claim is not covered by the children and raw signatures"),
            Self::MalformedRawSignature => write!(f, "a raw signature does not decode to a target-sum encoding"),
            Self::TooLarge => {
                write!(f, "too many children")
            }
            Self::InvalidBlobCount { blobs } => write!(f, "{blobs} blobs: expected at most {DA_MAX_ROWS}"),
            Self::BlobNotCovered => write!(f, "the requested blob commitment is not carried by any child"),
            Self::BlobsUnpublished => write!(f, "a node with blobs publishes their matrix's root"),
            Self::InvalidRate { log_inv_rate } => {
                write!(
                    f,
                    "log_inv_rate {log_inv_rate} is outside {}..={}",
                    MIN_LOG_INV_RATE, MAX_LOG_INV_RATE
                )
            }
            Self::ChildOutOfRange { log_committed } => {
                write!(
                    f,
                    "a child commits 2^{log_committed} words, outside the guest's opening arms"
                )
            }
            Self::ProofError(e) => write!(f, "proving failed: {e}"),
        }
    }
}

impl std::error::Error for AggregateProveError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::InvalidChild(e) => Some(e),
            Self::ProofError(e) => Some(e),
            _ => None,
        }
    }
}
