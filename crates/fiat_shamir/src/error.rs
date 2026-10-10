//! Why a verifier refuses a transcript.

use thiserror::Error;

/// Why a proof's transcript cannot be read.
///
/// Each variant is a malformed proof, never a verifier bug.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum TranscriptError {
    /// The proof ends before a message the verifier reads, or the message's bytes encode no value.
    #[error("message {index} is missing or not canonical")]
    Malformed {
        /// How many messages were read before it.
        index: usize,
    },
    /// A hint is missing, or its length runs past the proof.
    #[error("hint {index} is missing or cut short")]
    MissingHint {
        /// How many hints were read before it.
        index: usize,
    },
    /// A hint does not decode, or does not authenticate.
    #[error("hint {index} is invalid")]
    InvalidHint {
        /// How many hints were read before it.
        index: usize,
    },
    /// A nonce is short of its proof of work.
    #[error("a nonce misses its {bits}-bit proof of work")]
    PowFailed {
        /// The difficulty it missed.
        bits: u32,
    },
    /// Bytes are left once the verifier is done.
    #[error("the proof has {narg} unread message bytes and {hints} unread hint bytes")]
    TrailingBytes {
        /// Message bytes left.
        narg: usize,
        /// Hint bytes left.
        hints: usize,
    },
}
