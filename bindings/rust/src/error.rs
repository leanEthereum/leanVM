//! The error type of every fallible operation.

use std::fmt;

use crate::vrf::Slot;
use crate::xmss::LeafIndex;

/// Why a lean-pq operation failed.
///
/// Each message is self-contained: it includes the underlying reason.
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

    /// Bytes handed to [`SecretKey::from_cache_bytes`](crate::xmss::SecretKey::from_cache_bytes)
    /// are not this key's tree cache: a wrong length, or trees that do not match its public key.
    #[error("not this leanXMSS key's tree cache")]
    InvalidXmssCache,

    /// A leanXMSS signature does not verify.
    #[error("leanXMSS signature at leaf index {leaf_index} does not verify")]
    XmssVerify {
        /// The leaf index the signature claims.
        leaf_index: LeafIndex,
    },

    /// A leanSPHINCS signature does not verify.
    #[error("leanSPHINCS signature does not verify")]
    SphincsVerify,

    /// A VRF range is empty or ends past `2^31`.
    #[error("VRF range {start}..{end} is empty or ends past 2^31")]
    InvalidVrfRange {
        /// The range's first slot.
        start: Slot,
        /// One past the range's last slot.
        end: Slot,
    },

    /// Bytes handed to [`Key::from_cache_bytes`](crate::vrf::Key::from_cache_bytes) are not this
    /// key's cache: malformed, or not leading to its root.
    #[error("not this VRF key's cache")]
    InvalidVrfCache,

    /// A VRF proof was asked for outside the key's range.
    #[error("VRF slot {slot} is outside the key's range")]
    VrfSlot {
        /// The slot.
        slot: Slot,
    },

    /// A VRF proof does not open.
    #[error("VRF proof for slot {slot} does not open under the root")]
    VrfVerify {
        /// The slot the proof was checked at.
        slot: u64,
    },

    /// A raw leanXMSS signature handed to aggregation does not verify.
    #[error("leanXMSS input {index} (leaf index {leaf_index}) does not verify")]
    InvalidXmssInput {
        /// Position of the input in the leanXMSS list.
        index: usize,
        /// The leaf index the signature claims.
        leaf_index: LeafIndex,
    },

    /// A raw leanSPHINCS signature handed to aggregation does not verify.
    #[error("leanSPHINCS input {index} does not verify")]
    InvalidSphincsInput {
        /// Position of the input in the leanSPHINCS list.
        index: usize,
    },

    /// One aggregation was given more children than one proof can recurse over.
    #[error("aggregation takes at most {max} children, got {count}")]
    TooManyChildren {
        /// The number of children supplied.
        count: usize,
        /// The most children one proof accepts.
        max: usize,
    },

    /// The sidecar refused to aggregate, and says why.
    ///
    /// Empty input and too many signers for one proof both land here.
    #[error("aggregation failed: {reason}")]
    Aggregation {
        /// The sidecar's reason.
        reason: String,
    },

    /// An aggregate proof does not prove the claims it was checked against, or its bytes are not a
    /// proof.
    #[error("the aggregate does not prove the given claims")]
    AggregateRejected,

    /// The sidecar cannot be reached, stopped, or is not a compatible leanVM sidecar.
    #[error("leanVM sidecar: {reason}")]
    Sidecar {
        /// What went wrong.
        reason: String,
    },

    /// The [`Sidecar`](crate::Sidecar) was closed.
    #[error("the sidecar is closed")]
    SidecarClosed,

    /// This platform has no Unix sockets, so it cannot reach a sidecar.
    #[error("the leanVM sidecar needs Unix sockets, which this platform lacks")]
    SidecarUnsupported,
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
