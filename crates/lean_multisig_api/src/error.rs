use std::fmt::{Display, Formatter};

/// Every way a `lean_multisig_api` call can fail.
#[non_exhaustive]
#[derive(Debug)]
pub enum Error {
    KeyGen(xmss::XmssKeyGenError),
    Sign(xmss::XmssSignatureError),
    Aggregation(rec_aggregation::AggregationError),
    Proof(backend::ProofError),
    /// A `proof_or_sig` entry was not `SIGNATURE_SSZ_LEN` bytes and did not parse as an
    /// aggregate. The index is into `proof_or_sig`.
    MalformedEntry {
        index: usize,
    },
    /// A `proof_or_sig` entry was `SIGNATURE_SSZ_LEN` bytes — so it is a signature by the only
    /// classification rule there is — but failed to decode: damaged bytes, or non-canonical
    /// field elements. The index is into `proof_or_sig`.
    MalformedSignature {
        index: usize,
    },
    /// The bytes handed to `verify` are not a well-formed aggregate. Distinct from
    /// [`Self::MalformedEntry`], which names a position in a `proof_or_sig` vector — `verify`
    /// takes one blob and has no vector to index into.
    MalformedAggregate,
    /// A public key blob was not `PUB_KEY_SSZ_LEN` bytes, or held non-canonical field elements.
    MalformedPublicKey {
        index: usize,
    },
    /// Secret key bytes could not be deserialized.
    MalformedSecretKey,
    /// `public_keys.len()` must equal the number of raw signatures in `proof_or_sig`.
    PubkeyCountMismatch {
        expected: usize,
        got: usize,
    },
    /// The deduplicated signer union exceeds `MAX_XMSS_AGGREGATED`.
    TooManySigners {
        got: usize,
        max: usize,
    },
    /// `proof_or_sig` was empty.
    Empty,
    /// An aggregate proves a different (message, slot) than the one supplied: from `verify`,
    /// the aggregate under test; from `aggregate`, one of the supplied child aggregates.
    MessageMismatch,
    /// The proved signer set differs from the expected one.
    SignerSetMismatch,
}

impl From<xmss::XmssKeyGenError> for Error {
    fn from(err: xmss::XmssKeyGenError) -> Self {
        Self::KeyGen(err)
    }
}

impl From<xmss::XmssSignatureError> for Error {
    fn from(err: xmss::XmssSignatureError) -> Self {
        Self::Sign(err)
    }
}

impl From<rec_aggregation::AggregationError> for Error {
    fn from(err: rec_aggregation::AggregationError) -> Self {
        Self::Aggregation(err)
    }
}

impl From<backend::ProofError> for Error {
    fn from(err: backend::ProofError) -> Self {
        Self::Proof(err)
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            // These carry their cause in `source()`; adding it here too would print it twice
            // under any chain-aware reporter.
            Self::KeyGen(_) => write!(f, "Key generation failed"),
            // Not "Signing failed": `SecretKey::prepare` maps through this variant too, and it
            // signs nothing. The wording has to fit every entry point that can raise it.
            Self::Sign(_) => write!(f, "XMSS signing operation failed"),
            Self::Aggregation(_) => write!(f, "Aggregation failed"),
            Self::Proof(_) => write!(f, "Proof error"),
            Self::MalformedEntry { index } => {
                write!(f, "Entry {index} is neither a signature nor an aggregate")
            }
            Self::MalformedSignature { index } => {
                write!(f, "Entry {index} is signature-sized but could not be decoded")
            }
            Self::MalformedAggregate => write!(f, "The supplied bytes are not a well-formed aggregate"),
            Self::MalformedPublicKey { index } => write!(f, "Public key {index} is malformed"),
            Self::MalformedSecretKey => write!(f, "Secret key bytes could not be deserialized"),
            Self::PubkeyCountMismatch { expected, got } => {
                write!(f, "Expected {expected} public keys, got {got}")
            }
            Self::TooManySigners { got, max } => write!(f, "Too many signers: {got} (max {max})"),
            Self::Empty => write!(f, "Nothing to aggregate: no signatures or aggregates were supplied"),
            Self::MessageMismatch => {
                write!(
                    f,
                    "The aggregate proves a different (message, slot) than the one supplied"
                )
            }
            Self::SignerSetMismatch => write!(f, "The proved signer set differs from the expected one"),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::KeyGen(e) => Some(e),
            Self::Sign(e) => Some(e),
            Self::Aggregation(e) => Some(e),
            Self::Proof(e) => Some(e),
            // Spelled out rather than `_`: `#[non_exhaustive]` does not apply inside the
            // defining crate, so this match is compile-checked. A new wrapping variant then
            // fails to compile here instead of silently truncating the chain.
            Self::MalformedEntry { .. }
            | Self::MalformedSignature { .. }
            | Self::MalformedAggregate
            | Self::MalformedPublicKey { .. }
            | Self::MalformedSecretKey
            | Self::PubkeyCountMismatch { .. }
            | Self::TooManySigners { .. }
            | Self::Empty
            | Self::MessageMismatch
            | Self::SignerSetMismatch => None,
        }
    }
}
