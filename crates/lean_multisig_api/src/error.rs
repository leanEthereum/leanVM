use std::fmt::{Display, Formatter};

/// Every way a `lean_multisig_api` operation can fail.
#[non_exhaustive]
#[derive(Debug)]
pub enum Error {
    KeyGen(xmss::XmssKeyGenError),
    Sign(xmss::XmssSignatureError),
    /// A raw signature did not verify. The index refers to the input of [`crate::aggregate`],
    /// or is zero when verifying one standalone [`crate::Signature`].
    InvalidSignature {
        index: usize,
        source: xmss::XmssVerifyError,
    },
    Aggregation(rec_aggregation::AggregationError),
    Proof(backend::ProofError),
    /// A serialized [`crate::Signature`] envelope was malformed or unsupported.
    MalformedSignature,
    /// A serialized [`crate::MultiClaimProof`] envelope was malformed or unsupported.
    MalformedMultiClaimProof,
    /// Secret-key bytes failed their format or integrity checks.
    MalformedSecretKey,
    TooManySigners {
        got: usize,
        max: usize,
    },
    TooManyClaims {
        got: usize,
        max: usize,
    },
    Empty,
    MessageMismatch,
    SignerSetMismatch,
    ClaimSetMismatch,
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
        match err {
            rec_aggregation::AggregationError::InvalidChildProof(err) => Self::Proof(err),
            err => Self::Aggregation(err),
        }
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
            Self::KeyGen(_) => write!(f, "Key generation failed"),
            Self::Sign(_) => write!(f, "XMSS signing operation failed"),
            Self::InvalidSignature { index, .. } => write!(f, "Signature {index} is invalid"),
            Self::Aggregation(_) => write!(f, "Aggregation failed"),
            Self::Proof(_) => write!(f, "Proof error"),
            Self::MalformedSignature => write!(f, "The supplied bytes are not a well-formed signature"),
            Self::MalformedMultiClaimProof => {
                write!(f, "The supplied bytes are not a well-formed multi-claim proof")
            }
            Self::MalformedSecretKey => write!(f, "Secret key bytes failed validation"),
            Self::TooManySigners { got, max } => write!(f, "Too many signers: {got} (max {max})"),
            Self::TooManyClaims { got, max } => write!(f, "Too many distinct claims: {got} (max {max})"),
            Self::Empty => write!(f, "Nothing to aggregate: no signatures were supplied"),
            Self::MessageMismatch => write!(f, "The signature proves a different claim than the one supplied"),
            Self::SignerSetMismatch => write!(f, "The proved signer set differs from the expected one"),
            Self::ClaimSetMismatch => write!(f, "The proved claims or signer sets differ from the expected ones"),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::KeyGen(err) => Some(err),
            Self::Sign(err) => Some(err),
            Self::InvalidSignature { source, .. } => Some(source),
            Self::Aggregation(err) => Some(err),
            Self::Proof(err) => Some(err),
            Self::MalformedSignature
            | Self::MalformedMultiClaimProof
            | Self::MalformedSecretKey
            | Self::TooManySigners { .. }
            | Self::TooManyClaims { .. }
            | Self::Empty
            | Self::MessageMismatch
            | Self::SignerSetMismatch
            | Self::ClaimSetMismatch => None,
        }
    }
}
