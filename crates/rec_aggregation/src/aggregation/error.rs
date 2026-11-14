//! Why [`aggregate`](super::aggregate) made no proof.

/// Why [`aggregate`](super::aggregate) made no proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AggregateError {
    /// The request is inconsistent: too many children, a rate out of range, nothing to publish, or
    /// [`OutputClaims::Only`](super::OutputClaims::Only) asking for a claim or DA root the inputs do not
    /// cover. The message says which.
    InvalidInput(&'static str),
    /// A raw signature is invalid. Only some are caught here; the others make proving fail
    /// ([`Self::ProvingFailed`]).
    InvalidSignature,
    /// A child cannot be read: it was never a valid proof.
    InvalidChild,
    /// No proof was made: an input that passed the checks above is invalid (a forged signature or
    /// child), or the node is too large for one proof.
    ProvingFailed,
}

impl std::fmt::Display for AggregateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidInput(reason) => write!(f, "invalid input: {reason}"),
            Self::InvalidSignature => write!(f, "a raw signature is invalid"),
            Self::InvalidChild => write!(f, "a child is not a valid proof"),
            Self::ProvingFailed => write!(f, "proving failed"),
        }
    }
}

impl std::error::Error for AggregateError {}
