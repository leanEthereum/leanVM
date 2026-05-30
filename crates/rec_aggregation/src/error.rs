use std::fmt::{Display, Formatter};

use backend::ProofError;
use lean_prover::ProverError;

#[derive(Debug, Clone)]
pub enum AggregationError {
    Prover(ProverError),
    InvalidChildProof(ProofError),
    UnknownMessage,
    MultipleMessages,
    InvalidSplitIndex {
        index: usize,
        n_components: usize,
    },
    LimitExceeded {
        what: &'static str,
        actual: usize,
        max: usize,
    },
    EmptyAggregation {
        what: &'static str,
    },
    InconsistentChildren {
        what: &'static str,
    },
}

impl From<ProverError> for AggregationError {
    fn from(err: ProverError) -> Self {
        Self::Prover(err)
    }
}

impl From<ProofError> for AggregationError {
    fn from(err: ProofError) -> Self {
        Self::InvalidChildProof(err)
    }
}

impl Display for AggregationError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Prover(e) => write!(f, "{e}"),
            Self::InvalidChildProof(e) => write!(f, "Invalid child proof: {e}"),
            Self::UnknownMessage => write!(f, "Unknown message, not part of the multi-message aggregate"),
            Self::MultipleMessages => write!(f, "Multiple common messages in the multi-message aggregate"),
            Self::InvalidSplitIndex { index, n_components } => {
                write!(f, "Invalid split index {index} for {n_components} components")
            }
            Self::LimitExceeded { what, actual, max } => {
                write!(f, "Too many {what}: {actual} (max {max})")
            }
            Self::EmptyAggregation { what } => write!(f, "Nothing to aggregate: {what} is empty"),
            Self::InconsistentChildren { what } => write!(f, "Inconsistent aggregation children: {what}"),
        }
    }
}

impl std::error::Error for AggregationError {}
