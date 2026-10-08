// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Why a reduction is refused.

use thiserror::Error;

use crate::lincheck::LincheckError;
use crate::zerocheck::ZerocheckError;

/// Why a flock reduction is refused, by the step that refuses it.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum FlockError {
    /// The zerocheck refuses.
    #[error("zerocheck: {0}")]
    Zerocheck(ZerocheckError),

    /// The lincheck refuses.
    #[error("lincheck: {0}")]
    Lincheck(LincheckError),
}
