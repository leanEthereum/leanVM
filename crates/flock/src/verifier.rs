// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Errors of the R1CS reduction (zerocheck + lincheck + PCS opening).

use crate::lincheck::LincheckError;
use crate::zerocheck::ZerocheckError;
use thiserror::Error;

/// Why a flock reduction is rejected, by the step that rejects it.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum FlockError {
    /// The zerocheck rejects.
    #[error("zerocheck: {0}")]
    Zerocheck(ZerocheckError),
    /// The lincheck rejects.
    #[error("lincheck: {0}")]
    Lincheck(LincheckError),
}
