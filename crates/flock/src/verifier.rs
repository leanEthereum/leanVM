// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Errors of the R1CS reduction (zerocheck + lincheck + PCS opening).

use crate::lincheck;

use crate::zerocheck;

/// Why a flock reduction is rejected, by the step that rejects it.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum VerifyError {
    /// The zerocheck rejects.
    #[error("zerocheck: {0}")]
    Zerocheck(zerocheck::VerifyError),
    /// The lincheck rejects.
    #[error("lincheck: {0}")]
    Lincheck(lincheck::VerifyError),
}
