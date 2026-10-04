//! Why proof bytes fail to decode, and why a proof fails to verify.

use leanvm_core::cpu::CpuError;
use thiserror::Error;

/// Why bytes decode to no proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum DecodeError {
    /// The bytes are no proof.
    ///
    /// The header is foreign or cut short, or the body is not exactly one proof.
    #[error("the bytes are no proof")]
    Malformed,

    /// A proof of another protocol version.
    #[error("a proof of protocol version {found}, and this verifier reads version {expected}")]
    UnsupportedVersion {
        /// The version the bytes announce.
        found: u16,
        /// The version this build reads.
        expected: u16,
    },
}

/// Why a proof does not verify.
///
/// The message names the verifier's stage that refused it, for a human to read.
///
/// A caller only needs to know that the proof is refused.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
#[error("the proof does not verify: {0}")]
pub struct VerifyError(#[from] pub(crate) CpuError);
