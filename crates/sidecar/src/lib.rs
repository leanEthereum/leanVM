//! The leanVM sidecar: a process that proves for clients on the same machine.
//!
//! A client calls the library's `aggregate` over a Unix stream socket, and verifies proofs with the library, or with
//! the sidecar if it has no binding to it. The sidecar keeps the prover's allocator, threads and warm state out of
//! the client's process. `bins/leanvm-sidecar` runs [`serve`]; its `README.md` specifies the protocol, which any
//! language can speak, and [`Client`] speaks it from Rust.

mod client;
mod server;
mod wire;

pub use client::Client;
pub use server::{Config, serve};

/// Why the sidecar made no proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Rejection {
    /// [`aggregation::AggregateError::InvalidInput`], or more blobs than one proof takes.
    InvalidInput = 1,
    /// [`aggregation::AggregateError::InvalidSignature`].
    InvalidSignature = 2,
    /// [`aggregation::AggregateError::InvalidChild`], or a child proof's bytes that do not decode.
    InvalidChild = 3,
    /// [`aggregation::AggregateError::ProvingFailed`].
    ProvingFailed = 4,
    /// The request is not one: its bytes do not decode, or it is longer than the sidecar takes.
    Malformed = 5,
}

impl Rejection {
    fn from_code(code: u8) -> Option<Self> {
        [
            Self::InvalidInput,
            Self::InvalidSignature,
            Self::InvalidChild,
            Self::ProvingFailed,
            Self::Malformed,
        ]
        .into_iter()
        .find(|r| *r as u8 == code)
    }
}

/// Why a [`Client`] call failed.
#[derive(Debug)]
pub enum SidecarError {
    /// The socket failed, or the sidecar closed it: it stopped, or crashed. Connect again.
    Io(std::io::Error),
    /// The sidecar speaks another protocol version, or proves for another verifier or aggregation program.
    Incompatible(String),
    /// The sidecar's bytes are not the protocol, or prove other claims than asked for. Connect again.
    Protocol(String),
    /// The sidecar made no proof, and says why. The connection stays usable.
    Rejected(Rejection, String),
}

impl std::fmt::Display for SidecarError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(e) => write!(f, "sidecar connection: {e}"),
            Self::Incompatible(why) => write!(f, "incompatible sidecar: {why}"),
            Self::Protocol(why) => write!(f, "sidecar protocol: {why}"),
            Self::Rejected(rejection, message) => write!(f, "sidecar refused ({rejection:?}): {message}"),
        }
    }
}

impl std::error::Error for SidecarError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(e) => Some(e),
            _ => None,
        }
    }
}

impl From<std::io::Error> for SidecarError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}
