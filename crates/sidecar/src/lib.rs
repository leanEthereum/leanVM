//! The leanVM sidecar: a process that proves and verifies for clients on the same machine.
//!
//! A client calls the library's `aggregate` and `verify` over a Unix stream socket, so it builds no prover: the
//! sidecar keeps the prover's allocator, threads and warm state out of the client's process. `bins/leanvm-sidecar`
//! runs `serve`, which the `server` feature brings; its `README.md` specifies the protocol, which any language can
//! speak, and [`Client`] speaks it from Rust.

mod client;
#[cfg(feature = "server")]
mod server;
mod wire;

pub use client::Client;
#[cfg(feature = "server")]
pub use server::serve;

/// One blob, as `lean_da` takes it: its symbols, each 128 bits.
pub type Blob = [u128; 1 << verifier::da::LOG_BLOB_SYMBOLS];

/// Why the sidecar made no proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Rejection {
    /// `AggregateError::InvalidInput`, or more blobs than one proof takes.
    InvalidInput = 1,
    /// `AggregateError::InvalidSignature`.
    InvalidSignature = 2,
    /// `AggregateError::InvalidChild`, or a child proof's bytes that do not decode.
    InvalidChild = 3,
    /// `AggregateError::ProvingFailed`.
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
    /// The socket failed, or the sidecar closed it: it stopped, crashed, or already serves its 16 connections. Connect
    /// again.
    Io(std::io::Error),
    /// The peer is not a leanVM sidecar, speaks another protocol version, or proves for another verifier.
    Incompatible(String),
    /// The sidecar's bytes are not the protocol. Connect again.
    Protocol(String),
    /// The request was refused, by the sidecar or, for one longer than the sidecar takes, by the client, which says
    /// why. The connection stays usable.
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
