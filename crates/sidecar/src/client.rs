//! The protocol from Rust.

use crate::wire::{self, Incoming};
use crate::{Blob, Rejection, SidecarError};
use claims::{AggregateClaims, OutputClaims};
use lean_sphincs::{LeanSphincsPublicKey, LeanSphincsSignature};
use lean_xmss::{LeanXmssPublicKey, LeanXmssSignature};
use std::io::Write;
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::time::Duration;

/// The longest response read beyond the request's length, which bounds the claims it carries: room for a hello, a
/// verdict or a proof, far more than any takes.
const ROOM: u64 = 16 << 20;

/// A connection to a sidecar, for one request at a time. Proofs are their bytes, as the library's
/// `AggregateProof::to_bytes` writes them and `from_bytes` reads them.
///
/// After an error other than [`SidecarError::Rejected`], the connection is in an unknown state: drop it and connect
/// again.
#[derive(Debug)]
pub struct Client {
    stream: UnixStream,
    prover: String,
    max_request: u64,
}

impl Client {
    /// Connects to the sidecar listening on `socket`, and checks it speaks this protocol version and proves for this
    /// verifier.
    pub fn connect(socket: impl AsRef<Path>) -> Result<Self, SidecarError> {
        let mut stream = UnixStream::connect(socket)?;
        let body = match wire::read_frame(&mut stream, ROOM)? {
            Incoming::Body(body) => body,
            Incoming::End => {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::ConnectionRefused,
                    "closed before its hello: the sidecar serves at most 16 connections at once",
                )
                .into());
            }
            // Not a hello, as `hello_version` then says.
            Incoming::TooLarge(_) => Vec::new(),
        };
        let version =
            wire::hello_version(&body).ok_or_else(|| SidecarError::Incompatible("not a leanVM sidecar".into()))?;
        if version != wire::VERSION {
            return Err(SidecarError::Incompatible(format!(
                "protocol version {version}, this client speaks {}",
                wire::VERSION
            )));
        }
        let hello =
            wire::decode_hello(&body).ok_or_else(|| SidecarError::Protocol("a hello that does not decode".into()))?;
        if hello.tag != verifier::TAG {
            return Err(SidecarError::Incompatible(format!(
                "proves for verifier {}, this client verifies {}",
                String::from_utf8_lossy(&hello.tag),
                String::from_utf8_lossy(verifier::TAG)
            )));
        }
        Ok(Self {
            stream,
            prover: hello.prover,
            max_request: hello.max_request,
        })
    }

    /// How long a call may wait on the sidecar, reading or writing, before it fails with [`SidecarError::Io`]; `None`,
    /// the default, waits as long as it takes (a sidecar that dies closes the connection, failing the call at once).
    /// Dropping the client then closes the connection, so the sidecar drops the request unless it has started proving
    /// it.
    pub fn set_timeout(&self, timeout: Option<Duration>) -> std::io::Result<()> {
        self.stream.set_read_timeout(timeout)?;
        self.stream.set_write_timeout(timeout)
    }

    /// The prover the sidecar runs: `stable` or `experimental`.
    pub fn prover(&self) -> &str {
        &self.prover
    }

    /// The library's `aggregate`, proven by the sidecar: its arguments, but for the blobs, which go as they are (none
    /// for no blobs) and which the sidecar builds the matrix of.
    ///
    /// As with the library, children must be valid (checked with [`Self::verify`]), or proving fails.
    pub fn aggregate(
        &mut self,
        children: &[(AggregateClaims, Vec<u8>)],
        raw_lean_xmss: &[(LeanXmssPublicKey, lean_xmss::Message, LeanXmssSignature)],
        raw_lean_sphincs: &[(LeanSphincsPublicKey, lean_sphincs::Message, LeanSphincsSignature)],
        blobs: &[Blob],
        output: OutputClaims,
        log_inv_rate: usize,
    ) -> Result<(AggregateClaims, Vec<u8>), SidecarError> {
        let request = wire::encode_request(children, raw_lean_xmss, raw_lean_sphincs, blobs, output, log_inv_rate);
        let body = self.call(&request)?;
        answer(wire::decode_response(&body))
    }

    /// The library's `AggregateProof::verify`, run by the sidecar: whether `proof` proves `claims`. Bytes that do not
    /// decode prove nothing.
    pub fn verify(&mut self, claims: &AggregateClaims, proof: &[u8]) -> Result<bool, SidecarError> {
        let body = self.call(&wire::encode_verify(claims, proof))?;
        answer(wire::decode_verdict(&body))
    }

    /// Sends a request frame and reads the response's body.
    fn call(&mut self, request: &[u8]) -> Result<Vec<u8>, SidecarError> {
        let len = request.len() as u64 - 8;
        if len > self.max_request {
            return Err(SidecarError::Rejected(
                Rejection::Malformed,
                format!(
                    "a request of {len} bytes, the sidecar takes at most {}",
                    self.max_request
                ),
            ));
        }
        self.stream.write_all(request)?;
        match wire::read_frame(&mut self.stream, request.len() as u64 + ROOM)? {
            Incoming::Body(body) => Ok(body),
            Incoming::End => Err(std::io::Error::from(std::io::ErrorKind::UnexpectedEof).into()),
            Incoming::TooLarge(len) => Err(SidecarError::Protocol(format!(
                "a response of {len} bytes, longer than any"
            ))),
        }
    }
}

/// A decoded response as the client's result.
fn answer<T>(decoded: Option<Result<T, (Rejection, String)>>) -> Result<T, SidecarError> {
    let decoded = decoded.ok_or_else(|| SidecarError::Protocol("a response that does not decode".into()))?;
    decoded.map_err(|(rejection, message)| SidecarError::Rejected(rejection, message))
}
