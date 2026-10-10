//! Fiat-Shamir: an interactive proof made non-interactive by a duplex sponge.
//!
//! The design is spongefish's, after `draft-irtf-cfrg-fiat-shamir` and Chiesa-Orru (eprint 2025/536).
//!
//! A transcript has four operations:
//!
//! - a prover message is absorbed and written to the proof;
//! - a public message is absorbed only;
//! - a verifier message is squeezed;
//! - a hint is written to the proof and never absorbed.
//!
//! - A session identifier names the protocol and the relation.
//! - The instance is the first message, so every challenge depends on the statement.
//! - A message is absorbed in the same call that writes or reads it.
//! - The proof's messages are exactly the bytes the sponge absorbed.
//!
//! The sponge is a duplex built from the BLAKE2s compression function, the one hash the VM proves.

pub mod arith;
mod codec;
mod duplex;
mod error;
mod pow;
mod proof;
mod prover;
mod session;
mod verifier;

pub use codec::{Encoding, FromNarg, FromUniform, LengthPrefixed};
pub use duplex::{Blake2sDuplex, DuplexSponge, MAX_SQUEEZE, Role};
pub use error::TranscriptError;
pub use pow::ProofOfWork;
pub use proof::ProofTranscript;
pub use prover::ProverState;
pub use session::SessionId;
pub use verifier::VerifierState;

/// What both sides of a transcript do alike: draw verifier messages.
///
/// A step that only draws challenges, such as sampling query positions, is then written once.
pub trait Challenger {
    /// Draw a verifier message from the sponge.
    fn verifier_message<T: FromUniform>(&mut self) -> T;
}
