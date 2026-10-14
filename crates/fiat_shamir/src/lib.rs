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
//!
//! A transcript hashes by its [`Hashing`]: the prover's the build's fastest kernels ([`Native`]), the native
//! verifier's the portable code ([`Portable`]). Both give the same bytes.

pub mod arith;
mod codec;
mod duplex;
mod pow;
mod proof;
mod prover;
mod verifier;

use arith::{Native, Portable};
use primitives::hash::portable;

pub use codec::{Encoding, FromNarg, FromUniform, LengthPrefixed};
pub use duplex::{Blake2sDuplex, Role};
pub use pow::ProofOfWork;
pub use proof::{Hints, ProofTranscript};
pub use prover::ProverState;
pub use verifier::{TranscriptError, VerifierState};

/// What both sides of a transcript do alike: draw verifier messages.
///
/// A step that only draws challenges, such as sampling query positions, is then written once.
pub trait Challenger {
    /// Draw a verifier message from the sponge.
    fn verifier_message<T: FromUniform>(&mut self) -> T;
}

/// How a transcript hashes: its duplex's compressions and its proof of work's trials.
pub trait Hashing: Copy {
    /// The BLAKE2s compression of `m` into `h` at byte counter `t`, final if `last`.
    fn compress(h: &mut [u32; 8], m: &[u32; 16], t: u64, last: bool);

    /// One-shot BLAKE2s-256.
    fn hash(data: &[u8]) -> [u8; 32];
}

/// The prover's: the build's kernels.
impl Hashing for Native {
    fn compress(h: &mut [u32; 8], m: &[u32; 16], t: u64, last: bool) {
        primitives::hash::compress(h, m, t, last);
    }

    fn hash(data: &[u8]) -> [u8; 32] {
        primitives::hash::hash(data)
    }
}

/// The native verifier's: the portable code.
impl Hashing for Portable {
    fn compress(h: &mut [u32; 8], m: &[u32; 16], t: u64, last: bool) {
        portable::compress(h, m, t, last);
    }

    fn hash(data: &[u8]) -> [u8; 32] {
        portable::hash(data)
    }
}

/// The 32 bytes that start a transcript.
///
/// It identifies the protocol, the relation, and the context, as `draft-irtf-cfrg-fiat-shamir` requires.
///
/// - Two protocols, or one protocol over two relations, get unrelated challenges.
/// - The instance is not part of it: the transcript absorbs the instance as its first message.
///
/// A newtype, so that a tag cannot stand in for an identifier by mistake.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SessionId(pub [u8; 32]);

/// The initialization vector session identifiers are derived under.
///
/// The draft's constant: exactly 32 bytes.
const DERIVATION_IV: [u8; 32] = *b"irtf-cfrg-fiat-shamir/session-id";

impl SessionId {
    /// The identifier of a tag.
    ///
    /// Both sides derive it, the verifier included, so it compresses by the portable code.
    ///
    /// The tag names the protocol, its version, its hash and codecs, and the relation.
    ///
    /// ```text
    ///     sponge = init("irtf-cfrg-fiat-shamir/session-id")
    ///     absorb(tag)
    ///     id     = squeeze(32)
    /// ```
    #[must_use]
    pub fn new(tag: &[u8]) -> Self {
        let mut sponge = Blake2sDuplex::<Portable>::new(DERIVATION_IV);
        sponge.absorb(tag);
        let mut id = [0; 32];
        sponge.squeeze(&mut id);
        Self(id)
    }

    /// The identifier of a protocol's tag followed by the relation it is run for.
    ///
    /// ```text
    ///     id = new(protocol || relation)
    /// ```
    ///
    /// The relation is a digest or a parent session, so it has a fixed length and the concatenation is unambiguous.
    #[must_use]
    pub fn tagged(protocol: &[u8], relation: &[u8]) -> Self {
        Self::new(&[protocol, relation].concat())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn distinct_tags_give_distinct_identifiers() {
        // A tag and its extension by one zero byte must not collide.
        //
        // The absorb run's length in the sponge's framing tells them apart.
        let a = SessionId::new(b"protocol");
        let b = SessionId::new(b"protocol\0");
        assert_ne!(a, b);
    }
}
