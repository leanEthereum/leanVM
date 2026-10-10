//! Session identifiers: what a transcript is for, before any message.

use crate::duplex::{Blake2sDuplex, DuplexSponge};

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
    /// The identifier of a tag, through the BLAKE2s duplex.
    #[must_use]
    pub fn new(tag: &[u8]) -> Self {
        Self::derive::<Blake2sDuplex>(tag)
    }

    /// The identifier of a tag, through the given sponge.
    ///
    /// The tag names the protocol, its version, its hash and codecs, and the relation.
    ///
    /// ```text
    ///     sponge = init("irtf-cfrg-fiat-shamir/session-id")
    ///     absorb(tag)
    ///     id     = squeeze(32)
    /// ```
    #[must_use]
    pub fn derive<H: DuplexSponge>(tag: &[u8]) -> Self {
        let mut sponge = H::init(DERIVATION_IV);
        sponge.absorb(tag);
        let mut id = [0; 32];
        sponge.squeeze(&mut id);
        Self(id)
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
