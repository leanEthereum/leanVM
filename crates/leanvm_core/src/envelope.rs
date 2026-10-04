//! The header in front of every proof's bytes.

use crate::cpu::DecodeError;

/// A magic and a protocol version, written in front of a proof's body.
///
/// A reader checks both before decoding the body.
///
/// So a proof of another kind or another version is refused, never misread.
///
/// ```text
///     | magic: 4 bytes | version: u16, little-endian | body |
/// ```
pub(crate) struct Envelope {
    /// The kind of proof that follows.
    magic: [u8; 4],
    /// The protocol version, bumped by every change to what such a proof says.
    version: u16,
}

impl Envelope {
    /// The header's length: four bytes of magic, two of version.
    const HEADER: usize = 6;

    /// The envelope of one kind of proof at one version.
    pub(crate) const fn new(magic: [u8; 4], version: u16) -> Self {
        Self { magic, version }
    }

    /// The body, behind the header.
    pub(crate) fn seal(&self, body: &[u8]) -> Vec<u8> {
        // One allocation for the header and the body together.
        let mut bytes = Vec::with_capacity(Self::HEADER + body.len());
        bytes.extend_from_slice(&self.magic);
        bytes.extend_from_slice(&self.version.to_le_bytes());
        bytes.extend_from_slice(body);
        bytes
    }

    /// The body behind a header of this kind and version.
    ///
    /// # Errors
    ///
    /// - A header cut short, or of another kind.
    /// - A proof of another version.
    pub(crate) fn open<'a>(&self, bytes: &'a [u8]) -> Result<&'a [u8], DecodeError> {
        // Split the header off: fewer than six bytes hold no header.
        let (magic, rest) = bytes.split_first_chunk::<4>().ok_or(DecodeError::Malformed)?;
        let (version, body) = rest.split_first_chunk::<2>().ok_or(DecodeError::Malformed)?;

        // Another magic is another kind of proof, or no proof at all.
        if *magic != self.magic {
            return Err(DecodeError::Malformed);
        }

        // The right kind at another version is named as such, so the reader knows which build to reach for.
        match u16::from_le_bytes(*version) {
            found if found == self.version => Ok(body),
            found => Err(DecodeError::UnsupportedVersion {
                found,
                expected: self.version,
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ENVELOPE: Envelope = Envelope::new(*b"TEST", 0x0102);

    #[test]
    fn a_sealed_body_opens_to_itself() {
        // The header is the magic, then the version's little-endian bytes.
        //
        //     "TEST" | 02 01 | "body"
        let sealed = ENVELOPE.seal(b"body");
        assert_eq!(sealed, b"TEST\x02\x01body");
        assert_eq!(ENVELOPE.open(&sealed), Ok(&b"body"[..]));

        // An empty body is still a body.
        assert_eq!(ENVELOPE.open(&ENVELOPE.seal(&[])), Ok(&[][..]));
    }

    #[test]
    fn a_foreign_header_is_refused() {
        let sealed = ENVELOPE.seal(b"body");

        // Mutation: flip one bit of the magic.
        //
        //     "UEST" != "TEST"  →  another kind of proof
        let mut magic = sealed.clone();
        magic[0] ^= 1;
        assert_eq!(ENVELOPE.open(&magic), Err(DecodeError::Malformed));

        // Mutation: bump the version's low byte.
        //
        //     0x0103 != 0x0102  →  both versions are named
        let mut version = sealed;
        version[4] += 1;
        assert_eq!(
            ENVELOPE.open(&version),
            Err(DecodeError::UnsupportedVersion {
                found: 0x0103,
                expected: 0x0102,
            })
        );

        // Every header cut short, from no byte to five.
        for len in 0..Envelope::HEADER {
            assert_eq!(ENVELOPE.open(&b"TEST\x02\x01"[..len]), Err(DecodeError::Malformed));
        }
    }
}
