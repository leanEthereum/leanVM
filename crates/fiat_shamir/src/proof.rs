//! A non-interactive proof: its messages, then its hints.

/// What a prover sends: the NARG string and the hints.
///
/// - The NARG string is every prover message, in order: exactly the bytes the sponge absorbed.
/// - The hints are data the transcript never absorbs, such as Merkle openings, each length-prefixed.
///
/// A hint is sound to leave out of the sponge only when something already bound authenticates it.
/// A Merkle opening is: its root is a message.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ProofTranscript {
    /// The prover messages.
    pub narg: Vec<u8>,
    /// The hints, each as its four-byte little-endian length, then its bytes.
    pub hints: Vec<u8>,
}

impl ProofTranscript {
    /// Append a hint: its length as four little-endian bytes, then its bytes.
    ///
    /// # Panics
    ///
    /// Panics on a hint of `2^32` bytes or more.
    pub fn push_hint(&mut self, hint: &[u8]) {
        let len = u32::try_from(hint.len()).expect("a hint under 4 GiB");
        self.hints.extend_from_slice(&len.to_le_bytes());
        self.hints.extend_from_slice(hint);
    }

    /// The hints, in order.
    #[must_use]
    pub fn iter_hints(&self) -> Hints<'_> {
        Hints::new(&self.hints)
    }

    /// The proof's bytes: the NARG string's length as eight little-endian bytes, the NARG string, then the hints.
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(8 + self.narg.len() + self.hints.len());
        bytes.extend_from_slice(&(self.narg.len() as u64).to_le_bytes());
        bytes.extend_from_slice(&self.narg);
        bytes.extend_from_slice(&self.hints);
        bytes
    }

    /// The proof these bytes encode.
    ///
    /// Refuses a length past the end, and hints that are not whole length-prefixed hints.
    /// The verifier then refuses messages or hints its protocol does not read.
    #[must_use]
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let (len, rest) = bytes.split_first_chunk::<8>()?;
        let len = usize::try_from(u64::from_le_bytes(*len)).ok()?;
        // The length is untrusted: compare it with what is there before slicing.
        let (narg, hints) = (len <= rest.len()).then(|| rest.split_at(len))?;

        // Walk the hints' length prefixes: they must end exactly at the end.
        let mut walk = Hints::new(hints);
        walk.by_ref().for_each(drop);
        walk.as_slice().is_empty().then(|| Self {
            narg: narg.to_vec(),
            hints: hints.to_vec(),
        })
    }
}

/// Length-prefixed hints, read in order.
///
/// Reading stops at the first length that runs past the end.
/// The bytes left unread are then still there to inspect.
#[derive(Clone, Debug)]
pub struct Hints<'a> {
    /// The bytes not yet read.
    rest: &'a [u8],
}

impl<'a> Hints<'a> {
    /// The hints framed in `bytes`.
    #[must_use]
    pub const fn new(bytes: &'a [u8]) -> Self {
        Self { rest: bytes }
    }

    /// The bytes not yet read.
    #[must_use]
    pub const fn as_slice(&self) -> &'a [u8] {
        self.rest
    }
}

impl<'a> Iterator for Hints<'a> {
    type Item = &'a [u8];

    fn next(&mut self) -> Option<&'a [u8]> {
        // A four-byte little-endian length, then that many bytes.
        // The length is untrusted, so a short tail is left unread rather than sliced past.
        // Indexed reads rather than chunk splits, which the extraction does not translate.
        let rest = self.rest;
        if rest.len() < 4 {
            return None;
        }
        let len = u32::from_le_bytes([rest[0], rest[1], rest[2], rest[3]]) as usize;
        if rest.len() - 4 < len {
            return None;
        }
        self.rest = &rest[4 + len..];
        Some(&rest[4..4 + len])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_proof_survives_its_bytes_and_nothing_else_decodes() {
        // Fixture: three message bytes, then one hint of one byte.
        //
        //     | 03 00 .. 00 | a b c | 01 00 00 00 | h |
        let mut proof = ProofTranscript {
            narg: b"abc".to_vec(),
            hints: Vec::new(),
        };
        proof.push_hint(b"h");
        let mut bytes = proof.to_bytes();
        assert_eq!(ProofTranscript::from_bytes(&bytes), Some(proof));

        // A byte short or over leaves a partial hint.
        assert_eq!(ProofTranscript::from_bytes(&bytes[..bytes.len() - 1]), None);
        assert_eq!(ProofTranscript::from_bytes(&[bytes.as_slice(), &[0]].concat()), None);

        // A length field past the end, or no length field at all.
        bytes[0] = 9;
        assert_eq!(ProofTranscript::from_bytes(&bytes), None);
        assert_eq!(ProofTranscript::from_bytes(&[0; 7]), None);
    }

    #[test]
    fn hints_read_back_in_order_and_stop_at_a_cut() {
        // Fixture: hints "ab", "" and "xyz", framed back to back.
        //
        //     | 02 00 00 00 | a b | 00 00 00 00 | 03 00 00 00 | x y z |
        let mut proof = ProofTranscript::default();
        for hint in [&b"ab"[..], b"", b"xyz"] {
            proof.push_hint(hint);
        }
        assert_eq!(proof.iter_hints().collect::<Vec<_>>(), [&b"ab"[..], b"", b"xyz"]);

        // Mutation: drop the last byte, so the third length runs one byte past the end.
        //
        //     the first two hints read, the third's 7 framed bytes stay unread
        proof.hints.pop();
        let mut hints = proof.iter_hints();
        assert_eq!(hints.by_ref().count(), 2);
        assert_eq!(hints.as_slice().len(), 4 + 2);
    }
}
