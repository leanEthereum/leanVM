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
        let mut cursor = hints;
        while let Some((len, rest)) = cursor.split_first_chunk::<4>() {
            cursor = rest.get(u32::from_le_bytes(*len) as usize..)?;
        }
        if !cursor.is_empty() {
            return None;
        }
        Some(Self {
            narg: narg.to_vec(),
            hints: hints.to_vec(),
        })
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
        let proof = ProofTranscript {
            narg: b"abc".to_vec(),
            hints: [&1u32.to_le_bytes()[..], b"h"].concat(),
        };
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
}
