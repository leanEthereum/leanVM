//! A proof of a run, and its bytes.

use super::DecodeError;
use crate::envelope::Envelope;
use fiat_shamir::ProofTranscript;
use std::fmt::{self, Debug, Formatter};

/// A proof that a program, run on some advice, exits with an output.
///
/// The program checks it against the output.
///
/// It travels as bytes.
///
/// A zero-knowledge proof says the same, and reveals nothing else of the run than its public shape.
#[derive(Clone, PartialEq, Eq)]
pub struct Proof(#[doc(hidden)] pub ProofTranscript, pub(crate) ProofKind);

/// Whether a proof is zero knowledge.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ProofKind {
    /// A plain proof.
    Plain,
    /// A zero-knowledge proof.
    ZeroKnowledge,
}

impl ProofKind {
    /// The header of a proof's bytes: the magic, then the protocol version.
    ///
    /// The version is bumped by every change to what a proof says.
    /// The magic tells the two kinds apart, so a proof of one kind is refused as the other.
    const fn envelope(self) -> Envelope {
        match self {
            Self::Plain => Envelope::new(*b"LVMP", 18),
            Self::ZeroKnowledge => Envelope::new(*b"LVMZ", 2),
        }
    }
}

impl Proof {
    /// Whether the proof is zero knowledge.
    #[must_use]
    pub fn is_zero_knowledge(&self) -> bool {
        self.1 == ProofKind::ZeroKnowledge
    }

    /// The proof's bytes.
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        self.1.envelope().seal(&self.0.to_bytes())
    }

    /// The proof these bytes encode.
    ///
    /// # Errors
    ///
    /// - Bytes that are no proof.
    /// - A proof of another protocol version.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        // The magic picks the kind, then the header is checked whole: a foreign version is refused before its body is read.
        let kind = if bytes.starts_with(&ProofKind::ZeroKnowledge.envelope().magic()) {
            ProofKind::ZeroKnowledge
        } else {
            ProofKind::Plain
        };
        let body = kind.envelope().open(bytes)?;
        ProofTranscript::from_bytes(body)
            .map(|t| Self(t, kind))
            .ok_or(DecodeError::Malformed)
    }
}

impl Debug for Proof {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // A proof is kilobytes of field elements, which say nothing to a reader.
        f.debug_struct("Proof").finish_non_exhaustive()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::commitment::Rate;
    use crate::cpu::{Program, Prover};
    use crate::rv::Region;
    use crate::rv::asm::{Addi, Asm, Reg};

    #[test]
    fn legacy_and_foreign_proofs_are_refused_before_the_body() {
        for (kind, magic, legacy) in [
            (ProofKind::Plain, *b"LVMP", 17),
            (ProofKind::ZeroKnowledge, *b"LVMZ", 1),
        ] {
            let current = kind.envelope().seal(&[]);
            let expected = u16::from_le_bytes(current[4..6].try_into().unwrap());
            for found in 0..=legacy {
                let bytes = Envelope::new(magic, found).seal(&[0xff]);
                assert_eq!(
                    Proof::from_bytes(&bytes),
                    Err(DecodeError::UnsupportedVersion { found, expected })
                );
            }
            assert_eq!(
                Proof::from_bytes(&Envelope::new(*b"LVMT", expected).seal(&[0xff])),
                Err(DecodeError::Malformed)
            );
        }
    }

    #[test]
    fn a_proof_survives_its_bytes() {
        // A real proof of `a0 = 5; exit`, so the body decoder is exercised and not only the header.
        let text = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 5).exit().finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 0, 0).expect("a program");
        let proof = Prover::new(Rate::MIN)
            .prove(&program, &[])
            .expect("the run exits")
            .proof;
        let bytes = proof.to_bytes();
        assert_eq!(Proof::from_bytes(&bytes), Ok(proof));

        // Invariant: the body is exactly one proof.
        //
        //     one byte short  →  truncated proof
        //     one byte over   →  trailing garbage
        assert_eq!(
            Proof::from_bytes(&bytes[..bytes.len() - 1]),
            Err(DecodeError::Malformed)
        );
        let over = [bytes.as_slice(), &[0]].concat();
        assert_eq!(Proof::from_bytes(&over), Err(DecodeError::Malformed));
    }
}
