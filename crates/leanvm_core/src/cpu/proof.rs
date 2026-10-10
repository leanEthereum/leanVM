//! A proof of a run, and its bytes.

use super::DecodeError;
use crate::envelope::Envelope;
use fiat_shamir::transcript::ProofTranscript;
use std::fmt::{self, Debug, Formatter};

/// A proof that a program, run on some advice, exits with an output.
///
/// The program checks it against the output.
///
/// It travels as bytes. A zero-knowledge proof says the same and reveals nothing else of the run than its public shape.
#[derive(Clone, PartialEq, Eq)]
pub struct Proof(#[doc(hidden)] pub ProofTranscript, pub(crate) bool);

impl Proof {
    /// The header of a proof's bytes: the magic `LVMP`, then the protocol version.
    ///
    /// The version is bumped by every change to what a proof says.
    const ENVELOPE: Envelope = Envelope::new(*b"LVMP", 15);

    /// The header of a zero-knowledge proof's bytes: the magic `LVMZ`, then its protocol version.
    ///
    /// The magic is the envelope's zero-knowledge bit: a proof of either kind is refused as the other.
    const ZK_ENVELOPE: Envelope = Envelope::new(*b"LVMZ", Self::ZK_VERSION);

    /// The zero-knowledge protocol's version, which also separates its transcript's seed.
    pub(crate) const ZK_VERSION: u16 = 15;

    /// Whether the proof is zero knowledge.
    #[must_use]
    pub const fn is_zk(&self) -> bool {
        self.1
    }

    /// The envelope a proof of this kind travels in.
    const fn envelope(zk: bool) -> Envelope {
        if zk { Self::ZK_ENVELOPE } else { Self::ENVELOPE }
    }

    /// The proof's bytes.
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        Self::envelope(self.1).seal(&self.0.to_bytes())
    }

    /// The proof these bytes encode.
    ///
    /// # Errors
    ///
    /// - Bytes that are no proof.
    /// - A proof of another protocol version.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        // The magic picks the kind, then the header is checked whole: a foreign version is refused before its body is read.
        let zk = bytes.starts_with(&Self::ZK_ENVELOPE.magic());
        let body = Self::envelope(zk).open(bytes)?;
        ProofTranscript::from_bytes(body)
            .map(|t| Self(t, zk))
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
    use crate::cpu::{Program, Prover};
    use crate::pcs::Rate;
    use crate::rv::Region;
    use crate::rv::asm::{Addi, Asm, Reg};

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
