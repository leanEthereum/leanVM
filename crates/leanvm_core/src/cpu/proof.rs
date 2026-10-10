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
#[derive(Clone, PartialEq, Eq)]
pub struct Proof(#[doc(hidden)] pub ProofTranscript);

impl Proof {
    /// The header of a proof's bytes: the magic `LVMP`, then the protocol version.
    ///
    /// The version is bumped by every change to what a proof says.
    const ENVELOPE: Envelope = Envelope::new(*b"LVMP", 16);

    /// The proof's bytes.
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        Self::ENVELOPE.seal(&self.0.to_bytes())
    }

    /// The proof these bytes encode.
    ///
    /// # Errors
    ///
    /// - Bytes that are no proof.
    /// - A proof of another protocol version.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        // The header first: a foreign version is refused before its body is read.
        let body = Self::ENVELOPE.open(bytes)?;
        ProofTranscript::from_bytes(body)
            .map(Self)
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
