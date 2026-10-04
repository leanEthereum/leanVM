//! A proof of a run, and its bytes.

use crate::DecodeError;
use crate::envelope::Envelope;
use leanvm_core::cpu;
use std::fmt::{self, Debug, Formatter};

/// A proof that a program, run on some advice, exits with an output.
///
/// The program checks it against the output.
///
/// It travels as bytes.
#[derive(Clone, PartialEq, Eq)]
pub struct Proof(pub(crate) cpu::Proof);

impl Proof {
    /// The header of a proof's bytes: the magic `LVMP`, then the protocol version.
    ///
    /// The version is bumped by every change to what a proof says.
    const ENVELOPE: Envelope = Envelope::new(*b"LVMP", 6);

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
        cpu::Proof::from_bytes(body).map(Self).ok_or(DecodeError::Malformed)
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
    use crate::fixtures;

    #[test]
    fn a_proof_survives_its_bytes() {
        // A real proof, so the body decoder is exercised and not only the header.
        let proof = &fixtures::fibonacci_run().proof;
        let bytes = proof.to_bytes();
        assert_eq!(Proof::from_bytes(&bytes).as_ref(), Ok(proof));

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
