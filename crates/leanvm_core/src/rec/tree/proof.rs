//! A tree proof: the statement a node's circuit exposed, and the recursion proof of its run.

use super::Kind;
use super::statement::{StatementLayout, TreeStatement};
use crate::commitment::Rate;
use crate::cpu::DecodeError;
use crate::envelope::Envelope;
use crate::rec::circuit::{Assignment, Limbs};
use fiat_shamir::ProofTranscript;
use primitives::field::F192;

/// A proof made by one node of a tree, the root's included.
///
/// A first-level node's proof covers leaf proofs.
///
/// A higher node's proof covers tree proofs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreeProof {
    /// The kind of the circuit that made it, its statement's first word: its index within its tier, the tier above.
    pub(super) circuit: usize,
    /// Its statement's words.
    pub(super) words: Vec<F192>,
    /// The recursion proof.
    pub(super) proof: ProofTranscript,
    /// The rate it is proven at.
    pub(super) rate: Rate,
}

impl TreeProof {
    /// The header of a tree proof's bytes: the magic `LVMT`, then the tree protocol's version.
    ///
    /// The version is bumped by every change to what a tree proof says.
    const ENVELOPE: Envelope = Envelope::new(*b"LVMT", 20);

    /// The kind of node that made the proof.
    #[must_use]
    pub const fn kind(&self) -> Kind {
        if self.circuit == 0 { Kind::First } else { Kind::Node }
    }

    /// The proof's bytes.
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        Self::ENVELOPE.seal(&self.body())
    }

    /// The tree proof these bytes encode.
    ///
    /// # Errors
    ///
    /// - Bytes that are no tree proof.
    /// - A tree proof of another protocol version.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        // The header first: a foreign version is refused before its body is read.
        let body = Self::ENVELOPE.open(bytes)?;
        Self::from_body(body).ok_or(DecodeError::Malformed)
    }

    /// The body behind the header: its rate, its statement's words, then the recursion proof.
    ///
    /// ```text
    /// | log_inv_rate: u8 | n_words: u32 | words: 24 bytes each | proof |
    /// ```
    fn body(&self) -> Vec<u8> {
        let n_words = u32::try_from(self.words.len()).expect("a statement of a few hundred words");
        let mut bytes = vec![self.rate.log_inv_rate()];
        bytes.extend(n_words.to_le_bytes());
        for w in &self.words {
            bytes.extend(w.to_le_bytes());
        }
        bytes.extend(self.proof.to_bytes());
        bytes
    }

    /// The tree proof a body encodes, if it encodes one and nothing more.
    fn from_body(bytes: &[u8]) -> Option<Self> {
        let (&rate, rest) = bytes.split_first()?;
        let (n_words, rest) = rest.split_first_chunk::<4>()?;
        let n_words = usize::try_from(u32::from_le_bytes(*n_words)).ok()?;
        let (words, proof) = rest.split_at_checked(n_words.checked_mul(24)?)?;
        let words: Vec<F192> = (words.as_chunks::<24>().0.iter())
            .map(|&w| F192::from_le_bytes(w))
            .collect();
        let first = words.first()?;
        if (first.c1, first.c2) != (0, 0) {
            return None;
        }
        Some(Self {
            circuit: usize::try_from(first.c0).ok()?,
            words,
            proof: ProofTranscript::from_bytes(proof)?,
            rate: Rate::new(rate).ok()?,
        })
    }

    /// The proof of a run of the circuit of kind `circuit`, its statement the assignment's.
    pub(super) fn new(circuit: usize, assignment: &Assignment, proof: ProofTranscript, rate: Rate) -> Self {
        let words = (assignment.statement().iter())
            .map(|l| F192::new(l[0], l[1], l[2]))
            .collect();
        Self {
            circuit,
            words,
            proof,
            rate,
        }
    }

    /// Its statement, in a tree's layout.
    pub(super) fn statement(&self, layout: StatementLayout) -> TreeStatement {
        TreeStatement::new(layout, self.words.clone())
    }

    /// Its statement's words as the limbs the recursion proof states.
    pub(super) fn limbs(&self) -> Vec<Limbs> {
        self.words.iter().map(|w| [w.c0, w.c1, w.c2, 0]).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn legacy_and_foreign_tree_proofs_are_refused_before_the_body() {
        let current = TreeProof::ENVELOPE.seal(&[]);
        let expected = u16::from_le_bytes(current[4..6].try_into().unwrap());
        for found in 0..=19 {
            let bytes = Envelope::new(*b"LVMT", found).seal(&[0xff]);
            assert_eq!(
                TreeProof::from_bytes(&bytes),
                Err(DecodeError::UnsupportedVersion { found, expected })
            );
        }
        for magic in [*b"LVMP", *b"LVMZ"] {
            assert_eq!(
                TreeProof::from_bytes(&Envelope::new(magic, expected).seal(&[0xff])),
                Err(DecodeError::Malformed)
            );
        }
    }
}
