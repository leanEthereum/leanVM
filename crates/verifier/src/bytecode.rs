//! The program a proof is about, prepared once so that verifying many proofs of it hashes its bytecode once.

use crate::field::{E, K};
use crate::hash::{Digest, keccak_hash};
use crate::layout::TAG;
use crate::multilinear::eq_kernel;
use crate::{VerifierError, require};
use std::collections::BTreeMap;

/// The stacked bytecode multilinear, prepared to be evaluated, and the Fiat-Shamir IV it gives every transcript.
///
/// The multilinear is fixed while the points vary, so its values on the hypercube are grouped once (`blocks`).
#[derive(Clone, Debug)]
pub struct Bytecode {
    /// How many values `new` was given: unless that is a power of two, [`Bytecode::evaluate`] rejects every point.
    len: usize,
    pub(crate) fiat_shamir_iv: Digest,
    /// The values cut into blocks of `2^BLOCK_LOG` consecutive ones: a block's index is the high coordinates, a
    /// position within it the low ones. For each block, every distinct nonzero value, with the positions where it
    /// occurs; zeros are left out.
    blocks: Vec<Vec<(K, Vec<u16>)>>,
}

/// How many low coordinates one block of [`Bytecode::evaluate`] spans: their eq table stays in cache.
const BLOCK_LOG: usize = 14;
const _: () = assert!(BLOCK_LOG <= u16::BITS as usize, "a position within a block is a u16");

impl Bytecode {
    /// The Fiat-Shamir IV every transcript of this program starts from.
    pub fn fiat_shamir_iv(&self) -> [u8; 32] {
        self.fiat_shamir_iv.0
    }

    /// From the multilinear's values on the hypercube, LSB-first: what `isa::Program::stacked_bytecode` returns. Any
    /// length is accepted, but only a power of two can be evaluated.
    pub fn new(stacked_bytecode: &[u64]) -> Self {
        let fiat_shamir_iv = {
            let iv_preimage: Vec<u8> = TAG
                .iter()
                .copied()
                .chain(stacked_bytecode.iter().flat_map(|word| word.to_le_bytes()))
                .collect();
            keccak_hash(&iv_preimage)
        };
        let blocks = stacked_bytecode
            .chunks(1 << BLOCK_LOG)
            .map(|block| {
                let mut members = BTreeMap::<u64, Vec<u16>>::new();
                for (position, &word) in block.iter().enumerate().filter(|&(_, &word)| word != 0) {
                    members.entry(word).or_default().push(position as u16);
                }
                // Fewest positions first: the sum over a value's positions then runs one length many times over, so
                // its loop exit is predicted.
                let mut members: Vec<(K, Vec<u16>)> = members.into_iter().map(|(word, at)| (K(word), at)).collect();
                members.sort_by_key(|(_, at)| at.len());
                members
            })
            .collect();
        Self {
            len: stacked_bytecode.len(),
            fiat_shamir_iv,
            blocks,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The multilinear at an LSB-first `point`, equal to `multilinear_eval` of its values.
    ///
    /// The low coordinates' eq table weighs the values of a block, and the high coordinates' weighs the blocks. Within
    /// a block, the weights of a value's positions are summed before it multiplies them, once per distinct value.
    pub fn evaluate(&self, point: &[E]) -> Result<E, VerifierError> {
        require(
            point.len() < 64 && self.len == 1 << point.len(),
            VerifierError::MultilinearSize,
        )?;
        let (low, high) = point.split_at(point.len().min(BLOCK_LOG));
        let (low_weights, high_weights) = (eq_kernel(low), eq_kernel(high));
        let block_value = |block: &Vec<(K, Vec<u16>)>| {
            E::sum(
                block
                    .iter()
                    .map(|(word, at)| E::sum(at.iter().map(|&i| low_weights[i as usize])) * *word),
            )
        };
        Ok(E::sum(
            self.blocks
                .iter()
                .zip(&high_weights)
                .map(|(block, &weight)| weight * block_value(block)),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::multilinear::multilinear_eval;

    #[test]
    fn evaluate_matches_the_fold() {
        // An xorshift stream: distinct words, repeated short words, a run of zeros, a zero block, and points on both sides of the block split.
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for variables in [0, 3, BLOCK_LOG, BLOCK_LOG + 2] {
            let mut stacked_bytecode: Vec<u64> = (0..1 << variables).map(|_| next()).collect();
            for word in stacked_bytecode.iter_mut().skip(5).take(40) {
                *word = 0;
            }
            for word in stacked_bytecode.iter_mut().skip(50).step_by(3) {
                *word >>= 40;
            }
            for word in stacked_bytecode.iter_mut().skip(2 << BLOCK_LOG).take(1 << BLOCK_LOG) {
                *word = 0;
            }
            let point: Vec<E> = (0..variables).map(|_| E::new(next(), next())).collect();
            let words: Vec<K> = stacked_bytecode.iter().map(|&word| K(word)).collect();
            let bytecode = Bytecode::new(&stacked_bytecode);
            assert_eq!(bytecode.evaluate(&point), multilinear_eval(&words, &point));
        }
    }
}
