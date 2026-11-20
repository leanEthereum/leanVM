//! The program a proof is about, prepared once so that verifying many proofs of it hashes its bytecode once.

use crate::field::{E, K};
use crate::hash::{Digest, keccak_hash};
use crate::layout::{BUS_BITS, MAX_LOG_BYTECODE, OP_DEREF, OP_KECCAK, TAG};
use crate::multilinear::eq_kernel;
use crate::{VerifierError, require};
use std::collections::BTreeMap;

/// The stacked bytecode multilinear, prepared to be evaluated, and the Fiat-Shamir IV it gives every transcript.
///
/// The multilinear is fixed while the points vary, so its values on the hypercube are grouped once (`blocks`).
#[derive(Clone, Debug)]
pub struct Bytecode {
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

    /// From the multilinear's values on the hypercube, LSB-first: what `isa::Program::stacked_bytecode` returns.
    /// Rejects a bytecode that is not the encoding of a program (`is_valid_encoding_of_a_leanisa_program`).
    pub fn new(stacked_bytecode: &[u64]) -> Result<Self, VerifierError> {
        require(
            is_valid_encoding_of_a_leanisa_program(stacked_bytecode),
            VerifierError::BytecodeShape,
        )?;
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
        Ok(Self {
            len: stacked_bytecode.len(),
            fiat_shamir_iv,
            blocks,
        })
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

fn is_valid_encoding_of_a_leanisa_program(stacked_bytecode: &[u64]) -> bool {
    let n = stacked_bytecode.len() >> BUS_BITS;
    let instruction = |pc: usize| {
        let slot = |s: usize| stacked_bytecode[s * n + pc];
        let zero_from = |first: usize| (first..1 << BUS_BITS).all(|s| slot(s) == 0);
        (0..3).all(|s| slot(s) == 0)
            && match (0..=OP_KECCAK).find(|&op| slot(3) == 1 << op) {
                Some(OP_DEREF) => matches!((slot(7), slot(8)), (0, 0) | (1, 0) | (0, 1)) && zero_from(9),
                Some(OP_KECCAK) => {
                    slot(12) <= 1 && slot(13) <= 1 && matches!((slot(14), slot(15)), (0, 0) | (1, 0) | (1, 1))
                }
                Some(_) => zero_from(7),
                None => false,
            }
    };
    n.is_power_of_two()
        && stacked_bytecode.len() == n << BUS_BITS
        && n <= 1 << MAX_LOG_BYTECODE
        && (0..n).all(instruction)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::layout::OP_XOR;
    use crate::multilinear::multilinear_eval;

    #[test]
    fn evaluate_matches_the_fold() {
        // Programs of XORs with random operands: distinct words, a repeated one (the opcode), zero slots, at the
        // largest size zero blocks (slots 7 to 15), and points on both sides of the block split.
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for variables in [BUS_BITS, BUS_BITS + 3, BLOCK_LOG, BLOCK_LOG + 2] {
            let n = 1 << (variables - BUS_BITS);
            let mut stacked_bytecode = vec![0u64; 1 << variables];
            stacked_bytecode[3 * n..4 * n].fill(1 << OP_XOR);
            stacked_bytecode[4 * n..7 * n].fill_with(&mut next);
            let point: Vec<E> = (0..variables).map(|_| E::new(next(), next())).collect();
            let words: Vec<K> = stacked_bytecode.iter().map(|&word| K(word)).collect();
            let bytecode = Bytecode::new(&stacked_bytecode).expect("a program");
            assert_eq!(bytecode.evaluate(&point), multilinear_eval(&words, &point));
        }
    }
}
