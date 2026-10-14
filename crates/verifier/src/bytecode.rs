//! The program a proof is about, prepared once so that verifying many proofs of it hashes its table once.

use crate::field::{E, ZERO, reduce};
use crate::hash::{Digest, sha3_hash};
use crate::layout::RELATION_LABEL;
use crate::multilinear::eq_kernel;
use crate::{VerifierError, require};

/// The stacked bytecode multilinear, prepared to be evaluated, and the Fiat-Shamir IV it gives every transcript.
///
/// The table is fixed while the points vary, so its words are sorted once: per block of `2^BLOCK_LOG` words, the
/// positions of each distinct nonzero word, and the bytes those words have.
#[derive(Clone, Debug)]
pub struct Bytecode {
    len: usize,
    pub(crate) fiat_shamir_iv: Digest,
    blocks: Vec<Block>,
    /// A distinct word of a block, and where its positions end.
    words: Vec<(u64, usize)>,
    positions: Vec<u16>,
    /// A byte some word of a block has: which of the word's eight, times 256, plus its value.
    bytes: Vec<u16>,
}

/// A block with a nonzero word: its index, and where its words and bytes end.
#[derive(Clone, Copy, Debug)]
struct Block {
    index: usize,
    words_end: usize,
    bytes_end: usize,
}

/// How many low coordinates one block of [`Bytecode::evaluate`] spans: their eq table stays in cache, and a block is long enough to amortize closing it.
const BLOCK_LOG: usize = 14;

/// The nonzero bytes of `word`, each as its bucket: which byte, times 256, plus its value.
fn byte_buckets(word: u64) -> impl Iterator<Item = u16> {
    let bytes = word.to_le_bytes().into_iter().enumerate();
    bytes
        .filter(|&(_, value)| value != 0)
        .map(|(byte, value)| 256 * byte as u16 + value as u16)
}

impl Bytecode {
    pub fn new(table: &[u64]) -> Self {
        let encoded_bytecode: Vec<u8> = table.iter().flat_map(|word| word.to_le_bytes()).collect();
        let bytecode_hash = sha3_hash(&encoded_bytecode);
        let relation = sha3_hash(RELATION_LABEL).0;
        let length = (relation.len() as u64).to_le_bytes();
        let iv_preimage = [&b"leanvm"[..], &length, &relation, &bytecode_hash.0].concat();

        let (mut blocks, mut words, mut positions, mut bytes) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
        for (index, block) in table.chunks(1 << BLOCK_LOG).enumerate() {
            let mut members = std::collections::BTreeMap::<u64, Vec<u16>>::new();
            for (position, &word) in block.iter().enumerate().filter(|&(_, &word)| word != 0) {
                members.entry(word).or_default().push(position as u16);
            }
            if members.is_empty() {
                continue;
            }
            // Fewest positions first: the sum over a word's positions then runs one length many times over,
            // so its loop exit is predicted.
            let mut members: Vec<(u64, Vec<u16>)> = members.into_iter().collect();
            members.sort_by_key(|(_, at)| at.len());
            let mut used = std::collections::BTreeSet::new();
            for (word, at) in members {
                positions.extend(at);
                words.push((word, positions.len()));
                used.extend(byte_buckets(word));
            }
            bytes.extend(used);
            blocks.push(Block {
                index,
                words_end: words.len(),
                bytes_end: bytes.len(),
            });
        }
        Self {
            len: table.len(),
            fiat_shamir_iv: sha3_hash(&iv_preimage),
            blocks,
            words,
            positions,
            bytes,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The table's multilinear extension at an LSB-first `point`, equal to `multilinear_eval` of its words.
    ///
    /// The low coordinates' eq table weighs the words of every block, and the high coordinates' weighs the blocks.
    /// Within a block, the weights of each distinct word are summed once and credited to the buckets of its bytes,
    /// and each bucket to every bit its byte value sets: then bit `k` of the words holds its sum, which `x^k` scales.
    pub fn evaluate(&self, point: &[E]) -> Result<E, VerifierError> {
        require(
            point.len() < 64 && self.len == 1 << point.len(),
            VerifierError::MultilinearSize,
        )?;
        let (low, high) = point.split_at(point.len().min(BLOCK_LOG));
        let (low_weights, high_weights) = (eq_kernel(low), eq_kernel(high));
        let mut buckets = vec![ZERO; 8 * 256];
        let (mut words_start, mut positions_start, mut bytes_start) = (0, 0, 0);
        let mut total = ZERO;
        for block in &self.blocks {
            for &(word, positions_end) in &self.words[words_start..block.words_end] {
                let members = &self.positions[positions_start..positions_end];
                let sum = E::sum(members.iter().map(|&position| low_weights[position as usize]));
                // Every byte, the zero ones into buckets no block reads, so the loop has no branch on the data.
                for (byte, value) in word.to_le_bytes().into_iter().enumerate() {
                    buckets[256 * byte + value as usize] += sum;
                }
                positions_start = positions_end;
            }
            let mut bit_sums = [ZERO; 64];
            for &bucket in &self.bytes[bytes_start..block.bytes_end] {
                let sum = std::mem::take(&mut buckets[bucket as usize]);
                let (byte, value) = (bucket as usize / 256, bucket as u64 % 256);
                for (bit, bit_sum) in bit_sums[8 * byte..8 * byte + 8].iter_mut().enumerate() {
                    *bit_sum += sum.masked(0u64.wrapping_sub(value >> bit & 1));
                }
            }
            (words_start, bytes_start) = (block.words_end, block.bytes_end);
            total += high_weights[block.index] * monomial_sum(&bit_sums);
        }
        Ok(total)
    }
}

/// `sum_k x^k * sums[k]`: each limb shifted into place, then one reduction.
fn monomial_sum(sums: &[E; 64]) -> E {
    let (mut c0, mut c1, mut c2) = (0u128, 0u128, 0u128);
    for (k, sum) in sums.iter().enumerate() {
        c0 ^= (sum.c0 as u128) << k;
        c1 ^= (sum.c1 as u128) << k;
        c2 ^= (sum.c2 as u128) << k;
    }
    E::new(reduce(c0), reduce(c1), reduce(c2))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::K;
    use crate::multilinear::multilinear_eval;

    #[test]
    fn evaluate_matches_the_fold() {
        // An xorshift stream: words with every byte live, short words, a run of zeros, a zero block, and points on both sides of the block split.
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for variables in [0, 3, BLOCK_LOG, BLOCK_LOG + 2] {
            let mut table: Vec<u64> = (0..1 << variables).map(|_| next()).collect();
            for word in table.iter_mut().skip(5).take(40) {
                *word = 0;
            }
            for word in table.iter_mut().skip(50).step_by(3) {
                *word >>= 40;
            }
            for word in table.iter_mut().skip(2 << BLOCK_LOG).take(1 << BLOCK_LOG) {
                *word = 0;
            }
            let point: Vec<E> = (0..variables).map(|_| E::new(next(), next(), next())).collect();
            let words: Vec<K> = table.iter().map(|&word| K(word)).collect();
            let bytecode = Bytecode::new(&table);
            assert_eq!(bytecode.evaluate(&point), multilinear_eval(&words, &point));
        }
    }
}
