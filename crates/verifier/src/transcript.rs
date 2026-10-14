//! Proof transport and Fiat-Shamir.

use crate::field::{E, K, ZERO};
use crate::hash::{Digest, blake2s_hash};
use crate::merkle::{MerkleOpenings, MerklePath};
use crate::multilinear::{log2_strict, poly_eval};
use crate::{VerifierError, require};

/// The scalar stream, and the Merkle openings.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
    pub stream: Vec<E>,
    pub merkle_openings: MerkleOpenings,
}

impl Proof {
    /// From the two encodings: the stream as 24-byte little-endian field elements, and the raw Merkle openings as they are.
    pub fn load(stream: &[u8], merkle_openings: &[u8]) -> Result<Self, VerifierError> {
        require(stream.len().is_multiple_of(24), VerifierError::StreamNotWholeElements)?;
        Ok(Self {
            stream: stream
                .as_chunks::<24>()
                .0
                .iter()
                .map(|data| E::from_bytes(data))
                .collect::<Result<_, _>>()?,
            merkle_openings: MerkleOpenings::Raw(merkle_openings.to_vec()),
        })
    }
}

pub const DS_OBSERVE: u64 = 1;
pub const DS_SQUEEZE: u64 = 2;
const DS_POW_BASE: u64 = 3;
const DS_POW_NONCE: u64 = 4;

/// Hash two four-word operands.
pub fn compress(left: [u64; 4], right: [u64; 4]) -> [u64; 4] {
    let mut data = [0u8; 64];
    for (bytes, word) in data.as_chunks_mut().0.iter_mut().zip(left.into_iter().chain(right)) {
        *bytes = word.to_le_bytes();
    }
    blake2s_hash(&data).words()
}

pub struct Transcript<'a> {
    proof: &'a Proof,
    state: [u64; 4],
    stream_offset: usize,  // in E field elements
    opening_offset: usize, // in bytes, or in batches of the pruned form
    checked: bool,         // false for a replay, which walks the proof and checks none of it
    paths: Vec<MerklePath>,
}

impl<'a> Transcript<'a> {
    pub fn new(proof: &'a Proof, fiat_shamir_iv: Digest, public_input: Digest, checked: bool) -> Self {
        Self {
            proof,
            state: compress(fiat_shamir_iv.words(), public_input.words()),
            stream_offset: 0,
            opening_offset: 0,
            checked,
            paths: Vec::new(),
        }
    }

    /// Whether the proof's checks run. Every one a replay skips is behind this, and nothing else is.
    pub fn checked(&self) -> bool {
        self.checked
    }

    pub fn stream_offset(&self) -> usize {
        self.stream_offset
    }

    fn observe(&mut self, value: E) {
        self.state = compress(self.state, [value.c0, value.c1, value.c2, DS_OBSERVE]);
    }

    pub fn sample(&mut self) -> E {
        self.state = compress(self.state, [0, 0, 0, DS_SQUEEZE]);
        E::new(self.state[0], self.state[1], self.state[2])
    }

    pub fn samples(&mut self, count: usize) -> Vec<E> {
        (0..count).map(|_| self.sample()).collect()
    }

    fn next(&mut self) -> Result<E, VerifierError> {
        require(
            self.stream_offset < self.proof.stream.len(),
            VerifierError::StreamExhausted,
        )?;
        let value = self.proof.stream[self.stream_offset];
        self.stream_offset += 1;
        Ok(value)
    }

    pub fn next_scalar(&mut self) -> Result<E, VerifierError> {
        let value = self.next()?;
        self.observe(value);
        Ok(value)
    }

    pub fn next_scalars(&mut self, count: usize) -> Result<Vec<E>, VerifierError> {
        (0..count).map(|_| self.next_scalar()).collect()
    }

    pub fn grind_check(&mut self, bits: u32) -> Result<(), VerifierError> {
        let nonce = self.next()?;
        let block = [nonce.c0, nonce.c1, nonce.c2, DS_POW_NONCE];
        if self.checked {
            let digest = compress(compress(self.state, [0, 0, 0, DS_POW_BASE]), block)[0];
            let valid = if bits == 0 {
                nonce == ZERO
            } else {
                digest & ((1 << bits) - 1) == 0
            };
            require(valid, VerifierError::GrindingNonce)?;
        }
        self.state = compress(self.state, block);
        Ok(())
    }

    fn merkle_data(&mut self, data: &'a [u8], length: usize) -> Result<&'a [u8], VerifierError> {
        let end = self.opening_offset + length;
        require(end <= data.len(), VerifierError::MerkleOpeningMissing)?;
        let chunk = &data[self.opening_offset..end];
        self.opening_offset = end;
        Ok(chunk)
    }

    /// The leaf images at `queries`, authenticated against `root`. `row_words` is what the pruned form stores of
    /// each, the rest of the image being a zero prefix; the raw form carries whole images.
    ///
    /// Each query's own path is kept for [`Self::finish`], whichever form the proof came in.
    pub fn merkle(
        &mut self,
        root: Digest,
        block_length: u64,
        queries: &[u64],
        row_words: usize,
        leaf_words: usize,
    ) -> Result<Vec<Vec<K>>, VerifierError> {
        let height = log2_strict(block_length)?;
        let paths = match &self.proof.merkle_openings {
            MerkleOpenings::Raw(data) => {
                let mut paths = Vec::with_capacity(queries.len());
                for &leaf_index in queries {
                    let leaf = self.merkle_data(data, 8 * leaf_words)?;
                    let mut siblings = Vec::with_capacity(height);
                    for _ in 0..height {
                        let sibling = self.merkle_data(data, 32)?;
                        siblings.push(sibling.try_into().expect("32 bytes were read"));
                    }
                    let leaf = leaf.as_chunks().0.iter().map(|&word| K(u64::from_le_bytes(word)));
                    let path = MerklePath {
                        leaf_index,
                        leaf: leaf.collect(),
                        siblings,
                    };
                    if self.checked {
                        require(path.root() == root, VerifierError::MerkleRootMismatch)?;
                    }
                    paths.push(path);
                }
                paths
            }
            MerkleOpenings::Pruned(batches) => {
                let batch = batches
                    .get(self.opening_offset)
                    .ok_or(VerifierError::MerkleOpeningMissing)?;
                self.opening_offset += 1;
                let (batch_root, paths) = batch.expand(height, queries, row_words, leaf_words)?;
                if self.checked {
                    require(batch_root == root, VerifierError::MerkleRootMismatch)?;
                }
                paths
            }
        };
        let rows = paths.iter().map(|path| path.leaf.clone()).collect();
        self.paths.extend(paths);
        Ok(rows)
    }

    /// returns q(X) := c0 + c1X + c2X^2 + ...
    pub fn sumcheck_round_poly(
        &mut self,
        count: usize,
        claim: E,
        eq_factor: Option<E>,
    ) -> Result<Vec<E>, VerifierError> {
        let Some(eq_factor) = eq_factor else {
            // `q(0) + q(1) == claim`. The transcript contains c0, c2, c3 ...
            let constant = self.next_scalar()?;
            let tail = self.next_scalars(count - 2)?;
            return Ok([vec![constant, claim + E::sum(tail.iter().copied())], tail].concat());
        };
        // `(1 + r) q(0) + r q(1) == claim`. The transcript contains c1, c2, c3 ... (r := eq_factor)
        let tail = self.next_scalars(count - 1)?;
        Ok([vec![claim + eq_factor * E::sum(tail.iter().copied())], tail].concat())
    }

    /// Nothing of the proof is left unread. Returns every query's path, in the order they were opened.
    pub fn finish(self) -> Result<Vec<MerklePath>, VerifierError> {
        require(
            self.stream_offset == self.proof.stream.len(),
            VerifierError::StreamNotConsumed,
        )?;
        require(
            self.opening_offset == self.proof.merkle_openings.len(),
            VerifierError::MerkleNotConsumed,
        )?;
        Ok(self.paths)
    }
}

pub fn sumcheck(
    transcript: &mut Transcript,
    mut claim: E,
    count: usize,
    equalities: &[Option<E>],
) -> Result<(Vec<E>, E), VerifierError> {
    let mut point = Vec::with_capacity(equalities.len());
    for &equality in equalities {
        let message = transcript.sumcheck_round_poly(count, claim, equality)?;
        let challenge = transcript.sample();
        point.push(challenge);
        claim = poly_eval(&message, challenge);
    }
    Ok((point, claim))
}
