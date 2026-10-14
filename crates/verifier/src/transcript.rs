//! Proof transport and Fiat-Shamir.

use crate::field::{E, K, ZERO};
use crate::hash::{Digest, STATE_LANES, sha3_hash, step};
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
const DS_POW_NONCE: u64 = 4;
/// Scalars that wait to be absorbed: four, a scalar taking four rate lanes, three limbs and a tag.
const RATE_SCALARS: usize = 4;

/// A duplex sponge over the VM's `SHA3` step, in overwrite mode. The rate is lanes 0..16 and the capacity lanes
/// 16..25. A permutation writes waiting scalar `i` over lanes `4i..4i+4`, zeroes the rest of the rate and keeps the
/// capacity. A fifth scalar, or a challenge, permutes what waits, and every challenge takes a permutation of its own.
#[derive(Clone, Debug)]
pub struct Sponge {
    state: [u64; STATE_LANES],
    pending: [(E, u64); RATE_SCALARS],
    n_pending: usize,
}

impl Sponge {
    /// One permutation of the IV and the public input, from the zero state.
    pub fn new(fiat_shamir_iv: Digest, public_input: Digest) -> Self {
        let mut state = [0u64; STATE_LANES];
        state[..4].copy_from_slice(&fiat_shamir_iv.words());
        state[4..8].copy_from_slice(&public_input.words());
        Self {
            state: step(&state),
            pending: [(ZERO, 0); RATE_SCALARS],
            n_pending: 0,
        }
    }

    /// A protocol with no public input of its own, seeded from `label` alone.
    pub fn from_label(label: &[u8]) -> Self {
        Self::new(sha3_hash(label), Digest([0; 32]))
    }

    fn duplex(&mut self) {
        let mut input = self.state;
        input[..16].fill(0);
        for (i, &(value, tag)) in self.pending[..self.n_pending].iter().enumerate() {
            input[4 * i..4 * i + 4].copy_from_slice(&[value.c0, value.c1, value.c2, tag]);
        }
        self.state = step(&input);
        self.n_pending = 0;
    }

    fn absorb(&mut self, value: E, tag: u64) {
        if self.n_pending == RATE_SCALARS {
            self.duplex();
        }
        self.pending[self.n_pending] = (value, tag);
        self.n_pending += 1;
    }

    pub fn observe(&mut self, value: E) {
        self.absorb(value, DS_OBSERVE);
    }

    pub fn sample(&mut self) -> E {
        self.duplex();
        E::new(self.state[0], self.state[1], self.state[2])
    }
}

pub struct Transcript<'a> {
    proof: &'a Proof,
    sponge: Sponge,
    stream_offset: usize,  // in E field elements
    opening_offset: usize, // in bytes, or in batches of the pruned form
    checked: bool,         // false for a replay, which walks the proof and checks none of it
    paths: Vec<MerklePath>,
}

impl<'a> Transcript<'a> {
    pub fn new(proof: &'a Proof, fiat_shamir_iv: Digest, public_input: Digest, checked: bool) -> Self {
        Self {
            proof,
            sponge: Sponge::new(fiat_shamir_iv, public_input),
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

    pub fn sample(&mut self) -> E {
        self.sponge.sample()
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
        self.sponge.observe(value);
        Ok(value)
    }

    pub fn next_scalars(&mut self, count: usize) -> Result<Vec<E>, VerifierError> {
        (0..count).map(|_| self.next_scalar()).collect()
    }

    /// The nonce is absorbed with its own tag, and the challenge drawn next, which nothing else uses, must have its low
    /// `bits` bits zero. With no bits to grind the nonce must be zero.
    pub fn grind_check(&mut self, bits: u32) -> Result<(), VerifierError> {
        let nonce = self.next()?;
        self.sponge.absorb(nonce, DS_POW_NONCE);
        let challenge = self.sample();
        if self.checked {
            let mask = 1u64.checked_shl(bits).map_or(u64::MAX, |bit| bit - 1);
            let valid = if bits == 0 {
                nonce == ZERO
            } else {
                challenge.c0 & mask == 0
            };
            require(valid, VerifierError::GrindingNonce)?;
        }
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
