//! Proof transport and Fiat-Shamir.

use crate::field::{E, K, ZERO};
use crate::hash::{Digest, STATE_LANES, keccak_f};
use crate::merkle::MerklePath;
use crate::multilinear::{log2_strict, poly_eval};
use crate::{VerifierError, require};

/// The scalar stream, and the Merkle openings: one phase per commitment opened, each query's path in the order the
/// verifier samples them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
    pub stream: Vec<E>,
    pub merkle_openings: Vec<Vec<MerklePath>>,
}

const DS_OBSERVE: u64 = 1;
pub(crate) const DS_POW_NONCE: u64 = 4;
/// Scalars that wait to be absorbed: four, a scalar taking four rate lanes, its two limbs, a zero lane and a tag.
const RATE_SCALARS: usize = 4;

/// A duplex sponge over Keccak-f\[1600\], in overwrite mode. The rate is lanes 0..16 and the capacity lanes
/// 16..25. A permutation writes waiting scalar `i` over lanes `4i..4i+4`, zeroes the rest of the rate and keeps the
/// capacity. A fifth scalar, or a challenge, permutes what waits, and every challenge takes a permutation of its own.
#[derive(Clone, Debug)]
pub struct Sponge {
    state: [u64; STATE_LANES],
    pending: [(E, u64); RATE_SCALARS],
    n_pending: usize,
    /// The challenge a grind's permutation drew, which the next [`Self::sample`] returns.
    ground: Option<E>,
}

impl Sponge {
    /// One permutation of the IV and the public input, from the zero state.
    pub fn new(fiat_shamir_iv: Digest, public_input: Digest) -> Self {
        let mut state = [0u64; STATE_LANES];
        state[..4].copy_from_slice(&fiat_shamir_iv.words());
        state[4..8].copy_from_slice(&public_input.words());
        Self {
            state: {
                keccak_f(&mut state);
                state
            },
            pending: [(ZERO, 0); RATE_SCALARS],
            n_pending: 0,
            ground: None,
        }
    }

    fn duplex(&mut self) {
        let mut input = self.state;
        input[..16].fill(0);
        for (i, &(value, tag)) in self.pending[..self.n_pending].iter().enumerate() {
            input[4 * i..4 * i + 4].copy_from_slice(&[value.c0, value.c1, 0, tag]);
        }
        keccak_f(&mut input);
        self.state = input;
        self.n_pending = 0;
    }

    pub(crate) fn absorb(&mut self, value: E, tag: u64) {
        assert!(self.ground.is_none(), "a grind is followed by a challenge");
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
        self.ground.take().unwrap_or_else(|| {
            self.duplex();
            E::new(self.state[0], self.state[1])
        })
    }

    /// Absorb a grinding nonce and permute: the output's first two lanes are the next challenge, kept for
    /// [`Self::sample`], and its third lane is returned, the proof of work.
    pub(crate) fn absorb_nonce(&mut self, nonce: E) -> u64 {
        self.absorb(nonce, DS_POW_NONCE);
        self.duplex();
        self.ground = Some(E::new(self.state[0], self.state[1]));
        self.state[2]
    }
}

/// Round-by-round target (bits): every verifier message's error, after its grind, is at most `2^-SECURITY_BITS`.
pub const SECURITY_BITS: u32 = 125;

/// The grind before a verifier message whose round-by-round error is `numerator / |E|`, `|E| = 2^128`: the fewest
/// bits that bring it to `2^-SECURITY_BITS` (`fiat_shamir::grinding_bits`).
pub const fn grinding_bits(numerator: u128) -> u32 {
    let log = if numerator <= 1 {
        0
    } else {
        u128::BITS - (numerator - 1).leading_zeros()
    };
    log.saturating_sub(128 - SECURITY_BITS)
}

pub struct Transcript<'a> {
    proof: &'a Proof,
    sponge: Sponge,
    stream_offset: usize,  // in E field elements
    opening_offset: usize, // in phases
    checked: bool,         // false for a replay, which walks the proof and checks none of it
}

impl<'a> Transcript<'a> {
    pub fn new(proof: &'a Proof, fiat_shamir_iv: Digest, public_input: Digest, checked: bool) -> Self {
        Self {
            proof,
            sponge: Sponge::new(fiat_shamir_iv, public_input),
            stream_offset: 0,
            opening_offset: 0,
            checked,
        }
    }

    /// Whether the proof's checks run. Every one a replay skips is behind this, and nothing else is but
    /// work only a check reads.
    pub fn checked(&self) -> bool {
        self.checked
    }

    pub fn sample(&mut self) -> E {
        self.sponge.sample()
    }

    /// How many scalars of the stream have been read.
    pub fn stream_offset(&self) -> usize {
        self.stream_offset
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

    /// The nonce is absorbed with its own tag, and the permutation that draws the next challenge must leave its third
    /// lane with the low `bits` bits zero. A grind of zero bits is nothing: no nonce, no permutation.
    pub fn grind_check(&mut self, bits: u32) -> Result<(), VerifierError> {
        if bits == 0 {
            return Ok(());
        }
        let nonce = self.next()?;
        let pow = self.sponge.absorb_nonce(nonce);
        if self.checked {
            let mask = 1u64.checked_shl(bits).map_or(u64::MAX, |bit| bit - 1);
            require(pow & mask == 0, VerifierError::GrindingNonce)?;
        }
        Ok(())
    }

    /// The leaf images at `queries`, authenticated against `root`.
    ///
    /// The paths' positions and sizes must be the protocol's, which is reading the proof, as the stream's length is,
    /// so a replay refuses paths that differ too.
    pub fn merkle(
        &mut self,
        root: Digest,
        block_length: u64,
        queries: &[u64],
        leaf_words: usize,
    ) -> Result<Vec<&'a [K]>, VerifierError> {
        let height = log2_strict(block_length)?;
        let paths = self
            .proof
            .merkle_openings
            .get(self.opening_offset)
            .ok_or(VerifierError::MerkleOpeningMissing)?;
        self.opening_offset += 1;
        require(
            paths
                .iter()
                .all(|path| path.leaf.len() == leaf_words && path.siblings.len() == height),
            VerifierError::MerkleOpeningShape,
        )?;
        require(
            paths.iter().map(|path| path.leaf_index).eq(queries.iter().copied()),
            VerifierError::MerkleOpeningPosition,
        )?;
        require(
            !self.checked || paths.iter().all(|path| path.root() == root),
            VerifierError::MerkleRootMismatch,
        )?;
        Ok(paths.iter().map(|path| &path.leaf[..]).collect())
    }

    /// returns q(X) := c0 + c1X + c2X^2 + ..., after the round's grind: the round's error is the degree of the whole
    /// round polynomial, eq factor included, over `|E|`.
    pub fn sumcheck_round_poly(
        &mut self,
        count: usize,
        claim: E,
        eq_factor: Option<E>,
    ) -> Result<Vec<E>, VerifierError> {
        let poly = match eq_factor {
            // `q(0) + q(1) == claim`. The transcript contains c0, c2, c3 ...
            None => {
                let constant = self.next_scalar()?;
                let tail = self.next_scalars(count - 2)?;
                [vec![constant, claim + E::sum(tail.iter().copied())], tail].concat()
            }
            // `(1 + r) q(0) + r q(1) == claim`. The transcript contains c1, c2, c3 ... (r := eq_factor)
            Some(eq_factor) => {
                let tail = self.next_scalars(count - 1)?;
                [vec![claim + eq_factor * E::sum(tail.iter().copied())], tail].concat()
            }
        };
        self.grind_check(grinding_bits((count - 1 + usize::from(eq_factor.is_some())) as u128))?;
        Ok(poly)
    }

    /// Nothing of the proof is left unread.
    pub fn finish(self) -> Result<(), VerifierError> {
        require(
            self.stream_offset == self.proof.stream.len(),
            VerifierError::StreamNotConsumed,
        )?;
        require(
            self.opening_offset == self.proof.merkle_openings.len(),
            VerifierError::MerkleNotConsumed,
        )
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
