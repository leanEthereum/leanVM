//! A Fiat-Shamir transcript replayed in rows: every absorb and squeeze is a hash row on the wires it binds.

use super::circuit::{Builder, Dw, Ew, Kw, Limbs, digest_limbs, zero_prefix};
use fiat_shamir::transcript::RawProof;
use fiat_shamir::{DS_OBSERVE, DS_POW_BASE, DS_POW_NONCE, DS_SQUEEZE};
use primitives::field::F192;

/// What the circuit reads: the proof when it has one, zeros when it is built from the shape alone.
///
/// The rows never depend on what is read, so both sources give one circuit.
#[derive(Clone, Copy, Debug)]
pub enum ProofSource<'a> {
    /// The proof, as its native verifier read it.
    Proof(&'a RawProof),
    /// No proof: every scalar and opening is zero.
    Shape,
}

/// One Merkle opening as the circuit reads it: the leaf's image and the sibling path.
#[derive(Clone, Debug)]
pub struct Opening {
    /// The leaf's words.
    pub image: Vec<u64>,
    /// The siblings, lowest first.
    pub path: Vec<Limbs>,
}

/// The transcript's chaining value as a wire, and where the proof is read.
#[derive(Debug)]
pub struct Transcript<'a> {
    cv: Dw,
    source: ProofSource<'a>,
    offset: usize,
    opening: usize,
}

impl<'a> Transcript<'a> {
    /// The transcript seeded by `compress(iv, public_input)`, the input's first three words as `E`, its fourth as `K`.
    pub fn new(b: &mut Builder, iv: Dw, public_input: (Ew, Kw), source: ProofSource<'a>) -> Self {
        let (cv, _) = b.compress(iv, public_input.0, public_input.1);
        Self::from_state(cv, source)
    }

    /// A transcript whose chaining value is already `cv`.
    pub const fn from_state(cv: Dw, source: ProofSource<'a>) -> Self {
        Self {
            cv,
            source,
            offset: 0,
            opening: 0,
        }
    }

    /// The chaining value.
    pub const fn state(&self) -> Dw {
        self.cv
    }

    /// Whether every scalar and opening of the proof was read.
    pub const fn finished(&self) -> bool {
        match self.source {
            ProofSource::Proof(p) => self.offset == p.stream.len() && self.opening == p.merkle.len(),
            ProofSource::Shape => true,
        }
    }

    /// The next scalar of the stream as a free wire, unbound.
    fn take(&mut self, b: &mut Builder) -> Ew {
        let v = match self.source {
            ProofSource::Proof(p) => p.stream.get(self.offset).copied().unwrap_or(F192::ZERO),
            ProofSource::Shape => F192::ZERO,
        };
        self.offset += 1;
        b.free_e(v)
    }

    fn absorb(&mut self, b: &mut Builder, x: Ew, ds: u64) {
        let ds = b.k_const(ds);
        self.cv = b.compress(self.cv, x, ds).0;
    }

    /// Absorb `x`.
    pub fn observe(&mut self, b: &mut Builder, x: Ew) {
        self.absorb(b, x, DS_OBSERVE.0);
    }

    /// The next scalar of the stream, bound into the transcript.
    pub fn next_scalar(&mut self, b: &mut Builder) -> Ew {
        let x = self.take(b);
        self.observe(b, x);
        x
    }

    /// The next `n` scalars, each bound.
    pub fn next_scalars(&mut self, b: &mut Builder, n: usize) -> Vec<Ew> {
        (0..n).map(|_| self.next_scalar(b)).collect()
    }

    /// A challenge: the first three words of `compress(cv, (0, 0, 0, SQUEEZE))`, whose output becomes the state.
    pub fn sample(&mut self, b: &mut Builder) -> Ew {
        let zero = b.zero();
        let ds = b.k_const(DS_SQUEEZE.0);
        let (cv, ch) = b.compress(self.cv, zero, ds);
        self.cv = cv;
        ch
    }

    /// `n` challenges.
    pub fn sample_vec(&mut self, b: &mut Builder, n: usize) -> Vec<Ew> {
        (0..n).map(|_| self.sample(b)).collect()
    }

    /// A Merkle root as its two 128-bit halves, each bound, their top limbs zero.
    pub fn next_root(&mut self, b: &mut Builder) -> Dw {
        let lo = self.next_scalar(b);
        let hi = self.next_scalar(b);
        b.halves_to_d(lo, hi)
    }

    /// A sumcheck round's coefficients, constant first.
    ///
    /// Every coefficient but the one the claim fixes is read, then bound in index order.
    /// With an eq weight `r` the claim fixes the constant: `c_0 = claim + r·sum_{i>=1} c_i`.
    /// Without, it fixes the linear coefficient: `c_1 = claim + sum_{i>=2} c_i`.
    pub fn next_round_poly(&mut self, b: &mut Builder, n_coeffs: usize, claim: Ew, eq: Option<Ew>) -> Vec<Ew> {
        let fixed = usize::from(eq.is_none());
        let mut coeffs: Vec<Ew> = (0..n_coeffs)
            .map(|i| if i == fixed { claim } else { self.take(b) })
            .collect();
        let tail = b.sum(&coeffs[fixed + 1..]);
        coeffs[fixed] = match eq {
            None => b.add(claim, tail),
            Some(r) => b.mul_add(r, tail, claim),
        };
        for (i, &c) in coeffs.iter().enumerate() {
            if i != fixed {
                self.observe(b, c);
            }
        }
        coeffs
    }

    /// A grinding nonce: its proof of work checked, then bound.
    ///
    /// The check holds the low `bits` bits of `compress(base, (nonce, POW_NONCE))` to zero.
    /// A digest word has 64 bits, so more than 63 is a failure of the circuit.
    pub fn grind_check(&mut self, b: &mut Builder, bits: u32) {
        let nonce = self.take(b);
        if bits == 0 {
            b.eq_e_const(nonce, F192::ZERO);
        } else {
            if bits >= 64 {
                b.fail("grinding past the digest's low word");
            }
            let zero = b.zero();
            let base_tag = b.k_const(DS_POW_BASE.0);
            let (base, _) = b.compress(self.cv, zero, base_tag);
            let nonce_tag = b.k_const(DS_POW_NONCE.0);
            let (digest, _) = b.compress(base, nonce, nonce_tag);
            let [word, ..] = b.d_to_k(digest);
            for bit in b.split(word).into_iter().take(bits as usize) {
                b.eq_k_const(bit, 0);
            }
        }
        self.absorb(b, nonce, DS_POW_NONCE.0);
    }

    /// The next query's opening, its image and path padded with zeros to the given lengths.
    fn next_opening(&mut self, leaf_words: usize, depth: usize) -> Opening {
        let opening = match self.source {
            ProofSource::Proof(p) => p.merkle.get(self.opening).map(|o| Opening {
                image: o.leaf_data.iter().map(|w| w.0).collect(),
                path: o.path.iter().map(digest_limbs).collect(),
            }),
            ProofSource::Shape => None,
        };
        self.opening += 1;
        let mut opening = opening.unwrap_or(Opening {
            image: Vec::new(),
            path: Vec::new(),
        });
        opening.image.resize(leaf_words, 0);
        opening.path.resize(depth, [0; 4]);
        opening
    }

    /// Authenticate one query's row against a root and return the row's words.
    ///
    /// The leaf image ends with the row, every word before it zero.
    /// It is hashed from the shared state of its whole zero blocks, then up the path.
    /// The direction at each level is the query's bit there, lowest first.
    ///
    /// # Panics
    ///
    /// Panics if the leaf is not whole blocks of eight words, or the row is longer than it.
    pub fn open_row(&mut self, b: &mut Builder, root: Dw, bits: &[Kw], row_words: usize, leaf_words: usize) -> Vec<Kw> {
        assert!(
            leaf_words.is_multiple_of(8) && row_words <= leaf_words,
            "a leaf of whole blocks holds the row"
        );
        let opening = self.next_opening(leaf_words, bits.len());
        let prefix = leaf_words - row_words;
        let zero_blocks = prefix / 8;
        let mut h = b.d_const(zero_prefix(zero_blocks));
        let zero = b.k_const(0);
        let words: Vec<Kw> = (zero_blocks * 8..leaf_words)
            .map(|i| if i < prefix { zero } else { b.free_k(opening.image[i]) })
            .collect();
        let n_blocks = leaf_words / 8;
        for (j, m) in words.as_chunks::<8>().0.iter().enumerate() {
            let index = zero_blocks + j;
            h = b.leaf_block(h, *m, 64 * (index as u64 + 1), index + 1 == n_blocks);
        }
        for (&bit, sibling) in bits.iter().zip(&opening.path) {
            h = b.node(h, bit, *sibling);
        }
        b.eq_d(h, root);
        words[prefix - zero_blocks * 8..].to_vec()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rec::circuit::Circuit;
    use fiat_shamir::transcript::{Challenger, ProverState, Transmitter};

    const LABEL: &[u8] = b"rec-transcript-test";
    const POLY: [F192; 4] = [
        F192::new(5, 0, 0),
        F192::new(6, 1, 0),
        F192::new(7, 0, 9),
        F192::new(8, 8, 8),
    ];

    fn native() -> (RawProof, [F192; 3]) {
        let mut ps = ProverState::from_label(LABEL);
        ps.add_scalars(&[F192::new(1, 2, 3), F192::new(u64::MAX, 7, 0)]);
        let c0 = ps.sample();
        ps.add_round_poly(&POLY, false);
        let r = ps.sample();
        ps.add_round_poly(&POLY, true);
        ps.grind(6);
        let c1 = ps.sample();
        let proof = ps.into_proof();
        let raw = RawProof {
            stream: proof.stream,
            merkle: Vec::new(),
        };
        (raw, [c0, r, c1])
    }

    // The native transcript above, in rows: the claims are the sums the scalars read make.
    fn replay(source: ProofSource<'_>) -> (Circuit, Vec<F192>, Vec<String>) {
        let mut b = Builder::new();
        let iv = b.d_const(digest_limbs(&primitives::hash::hash(LABEL)));
        let mut t = Transcript::from_state(iv, source);
        let scalars = t.next_scalars(&mut b, 2);
        let c0 = t.sample(&mut b);
        // `g(0) + g(1)` of the honest polynomial, as a hint the round derives its linear coefficient from.
        let claim = b.free_e(match source {
            ProofSource::Proof(_) => POLY[0] + POLY[0] + POLY[1] + POLY[2] + POLY[3],
            ProofSource::Shape => F192::ZERO,
        });
        let first = t.next_round_poly(&mut b, 4, claim, None);
        let r = t.sample(&mut b);
        let claim = b.free_e(match source {
            ProofSource::Proof(_) => (F192::ONE + b.e(r)) * POLY[0] + b.e(r) * (POLY[0] + POLY[1] + POLY[2] + POLY[3]),
            ProofSource::Shape => F192::ZERO,
        });
        let second = t.next_round_poly(&mut b, 4, claim, Some(r));
        t.grind_check(&mut b, 6);
        let c1 = t.sample(&mut b);
        assert!(t.finished());
        let values = (scalars.iter().chain(&first).chain(&second).chain(&[c0, r, c1]))
            .map(|&w| b.e(w))
            .collect();
        let finished = b.finish();
        (finished.circuit, values, finished.failures)
    }

    #[test]
    fn the_circuit_replays_the_native_transcript() {
        let (raw, challenges) = native();
        let (_, values, failures) = replay(ProofSource::Proof(&raw));
        assert!(failures.is_empty(), "{failures:?}");
        assert_eq!(values[2..6], POLY);
        assert_eq!(values[6..10], POLY);
        assert_eq!(values[10..], challenges);
    }

    #[test]
    fn the_circuit_from_the_shape_is_the_circuit_from_the_proof() {
        let (raw, _) = native();
        assert_eq!(replay(ProofSource::Proof(&raw)).0, replay(ProofSource::Shape).0);
    }
}
