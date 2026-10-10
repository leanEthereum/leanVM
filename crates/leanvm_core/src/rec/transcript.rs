//! The byte duplex replayed on constrained words, with the same buffering and output cursor.

use super::circuit::{Builder, Dw, Ew, Kw, Limbs, PARAM_IV, digest_limbs, zero_prefix};
use fiat_shamir::transcript::RawProof;
use fiat_shamir::{
    COMMIT, MAX_GRINDING_BITS, MAX_SQUEEZE_BYTES, NONCE, OUTPUT, POW_BASE, POW_TAG, SEED, TranscriptContext,
    absorb_tweak,
};
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
pub struct MerkleOpening {
    /// The leaf's words.
    pub image: Vec<u64>,
    /// The siblings, lowest first.
    pub path: Vec<Limbs>,
}

/// A constrained chaining value, bounded input/output buffers, and the proof's transport cursors.
#[derive(Debug)]
pub struct Transcript<'a> {
    cv: Dw,
    pending: [Kw; 8],
    n_pending: usize,
    first: bool,
    previous: u64,
    squeezed: u64,
    output: [Kw; 4],
    source: ProofSource<'a>,
    offset: usize,
    opening: usize,
}

impl<'a> Transcript<'a> {
    /// Bind the domain digest and statement digest using the duplex's distinguished seed node.
    pub fn new(b: &mut Builder, iv: Dw, public_input: (Ew, Kw), source: ProofSource<'a>) -> Self {
        let d = b.d_to_k(iv);
        let p = b.e_to_k(public_input.0);
        let initial = b.d_const(PARAM_IV);
        let cv = b.leaf_block(
            initial,
            [d[0], d[1], d[2], d[3], p[0], p[1], p[2], public_input.1],
            SEED,
            true,
        );
        let zero = b.k_const(0);
        Self {
            cv,
            pending: [zero; 8],
            n_pending: 0,
            first: true,
            previous: 0,
            squeezed: 0,
            output: [zero; 4],
            source,
            offset: 0,
            opening: 0,
        }
    }

    /// A labeled protocol with the zero statement digest, as in the native duplex.
    pub fn from_label(b: &mut Builder, label: &[u8], source: ProofSource<'a>) -> Self {
        let domain = b.d_const(digest_limbs(&primitives::hash::hash(label)));
        let zero_e = b.e_const(F192::ZERO);
        let zero_k = b.k_const(0);
        Self::new(b, domain, (zero_e, zero_k), source)
    }

    /// Capture the logical duplex state without emitting rows or changing either transport cursor.
    ///
    /// Only live input words are included. As in the native duplex, the output buffer is a derivable cache for privately constructed valid states, not independent logical state.
    pub fn context(&self) -> TranscriptContext<Kw, Dw> {
        let mut pending = [None; 8];
        for (slot, &word) in pending.iter_mut().zip(&self.pending[..self.n_pending]) {
            *slot = Some(word);
        }
        TranscriptContext {
            state: self.cv,
            pending,
            pending_bytes: self.n_pending * 8,
            first: self.first,
            previous: self.previous,
            squeezed: self.squeezed,
        }
    }

    /// A terminal commitment to the complete transcript, including consumed output bytes.
    pub fn commitment(&self, b: &mut Builder) -> Dw {
        let cv = if self.n_pending == 0 {
            self.cv
        } else {
            let mut block = self.pending;
            block[self.n_pending..].fill(b.k_const(0));
            let tweak = absorb_tweak(self.first, true, self.n_pending * 8, self.previous);
            b.leaf_block(self.cv, block, tweak, true)
        };
        let zero = b.k_const(0);
        let mut block = [zero; 8];
        block[0] = b.k_const(self.squeezed);
        b.leaf_block(cv, block, COMMIT, true)
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

    fn flush(&mut self, b: &mut Builder, last: bool) {
        if self.n_pending == 0 {
            return;
        }
        let mut block = self.pending;
        block[self.n_pending..].fill(b.k_const(0));
        let tweak = absorb_tweak(self.first, last, self.n_pending * 8, self.previous);
        self.cv = b.leaf_block(self.cv, block, tweak, true);
        self.n_pending = 0;
        self.first = last;
        self.previous = 0;
    }

    /// Absorb the scalar's three words, retaining the final full input block until a mode switch.
    pub fn observe(&mut self, b: &mut Builder, x: Ew) {
        if self.squeezed != 0 {
            self.previous = self.squeezed;
            self.squeezed = 0;
        }
        for word in b.e_to_k(x) {
            if self.n_pending == 8 {
                self.flush(b, false);
            }
            self.pending[self.n_pending] = word;
            self.n_pending += 1;
        }
    }

    /// The next scalar of the stream, bound into the transcript.
    pub fn next_scalar(&mut self, b: &mut Builder) -> Ew {
        let x = self.take(b);
        self.observe(b, x);
        x
    }

    /// Consume three output words, including any unused suffix of the previous output block.
    pub fn sample(&mut self, b: &mut Builder) -> Ew {
        assert!(
            24 <= MAX_SQUEEZE_BYTES - self.squeezed,
            "squeeze request exceeds cursor"
        );
        self.flush(b, true);
        let mut result = [b.k_const(0); 3];
        for word in &mut result {
            let offset = (self.squeezed % 32 / 8) as usize;
            if offset == 0 {
                let mut block = [b.k_const(0); 8];
                block[0] = b.k_const(self.squeezed / 32);
                let digest = b.leaf_block(self.cv, block, OUTPUT, true);
                self.output = b.d_to_k(digest);
            }
            *word = self.output[offset];
            self.squeezed += 8;
        }
        b.k_to_e(result)
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
    /// The PoW base binds the pending input, output cursor, and difficulty, without consuming challenges.
    ///
    /// # Panics
    ///
    /// Panics if the grinding exceeds the digest's low word, as the native check does.
    pub fn grind_check(&mut self, b: &mut Builder, bits: u32) {
        assert!(bits <= MAX_GRINDING_BITS, "grinding past the digest's low word");
        self.flush(b, true);
        let nonce = self.take(b);
        if bits == 0 {
            b.eq_e_const(nonce, F192::ZERO);
        } else {
            let mut block = [b.k_const(0); 8];
            block[0] = b.k_const(self.squeezed);
            block[1] = b.k_const(u64::from(bits));
            let base = b.leaf_block(self.cv, block, POW_BASE, true);
            let nonce_tag = b.k_const(POW_TAG);
            let (digest, _) = b.compress(base, nonce, nonce_tag);
            let [word, ..] = b.d_to_k(digest);
            for bit in b.split(word).into_iter().take(bits as usize) {
                b.eq_k_const(bit, 0);
            }
        }
        let mut block = [b.k_const(0); 8];
        block[..3].copy_from_slice(&b.e_to_k(nonce));
        block[3] = b.k_const(self.squeezed);
        block[4] = b.k_const(u64::from(bits));
        self.cv = b.leaf_block(self.cv, block, NONCE, true);
        self.squeezed = 0;
    }

    /// The next query's opening, its image padded with zeros to `leaf_words` and its path cut or padded to `depth` siblings.
    fn next_opening(&mut self, leaf_words: usize, depth: usize) -> MerkleOpening {
        let opening = match self.source {
            ProofSource::Proof(p) => p.merkle.get(self.opening).map(|o| MerkleOpening {
                image: o.leaf_data.iter().map(|w| w.0).collect(),
                path: o.path.iter().map(digest_limbs).collect(),
            }),
            ProofSource::Shape => None,
        };
        self.opening += 1;
        let mut opening = opening.unwrap_or(MerkleOpening {
            image: Vec::new(),
            path: Vec::new(),
        });
        opening.image.resize(leaf_words, 0);
        opening.path.resize(depth, [0; 4]);
        opening
    }

    /// Hash one query's row up its path's lowest `bits.len()` levels, returning the node reached and the row's words.
    ///
    /// The leaf image ends with the row, every word before it zero.
    /// It is hashed from the shared state of its whole zero blocks, then up the path.
    /// The direction at each level is the query's bit there, lowest first.
    /// The caller ties the node to the root, so that every leaf sits at the tree's height, which the shape fixes.
    ///
    /// # Why the height is the shape's
    ///
    /// - A one-block leaf and a node are one compression from the parameter IV at counter 64.
    /// - So the root of a tree is also the root of the tree one level shorter whose leaves are node preimages.
    /// - Only the path's length tells them apart: the levels must number the tree's height.
    ///
    /// # Panics
    ///
    /// Panics if the leaf is not whole blocks of eight words, or the row is longer than it.
    pub fn open_row(&mut self, b: &mut Builder, bits: &[Kw], row_words: usize, leaf_words: usize) -> (Dw, Vec<Kw>) {
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
        (h, words[prefix - zero_blocks * 8..].to_vec())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rec::circuit::{Circuit, Unsatisfied};
    use crate::rec::verifier::Rows;
    use fiat_shamir::Duplex;
    use fiat_shamir::merkle::{Hash, RawMerklePath, hash_leaf, hash_pair};
    use fiat_shamir::transcript::{Challenger, ProverState, Transmitter};
    use pcs::verifier::OpeningVerifier;
    use primitives::field::F64;

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

    #[test]
    fn rows_preserve_long_runs_partial_blocks_and_nonce_resets() {
        const RUNS: [(usize, usize); 7] = [(0, 1), (1, 2), (2, 3), (3, 4), (8, 5), (9, 17), (17, 65)];
        let mut native = Duplex::from_label(LABEL);
        let mut raw = RawProof {
            stream: Vec::new(),
            merkle: Vec::new(),
        };
        let mut expected = Vec::new();
        for (stage, (absorbed, sampled)) in RUNS.into_iter().enumerate() {
            for i in 0..absorbed {
                let value = F192::new((stage * 100 + i) as u64, i as u64, stage as u64);
                native.observe(value);
                raw.stream.push(value);
            }
            expected.extend(native.sample_vec(sampled));
            if stage == 3 {
                assert!(native.verify_pow_field(F192::ZERO, 0));
                raw.stream.push(F192::ZERO);
            }
        }
        let replay = |source, capture| {
            let mut b = Builder::new();
            let mut transcript = Transcript::from_label(&mut b, LABEL, source);
            let mut challenges = Vec::new();
            if capture {
                let _ = Rows::new(&mut b, &mut transcript).context();
            }
            for (stage, (absorbed, sampled)) in RUNS.into_iter().enumerate() {
                for _ in 0..absorbed {
                    transcript.next_scalar(&mut b);
                    if capture {
                        let _ = Rows::new(&mut b, &mut transcript).context();
                    }
                }
                for _ in 0..sampled {
                    let challenge = transcript.sample(&mut b);
                    challenges.push(b.e(challenge));
                    if capture {
                        let _ = Rows::new(&mut b, &mut transcript).context();
                    }
                }
                if stage == 3 {
                    transcript.grind_check(&mut b, 0);
                    if capture {
                        let _ = Rows::new(&mut b, &mut transcript).context();
                    }
                }
            }
            assert!(transcript.finished());
            let commitment = transcript.commitment(&mut b);
            let commitment = b.d(commitment);
            (b.finish(), challenges, commitment)
        };
        let (plain, reference, reference_commitment) = replay(ProofSource::Proof(&raw), false);
        let (rows, actual, commitment) = replay(ProofSource::Proof(&raw), true);
        assert_eq!(rows.circuit, plain.circuit);
        assert_eq!(actual, reference);
        assert_eq!(commitment, reference_commitment);
        assert_eq!(actual, expected);
        assert_eq!(commitment, native.commitment().map(|word| word.0));
        assert!(rows.failures.is_empty(), "{:?}", rows.failures);
        assert_eq!(rows.circuit, replay(ProofSource::Shape, true).0.circuit);
        assert_eq!(rows.circuit, replay(ProofSource::Shape, false).0.circuit);
    }

    // The native transcript above, in rows: the claims are the sums the scalars read make.
    fn replay(source: ProofSource<'_>) -> (Circuit, Vec<F192>, Vec<Unsatisfied>) {
        let mut b = Builder::new();
        let mut t = Transcript::from_label(&mut b, LABEL, source);
        let scalars: Vec<Ew> = (0..2).map(|_| t.next_scalar(&mut b)).collect();
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

    // Opens one row of eight words at index 0 of a tree of the given depth, returning the rows' failures.
    fn open(leaf: &[u64; 8], path: &[Hash], root: &Hash, depth: usize) -> Vec<Unsatisfied> {
        let raw = RawProof {
            stream: Vec::new(),
            merkle: vec![RawMerklePath {
                leaf_index: 0,
                leaf_data: leaf.map(F64).to_vec(),
                path: path.to_vec(),
            }],
        };
        let mut b = Builder::new();
        let root = b.d_const(digest_limbs(root));
        let bits = vec![b.k_const(0); depth];
        let (node, _) = Transcript::from_label(&mut b, LABEL, ProofSource::Proof(&raw)).open_row(&mut b, &bits, 8, 8);
        b.eq_d(node, root);
        b.finish().failures
    }

    #[test]
    fn a_node_opened_as_a_leaf_is_refused_at_the_shapes_depth() {
        // Four one-block leaves under a root of depth two.
        let words = |i: u64| -> [u64; 8] { std::array::from_fn(|j| 8 * i + j as u64) };
        let bytes = |w: [u64; 8]| -> Vec<u8> { w.iter().flat_map(|x| x.to_le_bytes()).collect() };
        let leaves: Vec<Hash> = (0..4).map(|i| hash_leaf(&bytes(words(i)))).collect();
        let nodes = [hash_pair(&leaves[0], &leaves[1]), hash_pair(&leaves[2], &leaves[3])];
        let root = hash_pair(&nodes[0], &nodes[1]);
        assert!(open(&words(0), &[leaves[1], nodes[1]], &root, 2).is_empty());

        // The first node's preimage, its children's digests, is a one-block leaf of the same hash.
        let preimage: [u64; 8] = std::array::from_fn(|j| digest_limbs(&leaves[j / 4])[j % 4]);
        assert!(open(&preimage, &[nodes[1]], &root, 1).is_empty());
        assert!(!open(&preimage, &[nodes[1]], &root, 2).is_empty());
    }
}
