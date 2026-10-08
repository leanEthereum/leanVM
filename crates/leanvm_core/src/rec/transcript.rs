//! A Fiat-Shamir transcript replayed in rows: every absorb and squeeze is a hash row on the wires it binds.

use primitives::PrimeCharacteristicRing;

use super::circuit::{Builder, Dw, Ew, Kw, Limbs, digest_limbs, zero_prefix};
use fiat_shamir::transcript::RawProof;
use fiat_shamir::{DS_OBSERVE, DS_POW_BASE, DS_POW_NONCE, DS_SQUEEZE, MAX_GRINDING_BITS, MAX_PENDING};
use primitives::F192;

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

/// The transcript's chaining value as a wire, the scalars it has yet to absorb, and where the proof is read.
#[derive(Debug)]
pub struct Transcript<'a> {
    cv: Dw,
    pending: Vec<Ew>,
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
            pending: Vec::new(),
            source,
            offset: 0,
            opening: 0,
        }
    }

    /// The chaining value, once every pending scalar is absorbed.
    pub fn state(&mut self, b: &mut Builder) -> Dw {
        self.flush(b);
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

    /// Absorb the pending scalars, if any, in one step.
    fn flush(&mut self, b: &mut Builder) {
        if !self.pending.is_empty() {
            let pending = std::mem::take(&mut self.pending);
            self.cv = b.step(self.cv, &pending, DS_OBSERVE.to_bits()).0;
        }
    }

    /// Absorb `x`: it waits for the next step, which absorbs up to two scalars.
    pub fn observe(&mut self, b: &mut Builder, x: Ew) {
        if self.pending.len() == MAX_PENDING {
            self.flush(b);
        }
        self.pending.push(x);
    }

    /// The next scalar of the stream, bound into the transcript.
    pub fn next_scalar(&mut self, b: &mut Builder) -> Ew {
        let x = self.take(b);
        self.observe(b, x);
        x
    }

    /// A challenge: the first three words of the step absorbing the pending scalars under `SQUEEZE`, whose output becomes the state.
    pub fn sample(&mut self, b: &mut Builder) -> Ew {
        let pending = std::mem::take(&mut self.pending);
        let (cv, ch) = b.step(self.cv, &pending, DS_SQUEEZE.to_bits());
        self.cv = cv;
        ch
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
    /// The pending scalars are absorbed first. The check holds the low `bits` bits of `compress(base, (nonce, POW_NONCE))` to zero, `base` the `POW_BASE` step's output.
    ///
    /// # Panics
    ///
    /// Panics if the grinding exceeds the digest's low word, as the native check does.
    pub fn grind_check(&mut self, b: &mut Builder, bits: u32) {
        assert!(bits <= MAX_GRINDING_BITS, "grinding past the digest's low word");
        self.flush(b);
        let nonce = self.take(b);
        if bits == 0 {
            b.eq_e_const(nonce, F192::ZERO);
        } else {
            let (base, _) = b.step(self.cv, &[], DS_POW_BASE.to_bits());
            let nonce_tag = b.k_const(DS_POW_NONCE.to_bits());
            let (digest, _) = b.compress(base, nonce, nonce_tag);
            let [word, ..] = b.d_to_k(digest);
            for bit in b.split(word).into_iter().take(bits as usize) {
                b.eq_k_const(bit, 0);
            }
        }
        self.cv = b.step(self.cv, &[nonce], DS_POW_NONCE.to_bits()).0;
    }

    /// The next query's opening, its image padded with zeros to `leaf_words` and its path cut or padded to `depth` siblings.
    fn next_opening(&mut self, leaf_words: usize, depth: usize) -> MerkleOpening {
        let opening = match self.source {
            ProofSource::Proof(p) => p.merkle.get(self.opening).map(|o| MerkleOpening {
                image: o.leaf_data.iter().map(|w| w.to_bits()).collect(),
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
    use fiat_shamir::merkle::{Hash, RawMerklePath, hash_leaf, hash_pair};
    use fiat_shamir::transcript::{Challenger, ProverState, Transmitter};
    use primitives::F64;
    use primitives::PrimeCharacteristicRing;

    const LABEL: &[u8] = b"rec-transcript-test";
    const POLY: [F192; 4] = [
        F192::new([F64::new(5), F64::new(0), F64::new(0)]),
        F192::new([F64::new(6), F64::new(1), F64::new(0)]),
        F192::new([F64::new(7), F64::new(0), F64::new(9)]),
        F192::new([F64::new(8), F64::new(8), F64::new(8)]),
    ];

    fn native() -> (RawProof, [F192; 3]) {
        let mut ps = ProverState::from_label(LABEL);
        ps.add_scalars(&[
            F192::new([F64::new(1), F64::new(2), F64::new(3)]),
            F192::new([F64::new(u64::MAX), F64::new(7), F64::new(0)]),
        ]);
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
    fn replay(source: ProofSource<'_>) -> (Circuit, Vec<F192>, Vec<Unsatisfied>) {
        let mut b = Builder::new();
        let iv = b.d_const(digest_limbs(&primitives::hash::hash(LABEL)));
        let mut t = Transcript::from_state(iv, source);
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
                leaf_data: leaf.map(F64::new).to_vec(),
                path: path.to_vec(),
            }],
        };
        let mut b = Builder::new();
        let root = b.d_const(digest_limbs(root));
        let bits = vec![b.k_const(0); depth];
        let (node, _) = Transcript::from_state(root, ProofSource::Proof(&raw)).open_row(&mut b, &bits, 8, 8);
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
