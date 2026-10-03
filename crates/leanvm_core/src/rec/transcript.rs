//! The inner proof's transcript, replayed in the circuit: every absorb and squeeze is a hash row, so
//! the scalars hashed are the wires the arithmetic uses (`fiat_shamir::FiatShamirState`).

use super::circuit::{Builder, Dw, Ew, Kw, Limbs, tag};
use fiat_shamir::transcript::RawProof;
use primitives::field::F192;

/// What the circuit reads: the proof when it has one, zeros when it is built from the shape alone.
#[derive(Clone, Copy)]
pub enum Source<'a> {
    Proof(&'a RawProof),
    Shape,
}

/// One Merkle opening as the circuit reads it: the leaf's image and the sibling path.
pub struct Opening {
    pub image: Vec<u64>,
    pub path: Vec<Limbs>,
}

/// The transcript's chaining value as a wire, and where the proof is read.
pub struct Transcript<'a> {
    cv: Dw,
    source: Source<'a>,
    offset: usize,
    opening: usize,
}

fn digest_limbs(d: &[u8; 32]) -> Limbs {
    std::array::from_fn(|i| u64::from_le_bytes(d[8 * i..8 * i + 8].try_into().expect("eight bytes")))
}

impl<'a> Transcript<'a> {
    /// `compress(iv, public_input)`, the seed `FiatShamirState::new` takes, `public_input` given as an `E`
    /// element for its first three words and a `K` word for its fourth.
    pub fn new(b: &mut Builder, iv: Dw, public_input: (Ew, Kw), source: Source<'a>) -> Self {
        let (cv, _) = b.compress(iv, public_input.0, public_input.1);
        Self {
            cv,
            source,
            offset: 0,
            opening: 0,
        }
    }

    /// A transcript whose chaining value is already `cv`: a sub-protocol's, seeded by a label.
    pub const fn from_state(cv: Dw, source: Source<'a>) -> Self {
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
            Source::Proof(p) => self.offset == p.stream.len() && self.opening == p.merkle.len(),
            Source::Shape => true,
        }
    }

    fn take_raw(&mut self) -> F192 {
        let v = match self.source {
            Source::Proof(p) => p.stream.get(self.offset).copied().unwrap_or(F192::ZERO),
            Source::Shape => F192::ZERO,
        };
        self.offset += 1;
        v
    }

    fn absorb(&self, b: &mut Builder, x: Ew, ds: u64) -> Dw {
        let ds = b.k_const(ds);
        let (cv, _) = b.compress(self.cv, x, ds);
        cv
    }

    /// Absorb `x`.
    pub fn observe(&mut self, b: &mut Builder, x: Ew) {
        self.cv = self.absorb(b, x, tag::OBSERVE);
    }

    /// The next scalar of the stream, bound into the transcript.
    pub fn next_scalar(&mut self, b: &mut Builder) -> Ew {
        let v = self.take_raw();
        let x = b.free_e(v);
        self.observe(b, x);
        x
    }

    pub fn next_scalars(&mut self, b: &mut Builder, n: usize) -> Vec<Ew> {
        (0..n).map(|_| self.next_scalar(b)).collect()
    }

    /// A challenge: the first three words of `compress(cv, (0, 0, 0, SQUEEZE))`, which becomes the state.
    pub fn sample(&mut self, b: &mut Builder) -> Ew {
        let zero = b.zero();
        let ds = b.k_const(tag::SQUEEZE);
        let (cv, ch) = b.compress(self.cv, zero, ds);
        self.cv = cv;
        ch
    }

    pub fn sample_vec(&mut self, b: &mut Builder, n: usize) -> Vec<Ew> {
        (0..n).map(|_| self.sample(b)).collect()
    }

    /// A root as its two 128-bit halves, each bound, their top limbs zero.
    pub fn next_root(&mut self, b: &mut Builder) -> Dw {
        let lo = self.next_scalar(b);
        let hi = self.next_scalar(b);
        b.halves_to_d(lo, hi)
    }

    /// A sumcheck round's coefficients, constant first: every one but the one `claim` fixes is read, then
    /// bound in index order (`Receiver::next_round_poly`).
    pub fn next_round_poly(&mut self, b: &mut Builder, n_coeffs: usize, claim: Ew, eq: Option<Ew>) -> Vec<Ew> {
        let fixed = usize::from(eq.is_none());
        let mut coeffs: Vec<Option<Ew>> = vec![None; n_coeffs];
        for (i, c) in coeffs.iter_mut().enumerate() {
            if i != fixed {
                let v = self.take_raw();
                *c = Some(b.free_e(v));
            }
        }
        let sent = |from: usize| -> Vec<Ew> { coeffs[from..].iter().flatten().copied().collect() };
        let derived = match eq {
            None => {
                let mut terms = vec![claim];
                terms.extend(sent(2));
                b.sum(&terms)
            }
            Some(r) => {
                let tail = sent(1);
                let s = b.sum(&tail);
                b.mul_add(r, s, claim)
            }
        };
        coeffs[fixed] = Some(derived);
        let coeffs: Vec<Ew> = coeffs
            .into_iter()
            .map(|c| c.expect("every coefficient is set"))
            .collect();
        for (i, &c) in coeffs.iter().enumerate() {
            if i != fixed {
                self.observe(b, c);
            }
        }
        coeffs
    }

    /// A grinding nonce: its proof of work checked, then bound (`FiatShamirState::verify_pow_field`).
    pub fn grind_check(&mut self, b: &mut Builder, bits: u32) {
        let nonce_value = self.take_raw();
        let nonce = b.free_e(nonce_value);
        if bits == 0 {
            b.eq_e_const(nonce, F192::ZERO);
        } else {
            let zero = b.zero();
            let base_tag = b.k_const(tag::POW_BASE);
            let (base, _) = b.compress(self.cv, zero, base_tag);
            let nonce_tag = b.k_const(tag::POW_NONCE);
            let (digest, _) = b.compress(base, nonce, nonce_tag);
            let [word, ..] = b.d_to_k(digest);
            let low = b.split(word);
            for &bit in &low[..bits as usize] {
                b.eq_k_const(bit, 0);
            }
        }
        self.cv = self.absorb(b, nonce, tag::POW_NONCE);
    }

    /// The next query's opening: `leaf_words` words of image and `depth` siblings.
    pub fn next_opening(&mut self, leaf_words: usize, depth: usize) -> Opening {
        let opening = match self.source {
            Source::Proof(p) => p.merkle.get(self.opening).map(|o| Opening {
                image: o.leaf_data.iter().map(|w| w.0).collect(),
                path: o.path.iter().map(digest_limbs).collect(),
            }),
            Source::Shape => None,
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

    /// Authenticate one query's row against `root`: its leaf's image hashed from the shared zero prefix,
    /// then its path, the direction at each level the query's bit there, lowest first.
    ///
    /// Returns the row's words, the image less its zero prefix.
    pub fn open_row(&mut self, b: &mut Builder, root: Dw, bits: &[Kw], row_words: usize, leaf_words: usize) -> Vec<Kw> {
        let opening = self.next_opening(leaf_words, bits.len());
        let prefix = leaf_words - row_words;
        let zero_blocks = prefix / 8;
        let state = primitives::hash::zero_prefix_state(zero_blocks);
        let start: Limbs = std::array::from_fn(|i| u64::from(state[2 * i]) | (u64::from(state[2 * i + 1]) << 32));
        let mut h = b.d_const(start);
        let zero = b.k_const(0);
        let words: Vec<Kw> = (zero_blocks * 8..leaf_words)
            .map(|i| if i < prefix { zero } else { b.free_k(opening.image[i]) })
            .collect();
        let n_blocks = leaf_words / 8;
        for (j, block) in words.chunks(8).enumerate() {
            let index = zero_blocks + j;
            let m: [Kw; 8] = block.try_into().expect("whole blocks");
            h = b.leaf_block(h, m, 64 * (index as u64 + 1), index + 1 == n_blocks);
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
    use fiat_shamir::transcript::{Challenger, ProverState, Transmitter};

    /// The circuit's transcript draws the native one's challenges from the same stream.
    #[test]
    fn the_circuit_replays_the_native_transcript() {
        let label = b"rec-transcript-test";
        let mut ps = ProverState::from_label(label);
        let scalars = [F192::new(1, 2, 3), F192::new(u64::MAX, 7, 0)];
        ps.add_scalars(&scalars);
        let c0 = ps.sample();
        let poly = [
            F192::new(5, 0, 0),
            F192::new(6, 1, 0),
            F192::new(7, 0, 9),
            F192::new(8, 8, 8),
        ];
        ps.add_round_poly(&poly, false);
        let r = ps.sample();
        ps.add_round_poly(&poly, true);
        ps.grind(6);
        let c1 = ps.sample();
        let proof = ps.into_proof();
        let raw = RawProof {
            stream: proof.stream,
            merkle: Vec::new(),
        };

        let mut b = Builder::new();
        let iv = b.d_const(digest_limbs(&primitives::hash::hash(label)));
        let mut t = Transcript::from_state(iv, Source::Proof(&raw));
        t.next_scalars(&mut b, 2);
        let d0 = t.sample(&mut b);
        let claim = b.e_const(poly[0] + poly[0] + poly[1] + poly[2] + poly[3]);
        let got = t.next_round_poly(&mut b, 4, claim, None);
        let dr = t.sample(&mut b);
        let eq = b.e_const(r);
        let claim = b.e_const((F192::ONE + r) * poly[0] + r * (poly[0] + poly[1] + poly[2] + poly[3]));
        let got2 = t.next_round_poly(&mut b, 4, claim, Some(eq));
        t.grind_check(&mut b, 6);
        let d1 = t.sample(&mut b);
        assert!(t.finished());
        assert_eq!([b.e(d0), b.e(dr), b.e(d1)], [c0, r, c1]);
        assert_eq!(got.iter().map(|&w| b.e(w)).collect::<Vec<_>>(), poly);
        assert_eq!(got2.iter().map(|&w| b.e(w)).collect::<Vec<_>>(), poly);
        let (_, _, failures) = b.finish();
        assert!(failures.is_empty(), "{failures:?}");
    }
}
