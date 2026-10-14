//! The transcript in rows: the BLAKE2s duplex replayed on constrained words.
//!
//! It mirrors the native transcript call for call, with the same framing and the same output cursor.
//!
//! - A prover message is a free wire, absorbed as its words.
//! - A verifier message is squeezed words, each block of four an output row's.
//! - A hint is decoded natively, and only what it opens becomes wires.
//!
//! Every message the rows absorb is whole 64-bit words, so the native byte framing is a word framing here.

use super::circuit::{Builder, Compression, Dw, Ew, Kw, PARAM_IV, zero_prefix};
use fiat_shamir::{Blake2sDuplex, FromNarg, ProofOfWork, ProofTranscript, Role, SessionId};
use pcs::merkle::Openings;
use primitives::field::F192;

/// What the circuit reads: the proof when it has one, zeros when it is built from the shape alone.
///
/// The rows never depend on what is read, so both sources give one circuit.
#[derive(Clone, Copy, Debug)]
pub enum ProofSource<'a> {
    /// The proof the native verifier accepted, and every opening it authenticated, phase by phase.
    ///
    /// The openings are the hints decoded once, natively, so the rows never decode or hash them again.
    Proof(&'a ProofTranscript, &'a [Openings]),
    /// No proof: every message and opening is zero.
    Shape,
}

/// A row of a Merkle tree, opened in rows: its words, and the node its path reaches.
pub struct OpenedRow {
    /// The node the row's path reaches.
    pub node: Dw,
    /// The row's words.
    pub words: Vec<Kw>,
}

/// The duplex state in rows, and the cursors into the proof it reads.
#[derive(Debug)]
pub struct Transcript<'a> {
    /// The chaining value.
    cv: Dw,
    /// Absorbed words not yet compressed, at most one block.
    pending: [Kw; 8],
    /// Words of `pending` in use.
    n_pending: usize,
    /// Whether the next compressed block opens an absorb run.
    first: bool,
    /// The byte count of the squeeze run the current absorb run follows.
    previous: u64,
    /// Bytes squeezed in the current squeeze run, always whole words.
    squeezed: u64,
    /// The output block the next squeezed words come from.
    output: [Kw; 4],
    /// Where messages and hints come from.
    source: ProofSource<'a>,
    /// Message bytes read so far.
    narg_read: usize,
    /// The phase whose openings the rows hash, none when there is no such phase.
    openings: Option<&'a Openings>,
    /// Phases read so far.
    phases_read: usize,
    /// The next of the phase's openings to hash.
    next_opening: usize,
}

impl<'a> Transcript<'a> {
    /// A transcript for one session, its first message the instance's words.
    ///
    /// The session is fixed by the circuit, so the seed node is a constant and takes no row.
    ///
    /// # Panics
    ///
    /// Panics on an instance of no words.
    pub fn new(b: &mut Builder, session: &SessionId, instance: &[Kw], source: ProofSource<'a>) -> Self {
        assert!(!instance.is_empty(), "an instance has bytes");

        // The seed block is the session identifier, then zeros.
        let sid = primitives::hash::digest_words(&session.0);
        let seed = [sid[0], sid[1], sid[2], sid[3], 0, 0, 0, 0];
        let cv = Compression::new(PARAM_IV, seed, Role::Seed.counter(0, 0), true).output();

        let zero = b.k_const(0);
        let mut t = Self {
            cv: b.d_const(cv),
            pending: [zero; 8],
            n_pending: 0,
            first: true,
            previous: 0,
            squeezed: 0,
            output: [zero; 4],
            source,
            narg_read: 0,
            openings: None,
            phases_read: 0,
            next_opening: 0,
        };
        for &word in instance {
            t.absorb_word(b, word);
        }
        t
    }

    /// Whether every message and hint of the proof was read, and nothing past them.
    ///
    /// Each opening phase reads one hint, so the hints must frame exactly one per phase.
    pub fn finished(&self) -> bool {
        match self.source {
            ProofSource::Proof(p, _) => {
                let mut hints = p.iter_hints();
                let framed = hints.by_ref().count();
                self.narg_read == p.narg.len() && framed == self.phases_read && hints.as_slice().is_empty()
            }
            ProofSource::Shape => true,
        }
    }

    /// Compress the pending block, closing its absorb run if `last`.
    fn compress_pending(&mut self, b: &mut Builder, last: bool) {
        let mut block = self.pending;
        block[self.n_pending..].fill(b.k_const(0));
        let counter = Role::absorb(self.first, last).counter(8 * self.n_pending, self.previous);
        self.cv = b.leaf_block(self.cv, block, counter, true);
        self.n_pending = 0;
        self.first = last;
        self.previous = 0;
    }

    /// Absorb one word, holding a full block back until more input or a squeeze shows whether it is the last.
    fn absorb_word(&mut self, b: &mut Builder, word: Kw) {
        if self.squeezed != 0 {
            self.previous = self.squeezed;
            self.squeezed = 0;
        }
        if self.n_pending == 8 {
            self.compress_pending(b, false);
        }
        self.pending[self.n_pending] = word;
        self.n_pending += 1;
    }

    /// Squeeze one word, a new output block every four.
    fn squeeze_word(&mut self, b: &mut Builder) -> Kw {
        assert!(8 <= Blake2sDuplex::MAX_SQUEEZE - self.squeezed, "squeeze run too long");
        if self.n_pending != 0 {
            self.compress_pending(b, true);
        }
        let offset = (self.squeezed % 32 / 8) as usize;
        if offset == 0 {
            let mut block = [b.k_const(0); 8];
            block[0] = b.k_const(self.squeezed / 32);
            let out = b.leaf_block(self.cv, block, Role::Output.counter(0, 0), true);
            self.output = b.d_to_k(out);
        }
        self.squeezed += 8;
        self.output[offset]
    }

    /// The next message, of `len` bytes, as a value: zero past the proof's end, or from no proof.
    fn take<T: FromNarg + Default>(&mut self, len: usize) -> T {
        // The rows frame whole words, so a message of a partial word would diverge from the native framing.
        assert!(len.is_multiple_of(8), "a replayed message is whole words");
        let value = match self.source {
            ProofSource::Proof(p, _) => (p.narg.get(self.narg_read..)).and_then(|mut rest| T::from_narg(&mut rest)),
            ProofSource::Shape => None,
        };
        self.narg_read += len;
        value.unwrap_or_default()
    }

    /// Absorb an element the verifier knows, as its three words.
    pub fn public_message(&mut self, b: &mut Builder, x: Ew) {
        for word in b.e_to_k(x) {
            self.absorb_word(b, word);
        }
    }

    /// The next prover message, an element of `E`: a free wire, absorbed.
    pub fn prover_message(&mut self, b: &mut Builder) -> Ew {
        let x = b.free_e(self.take::<F192>(24));
        self.public_message(b, x);
        x
    }

    /// The next prover message, a 32-byte digest such as a Merkle root: four free words, absorbed.
    pub fn prover_root(&mut self, b: &mut Builder) -> Dw {
        let bytes = self.take::<[u8; 32]>(32);
        let words = primitives::hash::digest_words(&bytes).map(|w| b.free_k(w));
        for &word in &words {
            self.absorb_word(b, word);
        }
        b.k_to_d(words)
    }

    /// A verifier message: a uniform element of `E`, three squeezed words.
    pub fn verifier_message(&mut self, b: &mut Builder) -> Ew {
        let words = std::array::from_fn(|_| self.squeeze_word(b));
        b.k_to_e(words)
    }

    /// A 32-byte verifier message: four squeezed words.
    ///
    /// Drawn once the proof is read, it is a digest of everything the transcript absorbed.
    pub fn digest(&mut self, b: &mut Builder) -> Dw {
        let words = std::array::from_fn(|_| self.squeeze_word(b));
        b.k_to_d(words)
    }

    /// The digest [`Self::digest`] would draw now, leaving the transcript as it is: a commitment to what it absorbed.
    pub fn digest_so_far(&self, b: &mut Builder) -> Dw {
        Self {
            source: ProofSource::Shape,
            openings: None,
            ..*self
        }
        .digest(b)
    }

    /// Check `bits` of proof of work, as the native verifier does.
    ///
    /// - The challenge is 32 squeezed bytes, the nonce the next message word.
    /// - The trial is the one-block BLAKE2s of the challenge, the nonce, zeros, then the trial tag.
    /// - The trial's first word must have its top `bits` bits zero.
    ///
    /// # Panics
    ///
    /// Panics past the largest difficulty, as the native check does.
    pub fn check_pow(&mut self, b: &mut Builder, bits: u32) {
        let pow = ProofOfWork::new(bits);
        if pow.bits() == 0 {
            return;
        }
        let challenge = self.digest(b);
        let nonce = b.free_k(self.take::<u64>(8));
        self.absorb_word(b, nonce);

        // The hash row's block is `acc | x | ds`: here the challenge, then (nonce, 0, 0), then the tag.
        let x = b.k_to_e1(nonce);
        let tag = b.k_const(ProofOfWork::TRIAL_TAG);
        let (trial, _) = b.compress(challenge, x, tag);
        let [word, ..] = b.d_to_k(trial);
        for bit in b.split(word).into_iter().skip(64 - bits as usize) {
            b.eq_k_const(bit, 0);
        }
    }

    /// Take the next opening phase: its openings are the next the native verifier authenticated.
    ///
    /// The phase's hint holds the same paths, so the rows read the openings and never decode the hint.
    ///
    /// A phase with no such openings, from a proof that was not verified, hashes zeros: its rows then fail.
    pub fn next_openings(&mut self) {
        self.next_opening = 0;
        let phase = self.phases_read;
        self.phases_read += 1;
        self.openings = match self.source {
            ProofSource::Proof(_, openings) => openings.get(phase),
            ProofSource::Shape => None,
        };
    }

    /// Hash the next opened row up its path's lowest `bits.len()` levels.
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
    pub fn open_row(&mut self, b: &mut Builder, bits: &[Kw], row_words: usize, leaf_words: usize) -> OpenedRow {
        assert!(
            leaf_words.is_multiple_of(8) && row_words <= leaf_words,
            "a leaf of whole blocks holds the row"
        );

        // The next opening, or zeros: a word or sibling past what was opened reads zero, so the shape never moves.
        let i = self.next_opening;
        self.next_opening += 1;
        let opened = self.openings.filter(|o| i < o.len());
        let image = |w: usize| opened.and_then(|o| o.image(i).get(w)).map_or(0, |x| x.0);
        let sibling = |l: usize| {
            opened
                .and_then(|o| o.path(i).get(l))
                .map_or([0; 4], primitives::hash::digest_words)
        };

        // The image's whole zero blocks are one constant state, its other words free.
        let prefix = leaf_words - row_words;
        let zero_blocks = prefix / 8;
        let mut h = b.d_const(zero_prefix(zero_blocks));
        let zero = b.k_const(0);
        let words: Vec<Kw> = (zero_blocks * 8..leaf_words)
            .map(|w| if w < prefix { zero } else { b.free_k(image(w)) })
            .collect();
        let n_blocks = leaf_words / 8;
        for (j, m) in words.as_chunks::<8>().0.iter().enumerate() {
            let index = zero_blocks + j;
            h = b.leaf_block(h, *m, 64 * (index as u64 + 1), index + 1 == n_blocks);
        }
        for (l, &bit) in bits.iter().enumerate() {
            h = b.node(h, bit, sibling(l));
        }
        OpenedRow {
            node: h,
            words: words[prefix - zero_blocks * 8..].to_vec(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rec::circuit::Unsatisfied;
    use fiat_shamir::ProverState;
    use pcs::merkle::{Hash, hash_leaf, hash_pair};
    use primitives::field::F64;

    const INSTANCE: [u64; 2] = [3, 4];

    fn session() -> SessionId {
        SessionId::new(b"rec-transcript-test")
    }

    // Absorb runs of 0 to 17 elements between squeeze runs of 1 to 5, a root, and two proofs of work.
    //
    // The runs cross block boundaries both ways: a run ending on a full block, one spilling past it.
    const RUNS: [(usize, usize); 6] = [(0, 1), (1, 2), (2, 3), (8, 5), (9, 1), (17, 4)];

    fn element(stage: usize, i: usize) -> F192 {
        F192::new((stage * 100 + i) as u64, i as u64, u64::MAX - stage as u64)
    }

    // The native prover's run, and every challenge it drew.
    fn native() -> (ProofTranscript, Vec<F192>) {
        let mut ps = ProverState::new(&session(), &INSTANCE);
        let mut challenges = Vec::new();
        for (stage, (absorbed, squeezed)) in RUNS.into_iter().enumerate() {
            for i in 0..absorbed {
                ps.prover_message(&element(stage, i));
            }
            challenges.extend(ps.verifier_messages::<F192>(squeezed));
            if stage == 2 {
                ps.prover_message(&[7u8; 32]);
                ps.challenge_pow(6);
            }
        }
        ps.challenge_pow(1);
        challenges.push(ps.verifier_message());
        (ps.into_proof(), challenges)
    }

    // The same run in rows, from the given source: its circuit, its challenges, and its failures.
    fn rows(source: ProofSource<'_>) -> (crate::rec::circuit::Circuit, Vec<F192>, Vec<Unsatisfied>) {
        let mut b = Builder::new();
        let instance = INSTANCE.map(|w| b.k_const(w));
        let mut t = Transcript::new(&mut b, &session(), &instance, source);
        let mut challenges = Vec::new();
        for (stage, (absorbed, squeezed)) in RUNS.into_iter().enumerate() {
            for _ in 0..absorbed {
                t.prover_message(&mut b);
            }
            for _ in 0..squeezed {
                let c = t.verifier_message(&mut b);
                challenges.push(b.e(c));
            }
            if stage == 2 {
                t.prover_root(&mut b);
                t.check_pow(&mut b, 6);
            }
        }
        t.check_pow(&mut b, 1);
        let c = t.verifier_message(&mut b);
        challenges.push(b.e(c));
        assert!(t.finished());
        let finished = b.finish();
        (finished.circuit, challenges, finished.failures)
    }

    #[test]
    fn the_rows_replay_the_native_transcript() {
        // Same proof, same challenges, and every row satisfied.
        let (proof, expected) = native();
        let (circuit, challenges, failures) = rows(ProofSource::Proof(&proof, &[]));
        assert!(failures.is_empty(), "{failures:?}");
        assert_eq!(challenges, expected);

        // Built from the shape alone, the circuit is the same.
        assert_eq!(circuit, rows(ProofSource::Shape).0);
    }

    #[test]
    fn a_nonce_short_of_its_work_fails_a_row() {
        // Fixture: the last message is the 1-bit nonce; flip its bits until one misses the work.
        //
        // About half the nonces miss one bit, so a few flips find one.
        let (proof, _) = native();
        let last = proof.narg.len() - 8;
        let missed = (0..64u8).find_map(|bit| {
            let mut forged = proof.clone();
            forged.narg[last + usize::from(bit / 8)] ^= 1 << (bit % 8);
            let (_, _, failures) = rows(ProofSource::Proof(&forged, &[]));
            (!failures.is_empty()).then_some(failures)
        });
        assert!(missed.is_some(), "no forged nonce failed");
    }

    // Opens one row of eight words at index 0 of a tree of the given depth, returning the rows' failures.
    fn open(leaf: &[u64; 8], path: &[Hash], root: &Hash, depth: usize) -> Vec<Unsatisfied> {
        let openings = Openings {
            leaf_words: 8,
            height: path.len(),
            images: leaf.map(F64).to_vec(),
            paths: path.to_vec(),
        };
        let mut b = Builder::new();
        let root = b.d_const(primitives::hash::digest_words(root));
        let bits = vec![b.k_const(0); depth];
        let instance = [b.k_const(0)];
        let proof = ProofTranscript::default();
        let phases = [openings];
        let mut t = Transcript::new(&mut b, &session(), &instance, ProofSource::Proof(&proof, &phases));
        t.next_openings();
        let row = t.open_row(&mut b, &bits, 8, 8);
        b.eq(row.node, root);
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
        let preimage: [u64; 8] = std::array::from_fn(|j| primitives::hash::digest_words(&leaves[j / 4])[j % 4]);
        assert!(open(&preimage, &[nodes[1]], &root, 1).is_empty());
        assert!(!open(&preimage, &[nodes[1]], &root, 2).is_empty());
    }

    #[test]
    fn the_native_constants_are_the_lean_transcriptions() {
        // `LeanVMCircuits.Rec.Duplex` and `Rec.Merkle` state the transcript and the hashes over these values.
        use crate::rec::clean::{ABSORB_TWEAKS, DUPLEX_TAGS, PARAM_IV_WORDS, ZERO_PREFIXES};
        assert_eq!(PARAM_IV, PARAM_IV_WORDS);
        for (n, &z) in ZERO_PREFIXES.iter().enumerate() {
            assert_eq!(zero_prefix(n), z, "{n} zero blocks");
        }
        assert_eq!(
            [
                Role::Seed.counter(0, 0),
                Role::Output.counter(0, 0),
                ProofOfWork::TRIAL_TAG
            ],
            DUPLEX_TAGS
        );
        for &(first, last, len, previous, tweak) in ABSORB_TWEAKS {
            assert_eq!(
                Role::absorb(first, last).counter(len, previous),
                tweak,
                "{first} {last} {len} {previous}"
            );
        }
    }
}
