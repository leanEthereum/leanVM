//! The transcript in rows: the BLAKE2s duplex replayed on constrained words.
//!
//! It mirrors the native transcript call for call, with the same framing and the same output cursor.
//!
//! - A prover message is a free wire, absorbed as its words.
//! - A verifier message is squeezed words, each block of four an output row's.
//! - A hint is decoded natively, and only what it opens becomes wires.
//!
//! Every message the rows absorb is whole 64-bit words, so the native byte framing is a word framing here.

use super::circuit::{Builder, Compression, Dw, Ew, Kw, Limbs, PARAM_IV, digest_limbs, zero_prefix};
use fiat_shamir::{FromNarg, MAX_SQUEEZE, ProofOfWork, ProofTranscript, Role, SessionId};
use pcs::merkle::PrunedMerklePaths;
use primitives::field::F192;
use std::collections::VecDeque;

/// What the circuit reads: the proof when it has one, zeros when it is built from the shape alone.
///
/// The rows never depend on what is read, so both sources give one circuit.
#[derive(Clone, Copy, Debug)]
pub enum ProofSource<'a> {
    /// The proof the native verifier accepted.
    Proof(&'a ProofTranscript),
    /// No proof: every message and opening is zero.
    Shape,
}

/// One Merkle opening as the circuit reads it: the leaf's image and the sibling path.
#[derive(Clone, Debug, Default)]
struct MerkleOpening {
    /// The leaf image's words.
    image: Vec<u64>,
    /// The siblings, lowest first.
    path: Vec<Limbs>,
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
    /// Hint bytes read so far.
    hints_read: usize,
    /// Openings decoded from the last hint, not yet hashed.
    openings: VecDeque<MerkleOpening>,
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
        let sid = digest_limbs(&session.0);
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
            hints_read: 0,
            openings: VecDeque::new(),
        };
        for &word in instance {
            t.absorb_word(b, word);
        }
        t
    }

    /// Whether every message and hint of the proof was read, and nothing past them.
    pub const fn finished(&self) -> bool {
        match self.source {
            ProofSource::Proof(p) => self.narg_read == p.narg.len() && self.hints_read == p.hints.len(),
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
        assert!(8 <= MAX_SQUEEZE - self.squeezed, "squeeze run too long");
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
            ProofSource::Proof(p) => (p.narg.get(self.narg_read..)).and_then(|mut rest| T::from_narg(&mut rest)),
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
        let words = digest_limbs(&bytes).map(|w| b.free_k(w));
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

    /// Read the next hint as Merkle paths, and queue the openings it gives these queries.
    ///
    /// The paths are opened natively, against the root's value, so that each query gets its full path.
    /// A hint that does not open queues nothing: the rows that hash the openings then fail.
    pub fn read_openings(&mut self, b: &Builder, root: Dw, queries: &[Vec<Kw>], row_words: usize, leaf_words: usize) {
        self.openings.clear();
        let ProofSource::Proof(p) = self.source else {
            return;
        };

        // The hint: a four-byte little-endian length, then the paths.
        let hint = (p.hints.get(self.hints_read..))
            .and_then(|rest| rest.split_first_chunk::<4>())
            .and_then(|(len, rest)| rest.get(..u32::from_le_bytes(*len) as usize));
        self.hints_read += 4 + hint.map_or(0, <[u8]>::len);

        // The queries' values, their distinct count, and the root's bytes.
        let values: Vec<usize> = (queries.iter())
            .map(|bits| (bits.iter().enumerate()).fold(0, |acc, (i, &bit)| acc | (b.k(bit) as usize) << i))
            .collect();
        let mut distinct = values.clone();
        distinct.sort_unstable();
        distinct.dedup();
        let limbs = b.d(root);
        let root: [u8; 32] = std::array::from_fn(|i| (limbs[i / 8] >> (8 * (i % 8))) as u8);
        let depth = queries.first().map_or(0, Vec::len);

        let opened = hint
            .and_then(|hint| PrunedMerklePaths::from_hint(hint, distinct.len(), row_words))
            .and_then(|paths| paths.open(&root, 1 << depth, &values, row_words, leaf_words));
        self.openings = (opened.into_iter().flatten())
            .map(|o| MerkleOpening {
                image: o.leaf_data.iter().map(|w| w.0).collect(),
                path: o.path.iter().map(digest_limbs).collect(),
            })
            .collect();
    }

    /// Hash the next queued row up its path's lowest `bits.len()` levels, returning the node reached and the row's words.
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

        // The next queued opening, zero filled to the shape.
        let mut opening = self.openings.pop_front().unwrap_or_default();
        opening.image.resize(leaf_words, 0);
        opening.path.resize(bits.len(), [0; 4]);

        // The image's whole zero blocks are one constant state, its other words free.
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
    use crate::rec::circuit::Unsatisfied;
    use fiat_shamir::ProverState;
    use pcs::merkle::{Hash, hash_leaf, hash_pair};

    const INSTANCE: [u64; 2] = [3, 4];

    impl Transcript<'_> {
        // Queue an opening as a hint would, for rows built without one.
        pub(crate) fn queue_opening(&mut self, image: Vec<u64>, path: &[Hash]) {
            let path = path.iter().map(digest_limbs).collect();
            self.openings.push_back(MerkleOpening { image, path });
        }
    }

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
        let (circuit, challenges, failures) = rows(ProofSource::Proof(&proof));
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
            let (_, _, failures) = rows(ProofSource::Proof(&forged));
            (!failures.is_empty()).then_some(failures)
        });
        assert!(missed.is_some(), "no forged nonce failed");
    }

    // Opens one row of eight words at index 0 of a tree of the given depth, returning the rows' failures.
    fn open(leaf: &[u64; 8], path: &[Hash], root: &Hash, depth: usize) -> Vec<Unsatisfied> {
        let mut b = Builder::new();
        let root = b.d_const(digest_limbs(root));
        let bits = vec![b.k_const(0); depth];
        let instance = [b.k_const(0)];
        let mut t = Transcript::new(&mut b, &session(), &instance, ProofSource::Shape);
        t.queue_opening(leaf.to_vec(), path);
        let (node, _) = t.open_row(&mut b, &bits, 8, 8);
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
