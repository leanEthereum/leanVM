//! The outer proof that the keys satisfy what the recorder recorded, and the key commitment it opens.
//!
//! After the recorded transcript, a zero-knowledge proof holds, in order:
//!
//! ```text
//!     hidden   each auxiliary value, under the keys after the hidden scalars'
//!     clear    the outer Spartan over the system's rows
//!     clear    the key commitment's opening of the Spartan's two claims, batched by one challenge
//! ```
//!
//! The system is a rank-one system over `z = (1, slots)`, the key stack's slots:
//!
//! ```text
//!     rows 0 .. n        the record's, over the keys
//!     rows n, n + 1      the dummies: z_0 z_1 = z_2 and z_3 z_4 = z_5, on fresh uniform slots
//! ```
//!
//! # The key commitment
//!
//! It holds every one-time-pad key, the outer proof's dummy operands and its mask.
//!
//! Its shape is fixed, so both sides know it before anything is sent:
//!
//! ```text
//!     lane 0      slots of E, three words each: 6 dummy operands, the mask, then the keys in the order they pad
//!     lanes 1-3   zero
//!     lanes 4-7   uniform: the hiding commitment's random group
//! ```
//!
//! Its openings hide themselves.
//!
//! - Their weight lives on lane 0 alone.
//! - The random group makes the lane-folded witness uniform, as for any hiding commitment.
//! - Before the lane fold, each round reveals the target and sums of the random lanes against the weight, which are uniform too.

use crate::randomness::{Purpose, Seed};
use crate::record::{Record, Recorder, SparseWeights};
use crate::spartan::{self, Claims, log_rows, mask_len};
use fiat_shamir::arith::{Arith, Native};
use fiat_shamir::{ProverState, TranscriptError};
use pcs::stack::{CommittedStack, StackCommitment, Weighted};
use pcs::verifier::OpeningVerifier;
use pcs::whir::{Config, INITIAL_FOLDING_FACTOR, MIN_LOG_N_HIDING, WhirError};
use primitives::field::{F64, F192};
use rand_core::RngCore;
use thiserror::Error;

/// The key stack's size: `2^KEY_MU` words, the smallest a hiding opening takes.
const KEY_MU: usize = MIN_LOG_N_HIDING;

/// The words of a lane.
const LANE: usize = 1 << (KEY_MU - INITIAL_FOLDING_FACTOR);

/// The lanes committed: lane 0, the zero lanes, then the random group.
const LANES: usize = Config::hiding_lanes(1);

/// The slots of `E` lane 0 holds, three words each.
const N_SLOTS: usize = LANE / 3;

/// The first of the six dummy operands: two uniform pairs, then their products.
const DUMMY_SLOT: usize = 0;

/// The dummy operands.
const N_DUMMIES: usize = 6;

/// The dummy rows: each row's three slots.
const DUMMY_ROWS: [[usize; 3]; 2] = [
    [DUMMY_SLOT, DUMMY_SLOT + 1, DUMMY_SLOT + 2],
    [DUMMY_SLOT + 3, DUMMY_SLOT + 4, DUMMY_SLOT + 5],
];

/// The first of the mask's coefficients.
const MASK_SLOT: usize = DUMMY_SLOT + N_DUMMIES;

/// The largest outer system, in variables of its row cube: the mask's room is sized for it.
const MAX_LOG_ROWS: usize = 24;

/// The first key.
const KEY_SLOT: usize = MASK_SLOT + mask_len(MAX_LOG_ROWS);

/// The most keys one proof uses: its hidden scalars, then its auxiliary values.
const MAX_KEYS: usize = N_SLOTS - KEY_SLOT;

/// Why an outer proof is refused.
#[derive(Clone, Copy, Debug, Error, PartialEq, Eq)]
pub enum OuterError {
    /// The transcript needs more keys than the key commitment holds.
    #[error("{keys} keys, more than the {max} the key commitment holds")]
    TooManyKeys {
        /// Keys the transcript takes.
        keys: usize,
        /// Keys the commitment holds.
        max: usize,
    },
    /// The system has more rows than its mask covers.
    #[error("2^{log_rows} outer rows, more than 2^{max}")]
    TooManyRows {
        /// The rows' variables.
        log_rows: usize,
        /// The most the mask covers.
        max: usize,
    },
    /// The proof ends early.
    #[error(transparent)]
    Transcript(#[from] TranscriptError),
    /// The key commitment's opening is refused.
    #[error("the key opening: {0}")]
    KeyOpening(WhirError),
}

/// The outer rank-one system: a record's rows, then the dummy rows.
struct OuterSystem<'r, E> {
    /// What the recorder recorded.
    record: &'r Record<E>,
}

/// A claim on the key stack's slots: `sum_s weights[s] slot_s = value`, a weight absent where it is zero.
struct SlotClaim<E> {
    /// Each slot's weight.
    weights: Vec<Option<E>>,
    /// The claimed sum.
    value: E,
}

impl<'r, E: Copy> OuterSystem<'r, E> {
    /// The system of a record.
    ///
    /// # Errors
    ///
    /// Refuses a record whose keys or rows outgrow the key commitment.
    const fn new(record: &'r Record<E>) -> Result<Self, OuterError> {
        let system = Self { record };
        let keys = record.n_keys() + record.n_aux();
        if keys > MAX_KEYS {
            return Err(OuterError::TooManyKeys { keys, max: MAX_KEYS });
        }
        let log_rows = system.log_rows();
        if log_rows > MAX_LOG_ROWS {
            return Err(OuterError::TooManyRows {
                log_rows,
                max: MAX_LOG_ROWS,
            });
        }
        Ok(system)
    }

    /// The system's rows: the record's, then the dummies.
    const fn n_rows(&self) -> usize {
        self.record.n_rows() + DUMMY_ROWS.len()
    }

    /// The variables of the system's row cube.
    const fn log_rows(&self) -> usize {
        log_rows(self.n_rows())
    }

    /// The key opening's claim: the rows' claim pulled back onto the slots, plus `lambda` times the mask's claim.
    ///
    /// ```text
    ///     sum_s weights[s] slot_s  =  rows' value + constant + lambda g(r)     (characteristic two)
    /// ```
    fn opening_claim<A: Arith<E = E>>(&self, ar: &mut A, claims: &Claims<E>, sent: &[E], lambda: E) -> SlotClaim<E> {
        // Row x takes eq(r, x) on A, gamma eq(r, x) on B, gamma^2 eq(r, x) on C.
        let rows = &claims.rows;
        let eq = ar.eq_table_prefix(&rows.point, self.n_rows());
        let on_b: Vec<E> = eq.iter().map(|&e| ar.mul(e, rows.gamma)).collect();
        let on_c: Vec<E> = on_b.iter().map(|&e| ar.mul(e, rows.gamma)).collect();
        let mut slots = SparseWeights::new(N_SLOTS);

        // The record's rows, on the keys.
        let n = self.record.n_rows();
        let keys = self.record.weigh(ar, [&eq[..n], &on_b[..n], &on_c[..n]], sent);
        for (i, w) in keys.keys.into_iter().enumerate() {
            if let Some(w) = w {
                slots.add(ar, KEY_SLOT + i, w);
            }
        }

        // The dummy rows, on their slots.
        for (d, row) in DUMMY_ROWS.iter().enumerate() {
            for (&slot, weights) in row.iter().zip([&eq, &on_b, &on_c]) {
                slots.add(ar, slot, weights[n + d]);
            }
        }

        // The mask's claim, scaled by lambda, on the mask's slots.
        for (i, &w) in claims.mask.weight.iter().enumerate() {
            let lw = ar.mul(lambda, w);
            slots.add(ar, MASK_SLOT + i, lw);
        }

        let value = ar.add(rows.value, keys.constant);
        let value = ar.mul_add(lambda, claims.mask.value, value);
        SlotClaim {
            weights: slots.into_vec(),
            value,
        }
    }
}

/// A proof's keys, its outer proof's dummies and mask, committed: the prover's side of the key commitment.
pub struct Keys {
    /// Every slot of lane 0: dummy operands, mask, keys, all uniform but the dummies' two products.
    slots: Vec<F192>,
    /// The committed words: lane 0's slots, the zero lanes and the random group.
    words: Vec<F64>,
    /// The commitment to the words.
    committed: CommittedStack,
}

impl Keys {
    /// Draw a proof's keys, dummies and mask from its seed, commit them at L0 rate `2^-log_inv_rate`, and send the root.
    ///
    /// # Panics
    ///
    /// Panics on a rate the hiding table does not cover.
    #[must_use]
    pub fn commit(ps: &mut ProverState, log_inv_rate: usize, seed: &Seed) -> Self {
        let mut stream = seed.stream(Purpose::Keys);
        // A uniform element of `E` is three uniform words.
        let mut slots: Vec<F192> = (0..N_SLOTS)
            .map(|_| F192::new(stream.next_u64(), stream.next_u64(), stream.next_u64()))
            .collect();
        // The dummies' products, so that the dummy rows hold.
        slots[DUMMY_SLOT + 2] = slots[DUMMY_SLOT] * slots[DUMMY_SLOT + 1];
        slots[DUMMY_SLOT + 5] = slots[DUMMY_SLOT + 3] * slots[DUMMY_SLOT + 4];

        // Slot s is words 3s, 3s + 1 and 3s + 2 of lane 0, its limbs lowest first.
        let mut words = vec![F64::ZERO; LANES * LANE];
        let limbs = F192::coefficients(&slots);
        words[..limbs.len()].copy_from_slice(limbs);
        let config = Config::hiding(KEY_MU, log_inv_rate).expect("a supported rate");
        let committed =
            CommittedStack::new_hiding(&mut words, KEY_MU, config, &mut seed.stream(Purpose::KeyCommitment));
        ps.prover_message(&committed.root());
        Self {
            slots,
            words,
            committed,
        }
    }

    /// The keys, in the order the hidden messages use them.
    #[must_use]
    pub fn keys(&self) -> &[F192] {
        &self.slots[KEY_SLOT..]
    }

    /// Prove the outer proof of a recorded transcript.
    ///
    /// - `record` is what the prover's replay of its own proof recorded.
    /// - `ps` has sent exactly the record's hidden scalars, under the first keys.
    ///
    /// Keys that do not satisfy the record give a proof the verifier refuses.
    ///
    /// # Panics
    ///
    /// Panics if the record outgrows the key commitment.
    pub fn prove_outer(&self, ps: &mut ProverState, record: &Record<F192>) {
        let system = OuterSystem::new(record).unwrap_or_else(|e| panic!("the outer proof: {e}"));
        assert_eq!(
            ps.keys_used(),
            record.n_keys(),
            "the replay read every hidden scalar the prover sent"
        );

        // The auxiliary values, each under its key: what goes out is the value plus the key.
        let values = record.evaluate(self.keys());
        let sent: Vec<F192> = (values.aux().iter().zip(&self.keys()[record.n_keys()..]))
            .map(|(&v, &k)| v + k)
            .collect();
        ps.set_hidden(true);
        ps.prover_messages(values.aux());
        ps.set_hidden(false);

        // The Spartan over the record's rows, then the dummies.
        let mut sides = record.sides(&values);
        for row in DUMMY_ROWS {
            for (side, slot) in sides.iter_mut().zip(row) {
                side.push(self.slots[slot]);
            }
        }
        let mask = &self.slots[MASK_SLOT..MASK_SLOT + mask_len(system.log_rows())];
        let claims = spartan::prove(ps, sides, mask);

        // The key opening, its two claims batched.
        let lambda: F192 = ps.verifier_message();
        let claim = system.opening_claim(&mut Native, &claims, &sent, lambda);
        let weights: Vec<F192> = claim.weights.iter().map(|w| w.unwrap_or(F192::ZERO)).collect();
        self.open(ps, &weights, claim.value);
    }

    /// Prove `sum_s weights[s] slot_s = value`.
    #[expect(
        clippy::disallowed_methods,
        reason = "the outer proof's claim: its value and weights are functions of sent messages and earlier challenges"
    )]
    fn open(&self, ps: &mut ProverState, weights: &[F192], value: F192) {
        let weight = word_weights(weights, F192::ZERO, |w, y| w * y);
        self.committed
            .open_weighted(ps, &self.words, Weighted { weight: &weight, value });
    }
}

/// The key commitment as its verifier holds it.
///
/// Its root is a digest, or whatever a verifier holds it as.
///
/// It is a hiding commitment, so it has no anchor: an anchor's value would publish an evaluation of the keys.
pub struct KeyCommitment<R> {
    /// The commitment to the key stack.
    commitment: StackCommitment<F192, R>,
}

impl<R: Copy> KeyCommitment<R> {
    /// Read the key commitment's root, for openings at L0 rate `2^-log_inv_rate`.
    ///
    /// # Errors
    ///
    /// Refuses a rate the hiding table does not cover, or a proof that ends first.
    pub fn read<V: OpeningVerifier<Root = R>>(v: &mut V, log_inv_rate: usize) -> Result<Self, WhirError> {
        let config = Config::hiding(KEY_MU, log_inv_rate)?;
        let root = v.next_root()?;
        Ok(Self {
            commitment: StackCommitment::hiding(root, KEY_MU, LANES, config)?,
        })
    }

    /// Verify the outer proof of a recorded transcript, the recorder having read the transcript up to it.
    ///
    /// It returns the inner verifier, for the caller to check the proof's end.
    ///
    /// # Errors
    ///
    /// Refuses a record the key commitment cannot hold, a malformed proof, or a key opening its verifier refuses.
    pub fn verify_outer<V: OpeningVerifier<Root = R>>(&self, recorder: Recorder<V>) -> Result<V, OuterError> {
        let (mut v, record) = recorder.finish();
        let system = OuterSystem::new(&record)?;

        // The auxiliary values as sent: each is that plus the next key.
        let sent = v.prover_messages(record.n_aux())?;

        let claims = spartan::verify(&mut v, system.n_rows())?;
        let lambda = v.verifier_message();
        let claim = system.opening_claim(&mut v, &claims, &sent, lambda);
        self.verify(&mut v, &claim.weights, claim.value)
            .map_err(OuterError::KeyOpening)?;
        Ok(v)
    }

    /// Verify the opening of `sum_s weights[s] slot_s = value`, a weight absent where it is zero.
    ///
    /// # Errors
    ///
    /// Refuses the opening as the hiding WHIR verifier does.
    #[expect(
        clippy::disallowed_methods,
        reason = "the outer proof's claim: its value and weights are functions of sent messages and earlier challenges"
    )]
    fn verify<V: OpeningVerifier<Root = R>>(
        &self,
        v: &mut V,
        weights: &[Option<V::E>],
        value: V::E,
    ) -> Result<(), WhirError> {
        let zero = v.zero();
        let weight = word_weights(weights, zero, |w, y| w.map_or(zero, |w| v.mul_const(w, y)));
        self.commitment.verify_weighted(v, Weighted { weight: &weight, value })
    }
}

/// Each slot's weight spread on lane 0's words: slot `s` is `w_0 + w_1 y + w_2 y^2` of its words `3s`, `3s + 1`, `3s + 2`.
///
/// `spread(w, y^l)` is word `3s + l`'s weight.
/// The lane's words past the last slot weigh `zero`.
fn word_weights<W: Copy, E: Copy>(weights: &[W], zero: E, mut spread: impl FnMut(W, F192) -> E) -> Vec<E> {
    let powers = [F192::new(1, 0, 0), F192::new(0, 1, 0), F192::new(0, 0, 1)];
    let mut out = Vec::with_capacity(LANE);
    for &w in weights {
        out.extend(powers.map(|y| spread(w, y)));
    }
    out.resize(LANE, zero);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::randomness::Randomness;
    use fiat_shamir::{ProofTranscript, SessionId, VerifierState};
    use pcs::merkle::Hash;
    use primitives::test_util::Rng;

    const SESSION: &[u8] = b"outer-test";

    /// A toy protocol's prover: it sends `x, y, x y, 1 / x` and a bit hidden, then `x + y` in the clear.
    ///
    /// `forge` replaces what it sends for `(x y, 1 / x, bit)`.
    fn prove_toy(seed: u8, x: F192, y: F192, forge: Option<[F192; 3]>) -> ProofTranscript {
        let seed = Randomness::Fixed([seed; 32]).seed();
        let mut ps = ProverState::new(&SessionId::new(SESSION), &0u64);
        let keys = Keys::commit(&mut ps, 1, &seed);
        ps.set_keys(keys.keys().to_vec());

        // The hidden part of the transcript.
        let [xy, inv, bit] = forge.unwrap_or_else(|| [x * y, x.inv(), F192::ONE]);
        ps.set_hidden(true);
        ps.prover_messages(&[x, y, xy, inv, bit]);
        ps.set_hidden(false);
        ps.prover_message(&(x + y));

        // The prover replays the verifier over its own proof, then proves the outer proof.
        let replay = ps.proof().clone();
        let mut recorder = Recorder::new(VerifierState::new(&SessionId::new(SESSION), &0u64, &replay));
        let _ = verify_toy(&mut recorder);
        let (_, record) = recorder.finish();
        keys.prove_outer(&mut ps, &record);
        ps.into_proof()
    }

    /// The toy protocol's verifier, generic over the verifier it runs on: it returns the key commitment.
    fn verify_toy<V: OpeningVerifier>(v: &mut V) -> Result<KeyCommitment<V::Root>, WhirError> {
        let commitment = KeyCommitment::read(v, 1)?;
        v.set_hidden(true);
        let [x, y, xy, inv, bit] = std::array::from_fn(|_| v.prover_message().unwrap_or_else(|_| v.zero()));
        v.set_hidden(false);
        let sum = v.prover_message()?;
        // x y = xy, x / x = 1 through the inverse's own row, a bit, and the clear sum.
        let p = v.mul(x, y);
        v.ensure_eq(p, xy, || ()).ok();
        let q = v.mul(x, inv);
        let one = v.one();
        v.ensure_eq(q, one, || ()).ok();
        let b2 = v.mul(bit, bit);
        v.ensure_eq(b2, bit, || ()).ok();
        let s = v.add(x, y);
        v.ensure_eq(s, sum, || ()).ok();
        Ok(commitment)
    }

    /// Verify a toy proof whole.
    fn check(proof: &ProofTranscript) -> Result<(), OuterError> {
        let vs = VerifierState::new(&SessionId::new(SESSION), &0u64, proof);
        let mut recorder = Recorder::new(vs);
        let commitment = verify_toy(&mut recorder).map_err(OuterError::KeyOpening)?;
        let vs = commitment.verify_outer(recorder)?;
        vs.check_eof()?;
        Ok(())
    }

    #[test]
    fn an_honest_outer_proof_verifies() {
        let (x, y) = (F192::new(3, 5, 7), F192::new(11, 13, 17));
        assert_eq!(check(&prove_toy(1, x, y, None)), Ok(()));
    }

    #[test]
    fn a_false_hidden_statement_is_refused() {
        // Each forgery breaks one recorded row while the clear part still checks.
        //
        //     x y + 1   breaks the product row
        //     1/x + 1   breaks the inverse's equality
        //     bit = y   breaks the bit's row
        let (x, y) = (F192::new(3, 5, 7), F192::new(11, 13, 17));
        for forged in [
            [x * y + F192::ONE, x.inv(), F192::ONE],
            [x * y, x.inv() + F192::ONE, F192::ONE],
            [x * y, x.inv(), y],
        ] {
            assert!(check(&prove_toy(1, x, y, Some(forged))).is_err(), "forgery {forged:?}");
        }
    }

    #[test]
    fn a_tampered_auxiliary_value_is_refused() {
        // The toy's auxiliary values follow its 32-byte root and six scalars.
        let (x, y) = (F192::new(3, 5, 7), F192::new(11, 13, 17));
        let mut forged = prove_toy(1, x, y, None);
        forged.narg[32 + 6 * 24] ^= 1;
        assert!(check(&forged).is_err());
    }

    #[test]
    fn two_witnesses_send_unrelated_scalars() {
        // Same shape, other witness, other randomness: every hidden scalar differs.
        let a = prove_toy(1, F192::new(3, 5, 7), F192::new(11, 13, 17), None);
        let b = prove_toy(2, F192::new(4, 6, 8), F192::new(12, 14, 16), None);
        assert_eq!(a.narg.len(), b.narg.len());
        let hidden = 32..32 + 5 * 24;
        assert!((hidden.step_by(24)).all(|i| a.narg[i..i + 24] != b.narg[i..i + 24]));
    }

    #[test]
    fn a_key_opening_verifies_and_binds_its_claim() {
        // A claim on a few slots: a dummy, a mask coefficient, the first key and the last slot.
        let seed = Randomness::Fixed([5; 32]).seed();
        let session = SessionId::new(b"key-opening-test");
        let mut ps = ProverState::new(&session, &0u64);
        let keys = Keys::commit(&mut ps, 1, &seed);
        let mut rng = Rng::new(9);
        let mut weights = vec![None; N_SLOTS];
        for s in [DUMMY_SLOT, MASK_SLOT + 3, KEY_SLOT, N_SLOTS - 1] {
            weights[s] = Some(rng.ext());
        }
        let value =
            (weights.iter().zip(&keys.slots)).fold(F192::ZERO, |acc, (w, &x)| acc + w.map_or(F192::ZERO, |w| w * x));
        let dense: Vec<F192> = weights.iter().map(|w| w.unwrap_or(F192::ZERO)).collect();
        keys.open(&mut ps, &dense, value);
        let proof = ps.into_proof();

        let check = |value: F192| -> Result<(), WhirError> {
            let mut vs = VerifierState::new(&session, &0u64, &proof);
            let commitment = KeyCommitment::<Hash>::read(&mut vs, 1).expect("a root");
            commitment.verify(&mut vs, &weights, value)?;
            vs.check_eof().map_err(WhirError::from)
        };
        assert_eq!(check(value), Ok(()));
        // Mutation: a value off by one, which the opening's terminal check refuses.
        assert!(check(value + F192::ONE).is_err());
    }
}
