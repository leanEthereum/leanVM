//! The key commitment: every one-time-pad key, the outer proof's dummy operands and its mask, in one lane of its own stack, beside one lane of uniform words.
//!
//! Its shape is fixed, so neither side counts anything before committing:
//!
//! ```text
//!     lane 0   slots of E, three words each: the 6 dummy operands, the mask's room, then the keys in the order they pad
//!     lane 1   uniform words
//! ```
//!
//! Its opening's claim is public and its weight vanishes on lane 1, so the lane fold mixes the uniform lane into everything the opening reveals: it is the one commitment whose opening hides itself.

use super::r1cs::N_DUMMIES;
use super::randomness::{Purpose, ZkRng, uniform_e};
use super::spartan::{OuterClaims, libra_len};
use crate::pcs::LOG_BATCH;
use primitives::field::{F64, F192};

/// The key stack's size: two lanes of `2^(KEY_MU - LOG_BATCH)` words, the smallest stack a hiding opening takes.
pub(crate) const KEY_MU: usize = ::pcs::whir::MIN_LOG_N_HIDING;
/// The words of a lane.
pub(crate) const LANE: usize = 1 << (KEY_MU - LOG_BATCH);

/// The `E` slots lane 0 holds.
pub(crate) const N_SLOTS: usize = LANE / 3;

/// The dummy operands' first slot.
pub(crate) const DUMMY_SLOT: usize = 0;

/// The outer proof's mask's first slot.
pub(crate) const LIBRA_SLOT: usize = DUMMY_SLOT + N_DUMMIES;

/// The outer constraint system's largest row cube, which the mask's room is sized for.
pub(crate) const MAX_OUTER_LOG_ROWS: usize = 24;

/// The first key's slot.
pub(crate) const KEY_SLOT: usize = LIBRA_SLOT + libra_len(MAX_OUTER_LOG_ROWS);

/// The most keys one proof uses: hidden scalars, then auxiliary values.
pub(crate) const MAX_KEYS: usize = N_SLOTS - KEY_SLOT;

/// The prover's key stack: its slots, and the two lanes' words it commits.
pub(crate) struct KeyStack {
    /// Every slot of lane 0: dummy operands, mask, keys, all uniform but the dummies' products.
    pub(crate) slots: Vec<F192>,
    /// Lane 0's words, then lane 1's.
    pub(crate) words: Vec<F64>,
}

impl KeyStack {
    /// Draw a proof's keys, its outer proof's dummies and mask, and the uniform lane.
    pub(crate) fn draw(rng: &ZkRng) -> Self {
        let mut stream = rng.stream(Purpose::Keys);
        let mut slots: Vec<F192> = (0..N_SLOTS).map(|_| uniform_e(&mut stream)).collect();
        let dummies = super::r1cs::dummy_values(|| uniform_e(&mut stream));
        slots[DUMMY_SLOT..DUMMY_SLOT + N_DUMMIES].copy_from_slice(&dummies);

        let mut words = vec![F64::ZERO; 2 * LANE];
        rng.fill_k(Purpose::KeyLanes, &mut words[3 * N_SLOTS..]);
        for (s, slot) in slots.iter().enumerate() {
            words[3 * s..3 * s + 3].copy_from_slice(&[F64(slot.c0), F64(slot.c1), F64(slot.c2)]);
        }
        Self { slots, words }
    }

    /// The keys, in the order the hidden scalars use them.
    pub(crate) fn keys(&self) -> &[F192] {
        &self.slots[KEY_SLOT..]
    }

    /// The outer proof's mask for a constraint system of `2^log_rows` rows.
    pub(crate) fn libra(&self, log_rows: usize) -> &[F192] {
        &self.slots[LIBRA_SLOT..LIBRA_SLOT + libra_len(log_rows)]
    }

    /// The outer constraint system's assignment: the constant one, then every slot.
    pub(crate) fn z(&self) -> Vec<F192> {
        std::iter::once(F192::ONE).chain(self.slots.iter().copied()).collect()
    }
}

/// The key opening's claim: the outer proof's two claims, batched by `lambda`, as a weight on lane 0's words and a target.
pub(crate) fn opening_claim(claims: &OuterClaims, lambda: F192) -> (Vec<F192>, F192) {
    assert_eq!(
        claims.witness_weight.len(),
        N_SLOTS,
        "the outer proof's columns are the slots"
    );
    let mut slots = claims.witness_weight.clone();
    for (s, &w) in slots[LIBRA_SLOT..].iter_mut().zip(&claims.libra_weight) {
        *s += lambda * w;
    }
    let basis = [F192::new(1, 0, 0), F192::new(0, 1, 0), F192::new(0, 0, 1)];
    let mut weight = vec![F192::ZERO; LANE];
    for (s, &w) in slots.iter().enumerate() {
        for (l, &y) in basis.iter().enumerate() {
            weight[3 * s + l] = w * y;
        }
    }
    (weight, claims.witness_target + lambda * claims.libra_target)
}
