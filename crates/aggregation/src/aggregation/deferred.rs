//! The deferred claim on the stacked bytecode and the sumcheck that batches it.

use super::cells::{ONE, ZERO, count};
use super::guest::{scalar_bytecode, stacked_bytecode};
use super::hints::SubHints;
use crate::protocol::N_BYTECODE_SELECTORS;
use isa::Prover;
use std::ops::Range;
use verifier::{Digest, E, K, RATE_SCALARS, Sponge, grinding_bits};

pub(super) const RECURSION_AGG_LABEL: &[u8] = b"leanvm/recursion-aggregation/v1";

/// The claim on the stacked bytecode that a node defers rather than evaluating
/// in-circuit: one point and value (`doc/leanvm/main.tex` §Deferred evaluation
/// claims).
///
/// Only the point is transmitted; the value is derived from it on receipt, so a
/// prover that lies about a value changes the statement its proof has to satisfy
/// rather than the claim anyone checks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DeferredBytecodeClaim {
    pub(super) bytecode_point: Vec<E>,
    pub(super) bytecode_value: E,
}

impl DeferredBytecodeClaim {
    /// What a leaf defers: the all-zeros point, where the value is just the
    /// table's first entry.
    pub(super) fn leaf() -> Self {
        Self::recompute_scalar(vec![ZERO; bytecode_vars()]).expect("the all-zeros point has the right shape")
    }

    /// The claim at `bytecode_point`, its value read off the point's [`bytecode_sums`].
    pub(super) fn from_sums<P: Prover>(bytecode_point: Vec<E>, sums: &[E]) -> Self {
        let bytecode_value = bytecode_value::<P>(sums, &bytecode_point);
        Self {
            bytecode_point,
            bytecode_value,
        }
    }

    /// The claim at `bytecode_point`, evaluated by the `verifier` crate, scalar and single threaded: what a received
    /// aggregate is checked with. `None` for a point of the wrong length.
    pub(super) fn recompute_scalar(bytecode_point: Vec<E>) -> Option<Self> {
        if bytecode_point.len() != bytecode_vars() {
            return None;
        }
        // Every leaf defers the all-zeros point, where the bytecode polynomial is just its table's first entry: a
        // leaf is the aggregate people verify most, and the general path is a pass over the whole table.
        let bytecode_value = if bytecode_point.iter().all(|x| *x == ZERO) {
            E::from(K(stacked_bytecode()[0]))
        } else {
            scalar_bytecode()
                .evaluate(&bytecode_point)
                .expect("the point's length was checked")
        };
        Some(Self {
            bytecode_point,
            bytecode_value,
        })
    }

    /// The cells the statement digest absorbs, in the guest's `defer_stmt` order.
    pub(super) fn cells(&self) -> Vec<E> {
        let mut cells = self.bytecode_point.clone();
        cells.push(self.bytecode_value);
        cells
    }
}

/// The deferred-claim data the guest binds to the outer public input: the outer
/// verifier checks each claim natively (`doc/leanvm/main.tex` §Deferred evaluation claims).
/// A child's fresh claim is batched with its carried one at every child count, one included.
pub(super) struct DeferredSubproof {
    pub(super) public_input: [E; 2],
    pub(super) bytecode_point: Vec<E>,
    pub(super) bytecode_value: E,
}

/// The rows of [`BLOCK`] entries of the stacked bytecode that hold its populated slots: every other row is
/// structurally zero.
fn bytecode_rows() -> Range<usize> {
    static ROWS: std::sync::OnceLock<Range<usize>> = std::sync::OnceLock::new();
    ROWS.get_or_init(|| {
        let rows = stacked_bytecode().as_chunks::<BLOCK>().0;
        let per_slot = rows.len() >> N_BYTECODE_SELECTORS;
        assert!(
            per_slot.is_multiple_of(8),
            "a slot is whole groups of rows, as `Prover::combine_rows` may require"
        );
        let live = |s: &usize| rows[s * per_slot..(s + 1) * per_slot].iter().flatten().any(|&v| v != 0);
        let slots = || 0..1 << N_BYTECODE_SELECTORS;
        let start = slots().find(live).expect("the bytecode is not all zero");
        let end = slots().rfind(live).expect("the bytecode is not all zero") + 1;
        start * per_slot..end * per_slot
    })
    .clone()
}

/// Low row variables of the stacked bytecode, which the batch binds first.
const BLOCK_VARS: usize = 10;
const BLOCK: usize = 1 << BLOCK_VARS;

/// `eq(i, point)` for every index `i`, LSB-first.
fn eq_table<P: Prover>(point: &[E]) -> Vec<E> {
    let mut out = vec![ZERO; 1 << point.len()];
    out[0] = ONE;
    for (k, &r) in point.iter().enumerate() {
        let (low, high) = out[..2 << k].split_at_mut(1 << k);
        for (v, h) in low.iter_mut().zip(high) {
            *h = P::mul(*v, r);
            *v += *h;
        }
    }
    out
}

/// Per claim point, the stacked bytecode with the point's weight on all but the low `BLOCK_VARS` variables summed
/// out: `G(low) = Σ_r eq(point[BLOCK_VARS..], r) · row_r[low]`, over rows `r` of `BLOCK` entries. The weight
/// `eq(point, ·)` is a product of a factor on the low variables and one on the rest, so the batch's low rounds run
/// on these, and a point's value is read off its own ([`bytecode_value`]).
pub(super) fn bytecode_sums<P: Prover>(points: &[Vec<E>]) -> Vec<Vec<E>> {
    let _span = tracing::info_span!("Bytecode sums").entered();
    let (table, live) = (stacked_bytecode(), bytecode_rows());
    points
        .iter()
        .map(|point| {
            // A leaf's claim weighs the first row alone.
            if point.iter().all(|&x| x == ZERO) {
                return table[..BLOCK].iter().map(|&w| E::from(K(w))).collect();
            }
            let eq = eq_table::<P>(&point[BLOCK_VARS..]);
            P::combine_rows(&table[live.start * BLOCK..live.end * BLOCK], &eq[live.clone()])
        })
        .collect()
}

/// The stacked bytecode at `point`, from its [`bytecode_sums`].
pub(super) fn bytecode_value<P: Prover>(sums: &[E], point: &[E]) -> E {
    let eq = eq_table::<P>(&point[..BLOCK_VARS]);
    eq.iter().zip(sums).fold(ZERO, |acc, (&eq, &sum)| acc + P::mul(eq, sum))
}

/// Variables of a bytecode claim's point: the log row count plus the stacking
/// selectors.
pub(super) fn bytecode_vars() -> usize {
    stacked_bytecode().len().trailing_zeros() as usize
}

/// Bind a table's lowest variable to `challenge`.
fn fold_lsb<P: Prover>(table: &mut Vec<E>, challenge: E) {
    let half = table.len() / 2;
    for i in 0..half {
        let (lo, hi) = (table[2 * i], table[2 * i + 1]);
        table[i] = lo + P::mul(challenge, lo + hi);
    }
    table.truncate(half);
}

/// Compressed product-sumcheck round message of `u·m`: (g1, g∞) with g0 recovered from the
/// running claim.
fn round_msg<P: Prover>(u: &[E], m: &[E]) -> (E, E) {
    (0..u.len() / 2).fold((ZERO, ZERO), |acc, i| {
        let (u0, u1) = (u[2 * i], u[2 * i + 1]);
        let (m0, m1) = (m[2 * i], m[2 * i + 1]);
        (acc.0 + P::mul(u1, m1), acc.1 + P::mul(u0 + u1, m0 + m1))
    })
}

/// The grind before the batching challenge, whose powers weigh at most `2 MAX_RECURSIONS` claims.
pub(super) const BATCH_LAM_GRIND_BITS: u32 = grinding_bits(2 * super::MAX_RECURSIONS as u128 - 1);

/// The sponge a protocol with no public input of its own starts from: `label`'s hash as its IV.
pub(super) fn labeled_sponge(label: &[u8]) -> Sponge {
    Sponge::new(Digest(keccak256::hash(label)), Digest([0; 32]))
}

/// Find the smallest nonce whose permutation leaves the low `bits` bits of its proof of work zero, and absorb it, the
/// challenge it draws waiting for the next sample. No nonce at all for `bits = 0`.
fn grind(transcript: &mut Sponge, bits: u32) -> Option<u64> {
    if bits == 0 {
        return None;
    }
    let mask = (1 << bits) - 1;
    let nonce = (0..)
        .find(|&nonce| transcript.clone().absorb_nonce(E::new(nonce, 0)) & mask == 0)
        .expect("a nonce exists");
    transcript.absorb_nonce(E::new(nonce, 0));
    Some(nonce)
}

/// One round of a batching sumcheck, in the transcript order the guest mirrors
/// word for word: observe `(g1, g_inf)`, grind for the round's degree two, squeeze the fold challenge, record
/// the two words and the nonce, if the grind sends one, and advance the running claim through the compressed round polynomial.
/// Returns the challenge, which the caller folds its tables with.
fn absorb_round<P: Prover>(
    transcript: &mut Sponge,
    messages: &mut Vec<E>,
    challenges: &mut Vec<E>,
    claim: &mut E,
    (g1, gi): (E, E),
) -> E {
    transcript.observe(g1);
    transcript.observe(gi);
    let nonce = grind(transcript, grinding_bits(2));
    let challenge = transcript.sample();
    messages.extend([g1, gi]);
    messages.extend(nonce.map(|nonce| E::new(nonce, 0)));
    challenges.push(challenge);
    let g0 = *claim + g1;
    let c1 = g0 + g1 + gi;
    *claim = P::mul(P::mul(gi, challenge) + c1, challenge) + g0;
    challenge
}

/// Mirror the guest's `aggregate_claims` transcript and prove the batching
/// sumcheck over the stacked bytecode.
///
/// Each child brings two claims, the fresh one its verification raised and the one it deferred; `sums` holds their
/// [`bytecode_sums`] in that order. Returns the guest hints and the single claim they reduce to, or `None` when a
/// value is not the bytecode's evaluation.
pub(super) fn aggregate_deferred_claims<P: Prover>(
    subproofs: &[DeferredSubproof],
    carried_claims: &[DeferredBytecodeClaim],
    mut sums: Vec<Vec<E>>,
) -> Option<(SubHints, DeferredBytecodeClaim)> {
    let child_count = subproofs.len();
    assert_eq!(child_count, carried_claims.len(), "one carried claim per child");
    let kbcv = bytecode_vars();

    // The count and each child's words are padded with zeros to whole rates, so the
    // guest's loop over the children finds every child starting the same way.
    let mut transcript = labeled_sponge(RECURSION_AGG_LABEL);
    let pad = |transcript: &mut Sponge, n: usize| {
        for _ in 0..n.next_multiple_of(RATE_SCALARS) - n {
            transcript.observe(ZERO);
        }
    };
    transcript.observe(count(child_count));
    pad(&mut transcript, 1);
    for (subproof, carried) in subproofs.iter().zip(carried_claims) {
        let mut words = vec![subproof.public_input[0], subproof.public_input[1]];
        words.extend(&subproof.bytecode_point);
        words.push(subproof.bytecode_value);
        words.extend(carried.cells());
        for &value in &words {
            transcript.observe(value);
        }
        pad(&mut transcript, words.len());
    }

    let _span = tracing::info_span!("Bytecode batch", vars = kbcv).entered();
    // Powers of one challenge: child i's fresh claim takes lam^(2i), its carried one lam^(2i+1).
    let nonce = grind(&mut transcript, BATCH_LAM_GRIND_BITS);
    let lam = transcript.sample();
    let powers: Vec<E> = std::iter::successors(Some(ONE), |&power| Some(P::mul(power, lam)))
        .take(2 * child_count)
        .collect();
    let points: Vec<Vec<E>> = subproofs
        .iter()
        .zip(carried_claims)
        .flat_map(|(subproof, carried)| [subproof.bytecode_point.clone(), carried.bytecode_point.clone()])
        .collect();
    let values: Vec<E> = subproofs
        .iter()
        .zip(carried_claims)
        .flat_map(|(subproof, carried)| [subproof.bytecode_value, carried.bytecode_value])
        .collect();
    // The running claim: the claims' values weighed by their powers.
    let mut claim = powers
        .iter()
        .zip(&values)
        .fold(ZERO, |acc, (&g, &v)| acc + P::mul(g, v));
    let mut messages: Vec<E> = nonce.map(|nonce| E::new(nonce, 0)).into_iter().collect();
    let mut challenges = Vec::new();
    // The low rounds, on each claim's sums against its `eq` on the low rows, scaled by its power of `lam`.
    assert_eq!(sums.len(), points.len(), "sums for every claim");
    let mut low_weights: Vec<Vec<E>> = points
        .iter()
        .zip(&powers)
        .map(|(point, &power)| {
            let eq = eq_table::<P>(&point[..BLOCK_VARS]);
            eq.into_iter().map(|eq| P::mul(power, eq)).collect()
        })
        .collect();
    for _ in 0..BLOCK_VARS {
        let msg = sums
            .iter()
            .zip(&low_weights)
            .fold((ZERO, ZERO), |acc, (sums, weights)| {
                let (g1, gi) = round_msg::<P>(sums, weights);
                (acc.0 + g1, acc.1 + gi)
            });
        let r = absorb_round::<P>(&mut transcript, &mut messages, &mut challenges, &mut claim, msg);
        for table in sums.iter_mut().chain(&mut low_weights) {
            fold_lsb::<P>(table, r);
        }
    }
    // The rest: every row against the low challenges, zero outside the populated ones, and each claim's `eq` on
    // the rows, scaled by what its low rows left.
    let (table, live) = (stacked_bytecode(), bytecode_rows());
    let mut rows = vec![ZERO; table.len() / BLOCK];
    let dots = P::dot_rows(
        &table[live.start * BLOCK..live.end * BLOCK],
        &eq_table::<P>(&challenges),
    );
    rows[live].copy_from_slice(&dots);
    let mut weights = vec![ZERO; rows.len()];
    for (point, low_weight) in points.iter().zip(&low_weights) {
        for (weight, eq) in weights.iter_mut().zip(eq_table::<P>(&point[BLOCK_VARS..])) {
            *weight += P::mul(low_weight[0], eq);
        }
    }
    for _ in BLOCK_VARS..kbcv {
        let msg = round_msg::<P>(&rows, &weights);
        let r = absorb_round::<P>(&mut transcript, &mut messages, &mut challenges, &mut claim, msg);
        fold_lsb::<P>(&mut rows, r);
        fold_lsb::<P>(&mut weights, r);
    }
    let value = rows[0];
    if claim != P::mul(value, weights[0]) {
        return None;
    }

    drop(_span);
    let hints = vec![("bc_sumcheck_msgs", messages), ("bc_star_hint", vec![value])];
    Some((
        hints,
        DeferredBytecodeClaim {
            bytecode_point: challenges,
            bytecode_value: value,
        },
    ))
}
