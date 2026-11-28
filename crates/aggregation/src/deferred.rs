//! The deferred claim on the stacked bytecode and the sumcheck that batches it.

use super::cells::count;
use super::guest::unified_guest;
use super::hints::Hints;
use fiat_shamir_prover::{FiatShamirState, RATE_SCALARS, Sequential, grinding_bits};
use isa::Prover;
use lean_vm_core::cpu::{from_scalar, to_scalar};
use primitives::field::F128;
use verifier::layout::BUS_BITS;
// `eq` tables on the calling thread: the batch runs under either prover, some of it in its pool's tasks.
use primitives::multilinear::{eq_table_serial as eq_table, interp};
use std::ops::Range;

pub(super) const RECURSION_AGG_LABEL: &[u8] = b"leanvm/recursion-aggregation/v1";

/// The claim on the stacked bytecode that a node defers rather than evaluating
/// in-circuit: one point and value (`doc/leanvm/main.tex` §Deferred evaluation
/// claims).
///
/// Only the point is transmitted; the value is derived from it on receipt, so a
/// prover that lies about a value changes the statement its proof has to satisfy
/// rather than the claim anyone checks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct DeferredBytecodeClaim {
    pub(super) bytecode_point: Vec<F128>,
    pub(super) bytecode_value: F128,
}

impl DeferredBytecodeClaim {
    /// What a leaf defers: the all-zeros point, where the value is just the
    /// table's first entry.
    pub(super) fn leaf() -> Self {
        Self {
            bytecode_point: vec![F128::ZERO; bytecode_vars()],
            bytecode_value: F128::new(unified_guest().stacked_bytecode()[0], 0),
        }
    }

    /// The claim at `bytecode_point`, its value read off the point's [`bytecode_sums`].
    pub(super) fn from_sums(bytecode_point: Vec<F128>, sums: &[F128]) -> Self {
        let bytecode_value = bytecode_value(sums, &bytecode_point);
        Self {
            bytecode_point,
            bytecode_value,
        }
    }

    /// The claim at `bytecode_point`, a point of [`bytecode_vars`] coordinates, evaluated by the `verifier` crate,
    /// scalar and single threaded: what a received aggregate is checked with.
    pub(super) fn recompute(bytecode_point: Vec<F128>) -> Self {
        // Every leaf defers the all-zeros point, where the bytecode polynomial is just its table's first entry: a
        // leaf is the aggregate people verify most, and the general path is a pass over the whole table.
        let bytecode_value = if bytecode_point.iter().all(|x| *x == F128::ZERO) {
            F128::new(unified_guest().stacked_bytecode()[0], 0)
        } else {
            let scalars: Vec<_> = bytecode_point.iter().map(to_scalar).collect();
            from_scalar(
                unified_guest()
                    .bytecode()
                    .evaluate(&scalars)
                    .expect("a point of bytecode_vars() coordinates"),
            )
        };
        Self {
            bytecode_point,
            bytecode_value,
        }
    }

    /// The cells the statement digest absorbs, in the guest's `defer_stmt` order.
    pub(super) fn cells(&self) -> Vec<F128> {
        let mut cells = self.bytecode_point.clone();
        cells.push(self.bytecode_value);
        cells
    }
}

/// The rows of [`BLOCK`] entries of the stacked bytecode that hold its populated slots: every other row is
/// structurally zero.
fn bytecode_rows() -> Range<usize> {
    let rows = unified_guest().stacked_bytecode().as_chunks::<BLOCK>().0;
    let per_slot = rows.len() >> BUS_BITS;
    assert!(
        per_slot.is_multiple_of(8),
        "a slot is whole groups of rows, as `Prover::combine_rows` may require"
    );
    let live = |s: &usize| rows[s * per_slot..(s + 1) * per_slot].iter().flatten().any(|&v| v != 0);
    let slots = || 0..1 << BUS_BITS;
    let start = slots().find(live).expect("the bytecode is not all zero");
    let end = slots().rfind(live).expect("the bytecode is not all zero") + 1;
    start * per_slot..end * per_slot
}

/// Low row variables of the stacked bytecode, which the batch binds first.
const BLOCK_VARS: usize = 10;
const BLOCK: usize = 1 << BLOCK_VARS;

/// The stacked bytecode with the weight of a claim at `point` on all but the low `BLOCK_VARS` variables summed out:
/// `G(low) = Σ_r eq(point[BLOCK_VARS..], r) · row_r[low]`, over rows `r` of `BLOCK` entries. The weight
/// `eq(point, ·)` is a product of a factor on the low variables and one on the rest, so the batch's low rounds run
/// on these, and the point's value is read off them ([`bytecode_value`]).
pub(super) fn bytecode_sums<P: Prover>(point: &[F128]) -> Vec<F128> {
    let table = unified_guest().stacked_bytecode();
    // A leaf's claim weighs the first row alone.
    if point.iter().all(|&x| x == F128::ZERO) {
        return table[..BLOCK].iter().map(|&w| F128::new(w, 0)).collect();
    }
    let live = bytecode_rows();
    let eq: Vec<_> = eq_table(&point[BLOCK_VARS..])[live.clone()]
        .iter()
        .map(to_scalar)
        .collect();
    let sums = P::combine_rows(&table[live.start * BLOCK..live.end * BLOCK], &eq);
    sums.into_iter().map(from_scalar).collect()
}

/// The stacked bytecode at `point`, from its [`bytecode_sums`].
pub(super) fn bytecode_value(sums: &[F128], point: &[F128]) -> F128 {
    eq_table(&point[..BLOCK_VARS])
        .iter()
        .zip(sums)
        .map(|(&eq, &sum)| eq * sum)
        .sum()
}

/// Variables of a bytecode claim's point: the log row count plus the stacking
/// selectors.
pub(super) fn bytecode_vars() -> usize {
    unified_guest().stacked_bytecode().len().trailing_zeros() as usize
}

fn fold_lsb(table: &mut Vec<F128>, challenge: F128) {
    let half = table.len() / 2;
    for i in 0..half {
        table[i] = interp(table[2 * i], table[2 * i + 1], challenge);
    }
    table.truncate(half);
}

/// Compressed product-sumcheck round message of `u·m`: (g1, g∞) with g0 recovered from the
/// running claim.
fn round_msg(u: &[F128], m: &[F128]) -> (F128, F128) {
    let (mut g1, mut gi) = (F128::ZERO, F128::ZERO);
    for i in 0..u.len() / 2 {
        let (u0, u1) = (u[2 * i], u[2 * i + 1]);
        let (m0, m1) = (m[2 * i], m[2 * i + 1]);
        g1 += u1 * m1;
        gi += (u0 + u1) * (m0 + m1);
    }
    (g1, gi)
}

/// The grind before the batching challenge, whose powers weigh at most `2 MAX_RECURSIONS` claims.
pub(super) const BATCH_LAM_GRIND_BITS: u32 = grinding_bits(2 * super::MAX_RECURSIONS as u128 - 1);

/// One round of a batching sumcheck, in the transcript order the guest mirrors
/// word for word: observe `(g1, g_inf)`, grind for the round's degree two, squeeze the fold challenge, record
/// the two words and the nonce, if the grind sends one, and advance the running claim through the compressed round polynomial.
/// Returns the challenge, which the caller folds its tables with.
fn absorb_round(
    transcript: &mut FiatShamirState<F128>,
    messages: &mut Vec<F128>,
    challenges: &mut Vec<F128>,
    claim: &mut F128,
    (g1, gi): (F128, F128),
) -> F128 {
    transcript.observe(g1);
    transcript.observe(gi);
    let nonce = transcript.grind::<Sequential>(grinding_bits(2));
    let challenge = transcript.sample();
    messages.extend([g1, gi]);
    messages.extend(nonce.map(|nonce| F128::new(nonce, 0)));
    challenges.push(challenge);
    let g0 = *claim + g1;
    let c1 = g0 + g1 + gi;
    *claim = (gi * challenge + c1) * challenge + g0;
    challenge
}

/// Mirror the guest's `aggregate_claims` transcript and prove the batching
/// sumcheck over the stacked bytecode.
///
/// Each child brings its public input and two claims, the fresh one its verification raised and the one it deferred:
/// `claims` holds them child by child in that order, and `sums` their [`bytecode_sums`]. A child's fresh claim is
/// batched with its carried one at every child count, one included. Returns the guest hints and the single claim they
/// reduce to.
pub(super) fn aggregate_deferred_claims<P: Prover>(
    public_inputs: &[[F128; 2]],
    claims: &[DeferredBytecodeClaim],
    mut sums: Vec<Vec<F128>>,
) -> (Hints, DeferredBytecodeClaim) {
    let kbcv = bytecode_vars();

    // The count and each child's words are padded with zeros to whole rates, so the
    // guest's loop over the children finds every child starting the same way.
    let mut transcript = FiatShamirState::from_label(RECURSION_AGG_LABEL);
    let pad = |transcript: &mut FiatShamirState<F128>, words: usize| {
        for _ in words..words.next_multiple_of(RATE_SCALARS) {
            transcript.observe(F128::ZERO);
        }
    };
    transcript.observe(count(public_inputs.len()));
    pad(&mut transcript, 1);
    for (public_input, pair) in public_inputs.iter().zip(claims.chunks(2)) {
        for &word in public_input {
            transcript.observe(word);
        }
        let mut words = public_input.len();
        for claim in pair {
            for &word in &claim.bytecode_point {
                transcript.observe(word);
            }
            transcript.observe(claim.bytecode_value);
            words += claim.bytecode_point.len() + 1;
        }
        pad(&mut transcript, words);
    }

    let span = span!("Bytecode batch", vars = kbcv);
    // Powers of one challenge: child i's fresh claim takes lam^(2i), its carried one lam^(2i+1). The batch's grinds
    // are short, so they search on the calling thread, under either prover.
    let nonce = transcript.grind::<Sequential>(BATCH_LAM_GRIND_BITS);
    let lam = transcript.sample();
    // The running claim, the claims' values weighed by their powers. The low rounds run on each claim's sums against
    // its `eq` on the low rows, scaled by its power.
    let mut claim = F128::ZERO;
    let mut low_weights = Vec::with_capacity(claims.len());
    let mut power = F128::ONE;
    for c in claims {
        claim += power * c.bytecode_value;
        let mut weights = eq_table(&c.bytecode_point[..BLOCK_VARS]);
        for weight in &mut weights {
            *weight *= power;
        }
        low_weights.push(weights);
        power *= lam;
    }
    let mut messages: Vec<F128> = nonce.map(|nonce| F128::new(nonce, 0)).into_iter().collect();
    let mut challenges = Vec::new();
    for _ in 0..BLOCK_VARS {
        let mut msg = (F128::ZERO, F128::ZERO);
        for (sums, weights) in sums.iter().zip(&low_weights) {
            let (g1, gi) = round_msg(sums, weights);
            msg = (msg.0 + g1, msg.1 + gi);
        }
        let r = absorb_round(&mut transcript, &mut messages, &mut challenges, &mut claim, msg);
        for table in sums.iter_mut().chain(&mut low_weights) {
            fold_lsb(table, r);
        }
    }
    // The rest: every row against the low challenges, zero outside the populated ones, and each claim's `eq` on
    // the rows, scaled by what its low rows left.
    let (table, live) = (unified_guest().stacked_bytecode(), bytecode_rows());
    let mut rows = vec![F128::ZERO; table.len() / BLOCK];
    let low_eq: Vec<_> = eq_table(&challenges).iter().map(to_scalar).collect();
    let dots = P::dot_rows(&table[live.start * BLOCK..live.end * BLOCK], &low_eq);
    for (row, dot) in rows[live].iter_mut().zip(dots) {
        *row = from_scalar(dot);
    }
    let mut weights = vec![F128::ZERO; rows.len()];
    for (c, low_weight) in claims.iter().zip(&low_weights) {
        for (weight, eq) in weights.iter_mut().zip(eq_table(&c.bytecode_point[BLOCK_VARS..])) {
            *weight += low_weight[0] * eq;
        }
    }
    for _ in BLOCK_VARS..kbcv {
        let msg = round_msg(&rows, &weights);
        let r = absorb_round(&mut transcript, &mut messages, &mut challenges, &mut claim, msg);
        fold_lsb(&mut rows, r);
        fold_lsb(&mut weights, r);
    }
    let value = rows[0];
    assert_eq!(
        claim,
        value * weights[0],
        "every claim's value is the bytecode's evaluation"
    );

    drop(span);
    let mut hints = Hints::default();
    hints.push("bc_sumcheck_msgs", messages);
    hints.push("bc_star_hint", vec![value]);
    let reduced = DeferredBytecodeClaim {
        bytecode_point: challenges,
        bytecode_value: value,
    };
    (hints, reduced)
}
