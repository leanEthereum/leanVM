//! The deferred claim on the stacked bytecode and the sumcheck that batches it.

use super::cells::count;
use super::guest::unified_guest;
use super::hints::Hints;
use fiat_shamir_prover::{FiatShamirState, RATE_SCALARS, Sequential, grinding_bits};
use isa::Prover;
use lean_vm_core::cpu::{from_scalar, to_scalar};
use primitives::field::{F128, axpy, dot, powers};
use verifier::layout::BUS_BITS;
// `eq` tables on the calling thread: the batch runs under either prover, some of it in its pool's tasks.
use primitives::multilinear::{eq_table_serial as eq_table, fold};
use std::ops::Range;

pub(super) const RECURSION_AGG_LABEL: &[u8] = b"leanvm/recursion-aggregation/v1";

/// The claim on the stacked bytecode that a node defers rather than evaluating
/// in-circuit: one point and value (`doc/leanvm/main.tex` §Deferred evaluation
/// claims).
///
/// Only the point is transmitted; the value is derived from it on receipt, so a
/// prover that lies about a value changes the statement its proof has to satisfy
/// rather than the claim anyone checks.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
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

/// The rows of [`BLOCK`] entries of the stacked bytecode that hold its populated slots ([`isa::BYTECODE_SLOTS`]):
/// every other row is structurally zero.
fn bytecode_rows() -> Range<usize> {
    let per_slot = (unified_guest().stacked_bytecode().len() / BLOCK) >> BUS_BITS;
    assert!(
        per_slot.is_multiple_of(8),
        "a slot is whole groups of rows, as `Prover::combine_rows` may require"
    );
    isa::BYTECODE_SLOTS.start * per_slot..isa::BYTECODE_SLOTS.end * per_slot
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
    dot(&eq_table(&point[..BLOCK_VARS]), sums)
}

/// Variables of a bytecode claim's point: the log row count plus the stacking
/// selectors.
pub(super) fn bytecode_vars() -> usize {
    unified_guest().stacked_bytecode().len().trailing_zeros() as usize
}

/// One round of a product sumcheck of `u·m`, in the transcript order the guest mirrors word for word: observe the
/// compressed message `(g1, g_inf)` (`g0` follows from the running claim), grind for the round's degree two, squeeze
/// the challenge, record the two words and the nonce, if the grind sends one, and fold both tables on their low
/// variable at the challenge.
fn round(
    transcript: &mut FiatShamirState<F128>,
    messages: &mut Vec<F128>,
    challenges: &mut Vec<F128>,
    u: &mut Vec<F128>,
    m: &mut Vec<F128>,
) {
    let (mut g1, mut gi) = (F128::ZERO, F128::ZERO);
    for i in 0..u.len() / 2 {
        let (u0, u1) = (u[2 * i], u[2 * i + 1]);
        let (m0, m1) = (m[2 * i], m[2 * i + 1]);
        g1 += u1 * m1;
        gi += (u0 + u1) * (m0 + m1);
    }
    transcript.observe(g1);
    transcript.observe(gi);
    let nonce = transcript.grind::<Sequential>(grinding_bits(2));
    let challenge = transcript.sample();
    messages.extend_from_slice(&[g1, gi]);
    messages.extend(nonce.map(|nonce| F128::new(nonce, 0)));
    challenges.push(challenge);
    *u = fold(u, 1, challenge);
    *m = fold(m, 1, challenge);
}

/// The grind before the batching challenge, whose powers weigh at most `2 MAX_RECURSIONS` claims.
pub(super) const BATCH_LAM_GRIND_BITS: u32 = grinding_bits(2 * super::MAX_RECURSIONS as u128 - 1);

/// Mirror the guest's `aggregate_claims` transcript and prove the batching
/// sumcheck over the stacked bytecode.
///
/// Each child brings its public input and two claims, the fresh one its verification raised and the one it deferred:
/// `claims` holds them child by child in that order, and `sums` their [`bytecode_sums`] end to end. A child's fresh
/// claim is batched with its carried one at every child count, one included. Returns the guest hints and the single
/// claim they reduce to.
pub(super) fn aggregate_deferred_claims<P: Prover>(
    public_inputs: &[[F128; 2]],
    claims: &[DeferredBytecodeClaim],
    mut sums: Vec<F128>,
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
        transcript.observe(public_input[0]);
        transcript.observe(public_input[1]);
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
    let mut messages = Vec::new();
    messages.extend(nonce.map(|nonce| F128::new(nonce, 0)));
    let mut challenges = Vec::new();
    // The low rounds run on the claims' sums end to end against their `eq` on the low rows, each scaled by its power:
    // a claim's run folds within itself, to its value and its weight.
    let mut low_weights = vec![F128::ZERO; sums.len()];
    for (i, (c, power)) in claims.iter().zip(powers(lam, claims.len())).enumerate() {
        let eq = eq_table(&c.bytecode_point[..BLOCK_VARS]);
        axpy(&mut low_weights[i * BLOCK..][..BLOCK], power, &eq);
    }
    for _ in 0..BLOCK_VARS {
        round(
            &mut transcript,
            &mut messages,
            &mut challenges,
            &mut sums,
            &mut low_weights,
        );
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
    for (c, &low_weight) in claims.iter().zip(&low_weights) {
        axpy(&mut weights, low_weight, &eq_table(&c.bytecode_point[BLOCK_VARS..]));
    }
    for _ in BLOCK_VARS..kbcv {
        round(&mut transcript, &mut messages, &mut challenges, &mut rows, &mut weights);
    }
    // The guest checks that the claims' batched values are this one's.
    let value = rows[0];

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
