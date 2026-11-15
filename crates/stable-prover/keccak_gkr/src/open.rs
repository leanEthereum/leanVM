//! From the two claims the layers leave to openings of the commitment.
//!
//! A claim weighs every bit of the committed states it speaks of. The commitment holds those
//! bits as lanes, 64 positions to a word, so an opening is the 64 partial evaluations along `z`
//! at one point of the word index, an instance then a slot. A short sumcheck over the slot (and,
//! for a claim whose instance weights are not an `eq`, over the instances of a pack) gets there.
//! The first claim weighs the bits of a word as the word itself does, so its 64 evaluations
//! are only ever needed as the one they add up to: the committed polynomial at that point.

use pcs::stack_open::{RingSwitchClaim, RingSwitchOpen, StackClaim};
use primitives::field::{F64, F128};
use primitives::multilinear::{eq_table, interp, mle_eval, poly_eval};
use primitives::transcript::ProverState;

use crate::keccak::{BITS, LANES};
use crate::kernels::byte_sums;
use crate::protocol::{Claim, dot};
use crate::witness::{Shape, transpose64};

/// The 64 slices of the committed stack at `point`: bit `z` of every word, as a multilinear.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Opening {
    pub point: Vec<F128>,
    pub slices: Vec<F128>,
}

/// The committed stack at `point`, its words as field elements.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WordOpening {
    pub point: Vec<F128>,
    pub value: F128,
}

/// What the reduction leaves for the commitment to answer: the committed segment outputs as
/// words, if a segment's output is committed at all, and the inputs as slices.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Openings {
    pub outputs: Option<WordOpening>,
    pub inputs: Opening,
}

impl Openings {
    /// The openings as claims on the committed states, placed at `offset` of the stack: the
    /// inputs' ring-switched, the outputs' a point claim to add to the batch.
    pub fn into_pcs_claims(self, offset: usize) -> (RingSwitchOpen, Option<StackClaim>) {
        let ring = RingSwitchOpen {
            offset,
            claims: vec![RingSwitchClaim {
                suffix_point: self.inputs.point,
                s_hat_v: Some(self.inputs.slices),
            }],
        };
        let outputs = self.outputs.map(|outputs| StackClaim {
            offset,
            low_point: outputs.point,
            value: outputs.value,
        });
        (ring, outputs)
    }
}

/// The weight a claim puts on each `(slot, z)`: its position weights, on the slots of the states
/// it speaks of, scaled by the segment. `first` is the state segment 0 claims, and only the first
/// `count` segments' states are committed.
fn slot_weights(shape: Shape, claim: &Claim, first: usize, count: usize) -> Vec<F128> {
    let segments = eq_table(&claim.point[shape.pack_vars()..]);
    let mut out = vec![F128::ZERO; 64 << shape.slot_log()];
    for segment in 0..count {
        let base = 64 * LANES * (first + segment);
        for j in 0..BITS {
            out[base + j] = segments[segment] * claim.weights[j];
        }
    }
    out
}

/// Every slot of the committed block at a pack `point`, keeping the sixteen instances of a pack
/// apart: entry `(i + 16 * slot) * 64 + z` is the sum over packs `y` of `eq(point, y)` times bit
/// `z` of slot `slot` of instance `16 * y + i`. An opening is of the whole block, so the slots the
/// claim puts no weight on are evaluated too: the spare ones past [`Shape::slots`] carry other
/// columns (§cpu), and the fold that follows must see them.
///
/// The words of 64 packs, bit-transposed, give per `z` a byte per eight packs, whose weighted sum
/// is a lookup in the subset sums of those packs' weights.
fn slices(shape: Shape, committed: &[F64], point: &[F128]) -> Vec<F128> {
    let n = shape.n();
    let eq = eq_table(point);
    let chunks = eq.len().div_ceil(64);
    let tables: Vec<[F128; 256]> = parallel::map_collect(8 * chunks, |k| {
        byte_sums(&std::array::from_fn(|t| {
            eq.get(8 * k + t).copied().unwrap_or(F128::ZERO)
        }))
    });
    let slots: Vec<Vec<F128>> = parallel::map_collect(1 << shape.slot_log(), |slot| {
        let words = &committed[slot * n..][..n];
        let mut out = vec![F128::ZERO; 16 * 64];
        for (i, out) in out.as_chunks_mut::<64>().0.iter_mut().enumerate() {
            for chunk in 0..chunks {
                let mut rows: [u64; 64] =
                    std::array::from_fn(|t| words.get(16 * (64 * chunk + t) + i).map_or(0, |w| w.0));
                transpose64(&mut rows);
                for (out, row) in out.iter_mut().zip(rows) {
                    for (b, byte) in row.to_le_bytes().into_iter().enumerate() {
                        *out += tables[8 * chunk + b][byte as usize];
                    }
                }
            }
        }
        out
    });
    slots.concat()
}

/// The sum over rows of the two tables' dot product: its round values at `0` and infinity.
fn round_values(a: &[F128], b: &[F128], width: usize) -> (F128, F128) {
    let mut zero = F128::ZERO;
    let mut infinity = F128::ZERO;
    for (a, b) in a.chunks_exact(2 * width).zip(b.chunks_exact(2 * width)) {
        for j in 0..width {
            zero += a[j] * b[j];
            infinity += (a[j] + a[width + j]) * (b[j] + b[width + j]);
        }
    }
    (zero, infinity)
}

/// `table`, rows of `width`, with the row index's lowest variable bound at `challenge`.
pub(crate) fn fold(table: &[F128], width: usize, challenge: F128) -> Vec<F128> {
    table
        .chunks_exact(2 * width)
        .flat_map(|pair| (0..width).map(move |j| interp(pair[j], pair[width + j], challenge)))
        .collect()
}

/// The sumcheck of `scale * sum of a * b` over the row index, rows of `width`, its lowest variable first, down to one
/// row of each: returns those rows and the point.
fn prove_rounds(
    ps: &mut ProverState,
    mut a: Vec<F128>,
    mut b: Vec<F128>,
    width: usize,
    scale: F128,
    value: &mut F128,
) -> (Vec<F128>, Vec<F128>, Vec<F128>) {
    let mut point = Vec::new();
    while a.len() > width {
        let (zero, infinity) = round_values(&a, &b, width);
        let (zero, infinity) = (scale * zero, scale * infinity);
        let coeffs = [zero, *value + infinity, infinity];
        ps.add_round_poly(&coeffs, false);
        let challenge = ps.sample();
        *value = poly_eval(&coeffs, challenge);
        point.push(challenge);
        a = fold(&a, width, challenge);
        b = fold(&b, width, challenge);
    }
    (a, b, point)
}

/// The weight a word-level claim puts on each slot of the committed segment outputs, every
/// segment's but the last: what [`slot_weights`] gives its bit 0.
fn word_weights(shape: Shape, claim: &Claim) -> Vec<F128> {
    slot_weights(shape, claim, 1, shape.segments() - 1)
        .into_iter()
        .step_by(64)
        .collect()
}

/// Every slot of the committed block as a word, at an instance point, and the part of the
/// word-level `claim` on the committed segment outputs among them. An opening is of the whole
/// block, so the slots the claim puts no weight on are evaluated too: the spare ones past
/// [`Shape::slots`] carry other columns (§cpu), and the fold that follows must see them.
pub fn output_words(shape: Shape, committed: &[F64], instance: &[F128], claim: &Claim) -> (Vec<F128>, F128) {
    let n = shape.n();
    let words = parallel::map_collect(1 << shape.slot_log(), |slot| {
        mle_eval(&committed[slot * n..][..n], instance)
    });
    let value = dot(&words, &word_weights(shape, claim));
    (words, value)
}

/// Open `value`, the part of the first claim on the committed segment outputs, whose instance
/// weights are `eq(instance, .)` and whose position weights are those of a word.
pub fn open_outputs(
    ps: &mut ProverState,
    shape: Shape,
    instance: &[F128],
    claim: &Claim,
    mut value: F128,
    words: Vec<F128>,
) -> WordOpening {
    let (word, _, slot) = prove_rounds(ps, words, word_weights(shape, claim), 1, F128::ONE, &mut value);
    let word = word[0];
    ps.add_scalar(word);
    WordOpening {
        point: [instance, &slot].concat(),
        value: word,
    }
}

/// Open the claim on the inputs: the instances of a pack first, then the slot.
pub fn open_inputs(ps: &mut ProverState, shape: Shape, committed: &[F64], claim: &Claim) -> Opening {
    let pack = &claim.point[..shape.pack_vars()];
    let folded = slices(shape, committed, pack);
    let weights = slot_weights(shape, claim, 0, shape.segments());
    // Per instance of a pack, the weighted sum over slots and positions.
    let per_instance: Vec<F128> = (0..16)
        .map(|i| {
            (0..1usize << shape.slot_log())
                .map(|slot| dot(&folded[(i + 16 * slot) * 64..][..64], &weights[slot * 64..][..64]))
                .sum()
        })
        .collect();
    let mut value = claim.value;
    let (_, mu, low) = prove_rounds(ps, per_instance, claim.mu.to_vec(), 1, F128::ONE, &mut value);
    // The slots of the stack at that instance: entry `(i + 16 * slot) * 64 + z` folds over `i`.
    let mut at_instance = vec![F128::ZERO; 64 << shape.slot_log()];
    let low_eq = eq_table(&low);
    for (slot, out) in at_instance.as_chunks_mut::<64>().0.iter_mut().enumerate() {
        for i in 0..16 {
            for z in 0..64 {
                out[z] += low_eq[i] * folded[(i + 16 * slot) * 64 + z];
            }
        }
    }
    let (slices, _, slot) = prove_rounds(ps, at_instance, weights, 64, mu[0], &mut value);
    ps.add_scalars(&slices);
    Opening {
        point: [&low, pack, &slot].concat(),
        slices,
    }
}
