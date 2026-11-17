//! From the two claims the layers leave to openings of the commitment.
//!
//! A claim weighs every bit of the committed states it speaks of. The commitment holds those
//! bits as lanes, 64 positions to a word, so an opening is the 64 partial evaluations along `z`
//! at one point of the word index, an instance then a slot. A short sumcheck over the slot (and,
//! for a claim whose instance weights are not an `eq`, over the instances of a pack) gets there.
//! The first claim weighs the bits of a word as the word itself does, so its 64 evaluations
//! are only ever needed as the one they add up to: the committed polynomial at that point.

use pcs::stack_open::{RingSwitchClaim, RingSwitchOpen, StackClaim};
use primitives::bit_fold::{BLOCK as ROWS, BitFold};
use primitives::field::{F64, F128, F128Unreduced};
use primitives::hash::STATE_LANES;
use primitives::hash::positions::iota_bit;
use primitives::multilinear::{eq_table, interp, mle_eval, poly_eval};
use primitives::transcript::ProverState;
use verifier::keccak::{BITS, along};

use crate::protocol::{Claim, dot};
use crate::witness::{BLOCK_WORDS, Shape, Witness, words};

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
        let outputs = self.outputs.map(|outputs| StackClaim::Point {
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
pub fn slot_weights(shape: Shape, claim: &Claim, first: usize, count: usize) -> Vec<F128> {
    let segments = eq_table(&claim.point[shape.pack_vars()..]);
    let mut out = vec![F128::ZERO; 64 << shape.slot_log()];
    for segment in 0..count {
        let base = 64 * STATE_LANES * (first + segment);
        for j in 0..BITS {
            out[base + j] = segments[segment] * claim.weights[j];
        }
    }
    out
}

/// The eight words of position `j` in block `g` of the state after `round` rounds: the input for
/// round 0, else `chi` and `iota` on the layer `round` applies them to.
#[inline(always)]
pub(crate) fn state_words(witness: &Witness, round: usize, g: usize, j: usize) -> [u64; BLOCK_WORDS] {
    let block = witness.layer(round, g);
    let a = words(block, j);
    if round == 0 {
        return *a;
    }
    let (b, c) = (words(block, along(j, 1)), words(block, along(j, 2)));
    let iota = if j < 64 && iota_bit(round, j) { !0 } else { 0 };
    std::array::from_fn(|w| a[w] ^ (!b[w] & c[w]) ^ iota)
}

/// Every position of every committed state, at a pack `point`, keeping the sixteen instances
/// of a pack apart: entry `(i + 16 * slot) * 64 + z`.
///
/// The weight of a pack is a product over its index in a run of blocks and the run's own
/// index. The first factor is a fixed weight per bit of a run, so a run's bits meet it as one
/// [`BitFold`] row per position and instance, and only a run's sum is multiplied. Every bit of
/// the padding block is that of its first word, so the blocks it stands for weigh it together.
fn fold_packs(witness: &Witness, point: &[F128]) -> Vec<F128> {
    let shape = witness.shape;
    let written = witness.written();
    let padding = eq_table(&point[5..])[written..].iter().sum();
    let run_vars = (point.len() - 5).min(3);
    let (low, runs) = (eq_table(&point[..5 + run_vars]), eq_table(&point[5 + run_vars..]));
    // Bit `w` of byte `4 * block + p` of a row is pack `p + 4 * w` of the run's block. A run has
    // eight blocks but at small batches, and the bytes past it weigh nothing.
    let weights: Vec<F128> = (0..8 * 32)
        .map(|b| {
            let (block, p, w) = (b / 32, b / 8 % 4, b % 8);
            low.get(32 * block + 4 * w + p).copied().unwrap_or(F128::ZERO)
        })
        .collect();
    let fold = BitFold::new(&weights);
    // A task per four positions `j ..` of a lane, row `16 * dz + i` being instance `i` of a pack
    // at `j + dz`.
    let positions: Vec<[F128; ROWS]> = parallel::map_collect(16 * shape.slots(), |task| {
        let lane = task / 16;
        let round = shape.depth * (lane / STATE_LANES);
        let j = 64 * (lane % STATE_LANES) + 4 * (task % 16);
        let mut acc = [F128Unreduced::ZERO; ROWS];
        for (run, &scale) in runs.iter().enumerate().take(written.div_ceil(1 << run_vars)) {
            let mut cols = [[0u8; ROWS]; 32];
            for block in 0..(1 << run_vars).min(written - (run << run_vars)) {
                for dz in 0..4 {
                    let words = state_words(witness, round, (run << run_vars) + block, j + dz);
                    // Byte `16 * p + i` gathers instance `i` of pack `p + 4 * w` at bit `w`.
                    let mut gathered = [0u8; 64];
                    primitives::bits::bit_transpose_64bytes(&le_bytes(&words), &mut gathered);
                    for (p, gathered) in gathered.as_chunks::<16>().0.iter().enumerate() {
                        cols[4 * block + p][16 * dz..][..16].copy_from_slice(gathered);
                    }
                }
            }
            let mut sums = [F128::ZERO; ROWS];
            fold.fold_columns(&cols, &mut sums);
            for (acc, sum) in acc.iter_mut().zip(sums) {
                *acc ^= scale.mul_unreduced(sum);
            }
        }
        let pad: [bool; 4] = std::array::from_fn(|dz| {
            written < shape.n_blocks() && state_words(witness, round, written, j + dz)[0] & 1 == 1
        });
        std::array::from_fn(|r| acc[r].reduce() + if pad[r / 16] { padding } else { F128::ZERO })
    });
    let mut out = vec![F128::ZERO; (16 * 64) << shape.slot_log()];
    for (task, sums) in positions.iter().enumerate() {
        let (lane, z) = (task / 16, 4 * (task % 16));
        for (r, &sum) in sums.iter().enumerate() {
            out[(r % 16 + 16 * lane) * 64 + z + r / 16] = sum;
        }
    }
    out
}

/// Byte `b` of word `x` at `8 * x + b`.
fn le_bytes(words: &[u64; BLOCK_WORDS]) -> [u8; 64] {
    let mut bytes = [0u8; 64];
    for (bytes, word) in bytes.as_chunks_mut::<8>().0.iter_mut().zip(words) {
        *bytes = word.to_le_bytes();
    }
    bytes
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

fn fold(table: &[F128], width: usize, challenge: F128) -> Vec<F128> {
    table
        .chunks_exact(2 * width)
        .flat_map(|pair| (0..width).map(move |j| interp(pair[j], pair[width + j], challenge)))
        .collect()
}

/// Bind the leading variable of `scale * sum of a * b` in every round, down to one row of `a`.
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
pub fn output_claim(shape: Shape, committed: &[F64], instance: &[F128], claim: &Claim) -> (Vec<F128>, F128) {
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

/// Instance variables of a [`spare_slices`] chunk.
const CHUNK_VARS: usize = 8;

/// The bit slices, at the instance point, of the committed slots the claim weighs nothing on:
/// the spare ones past [`Shape::slots`], where other columns ride (§cpu). The reduction says
/// nothing about them, but the claim it leaves is on the whole committed block, so the slot
/// fold below has to carry their bits.
///
/// Slice `z` of slot `s` is `Σ_step eq(instance, step) · bit z of committed[s·n + step]`. The
/// `eq` table is the product of one on the low [`CHUNK_VARS`] instance variables and one on the
/// rest, so a chunk of steps is one [`BitFold`] by the low table, row `z` being the chunk's bits
/// `z` read off their transposed bytes, and only the chunk's 64 sums meet the high table.
fn spare_slices(shape: Shape, committed: &[F64], instance: &[F128]) -> Vec<[F128; 64]> {
    let (n, spare) = (shape.n(), (1 << shape.slot_log()) - shape.slots());
    // An instance point has `Shape::n_log` variables, at least nine.
    let (low, high) = instance.split_at(CHUNK_VARS);
    let (fold, high) = (BitFold::new(&eq_table(low)), eq_table(high));
    let slots = &committed[shape.slots() * n..];
    // A task per chunk and slot: at small batches there are few of either.
    let slices = parallel::fold_reduce(
        (n >> CHUNK_VARS) * spare,
        || vec![[F128Unreduced::ZERO; 64]; spare],
        |acc, task| {
            let (chunk, slot) = (task / spare, task % spare);
            let steps = &slots[slot * n + (chunk << CHUNK_VARS)..][..1 << CHUNK_VARS];
            // Column `g` gathers bit `z` of the eight steps `8 * g ..` at byte `z`.
            let mut cols = [[0u8; ROWS]; (1 << CHUNK_VARS) / 8];
            for (col, steps) in cols.iter_mut().zip(steps.as_chunks::<8>().0) {
                primitives::bits::bit_transpose_64bytes(&le_bytes(&steps.map(|step| step.0)), col);
            }
            let mut sums = [F128::ZERO; ROWS];
            fold.fold_columns(&cols, &mut sums);
            for (acc, sum) in acc[slot].iter_mut().zip(sums) {
                *acc ^= high[chunk].mul_unreduced(sum);
            }
        },
        |mut a, b| {
            for (a, b) in a.iter_mut().flatten().zip(b.iter().flatten()) {
                *a ^= *b;
            }
            a
        },
    );
    slices.iter().map(|slice| slice.map(F128Unreduced::reduce)).collect()
}

/// Open the claim on the inputs: the instances of a pack first, then the slot.
pub fn open_inputs(ps: &mut ProverState, witness: &Witness, committed: &[F64], claim: &Claim) -> Opening {
    let shape = witness.shape;
    let pack = &claim.point[..shape.pack_vars()];
    let folded = fold_packs(witness, pack);
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
    for (slot, slices) in spare_slices(shape, committed, &[&low, pack].concat())
        .into_iter()
        .enumerate()
    {
        at_instance[(shape.slots() + slot) * 64..][..64].copy_from_slice(&slices);
    }
    let (slices, _, slot) = prove_rounds(ps, at_instance, weights, 64, mu[0], &mut value);
    ps.add_scalars(&slices);
    Opening {
        point: [&low, pack, &slot].concat(),
        slices,
    }
}
