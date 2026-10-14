//! From the two claims the layers leave to openings of the commitment.
//!
//! A claim weighs every bit of the committed states it speaks of. The commitment holds those
//! bits as lanes, 64 positions to a word, so an opening is the 64 partial evaluations along `z`
//! at one point of the word index, an instance then a slot. A short sumcheck over the slot (and,
//! for a claim whose instance weights are not an `eq`, over the instances of a pack) gets there.
//! The first claim weighs the bits of a word as the word itself does, so its 64 evaluations
//! are only ever needed as the one they add up to: the committed polynomial at that point.

use fiat_shamir::transcript::{Receiver, Transmitter};
use primitives::field::{F64, F192, F192Unreduced};
use primitives::multilinear::{eq_table, mle_eval, poly_eval};

use crate::keccak::{BITS, LANES, along, iota_bit};
use crate::protocol::{Claim, VerifyError, dot};
use crate::witness::{BLOCK_WORDS, Shape, Witness};

/// The 64 slices of the committed stack at `point`: bit `z` of every word, as a multilinear.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Opening {
    pub point: Vec<F192>,
    pub slices: Vec<F192>,
}

/// The committed stack at `point`, its words as field elements.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WordOpening {
    pub point: Vec<F192>,
    pub value: F192,
}

/// What the reduction leaves for the commitment to answer: the committed segment outputs as
/// words, if a segment's output is committed at all, and the inputs as slices.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Openings {
    pub outputs: Option<WordOpening>,
    pub inputs: Opening,
}

/// The weight a claim puts on each `(slot, z)`: its position weights, on the slots of the states
/// it speaks of, scaled by the segment. `first` is the state segment 0 claims, and only the first
/// `count` segments' states are committed.
pub fn slot_weights(shape: Shape, claim: &Claim, first: usize, count: usize) -> Vec<F192> {
    let segments = eq_table(&claim.point[shape.pack_vars()..]);
    let mut out = vec![F192::ZERO; 64 << shape.slot_log()];
    for segment in 0..count {
        let base = 64 * LANES * (first + segment);
        for j in 0..BITS {
            out[base + j] = segments[segment] * claim.weights[j];
        }
    }
    out
}

/// One word of the sliced state after a round, from the state the round applies `chi` to.
#[inline(always)]
fn chi_word(block: &[u64], round: usize, j: usize, w: usize) -> u64 {
    let chi =
        block[j * BLOCK_WORDS + w] ^ (!block[along(j, 1) * BLOCK_WORDS + w] & block[along(j, 2) * BLOCK_WORDS + w]);
    if j < 64 && iota_bit(round, j) { !chi } else { chi }
}

/// The eight words of position `j` in block `g` of the state after `round` rounds.
#[inline(always)]
fn state_words(witness: &Witness, round: usize, g: usize, j: usize) -> [u64; BLOCK_WORDS] {
    if round == 0 {
        let at = j * BLOCK_WORDS;
        return witness.input(g)[at..at + BLOCK_WORDS].try_into().expect("eight words");
    }
    let block = witness.layer(round, g);
    std::array::from_fn(|w| chi_word(block, round, j, w))
}

fn subset_sums(weights: &[F192]) -> Vec<[F192; 256]> {
    weights
        .chunks(8)
        .map(|chunk| {
            let mut t = [F192::ZERO; 256];
            for (bit, &w) in chunk.iter().enumerate() {
                for byte in 1usize << bit..2 << bit {
                    t[byte] = t[byte - (1 << bit)] + w;
                }
            }
            t
        })
        .collect()
}

/// Every position of every committed state, at a pack `point`, keeping the sixteen instances
/// of a pack apart: entry `(i + 16 * slot) * 64 + z`.
///
/// The weight of a pack is a product over its index in a run of blocks and the run's own
/// index. The first factor meets the bits as subset sums, a table per pack of a word and block
/// of the run, so only a run's sum is multiplied.
fn fold_packs(witness: &Witness, point: &[F192]) -> Vec<F192> {
    let shape = witness.shape;
    let run_vars = (point.len() - 5).min(3);
    let (low, runs) = (eq_table(&point[..5 + run_vars]), eq_table(&point[5 + run_vars..]));
    // Table `4 * block + p`: pack `p + 4 * w` of the run's block, over the eight words `w`.
    let tables: Vec<[F192; 256]> = (0..4 << run_vars)
        .map(|t| subset_sums(&(0..8).map(|w| low[t % 4 + 4 * w + 32 * (t / 4)]).collect::<Vec<_>>())[0])
        .collect();
    let lanes = shape.slots();
    let mut out = vec![F192::ZERO; (16 * 64) << shape.slot_log()];
    parallel::chunks_mut(&mut out[..16 * 64 * lanes], 16 * 64, |lane, out| {
        let round = shape.depth * (lane / LANES);
        for z in 0..64 {
            let mut acc = [F192Unreduced::ZERO; 16];
            for (run, &scale) in runs.iter().enumerate() {
                let mut sums = [F192::ZERO; 16];
                for block in 0..1 << run_vars {
                    let words = state_words(witness, round, (run << run_vars) + block, 64 * (lane % LANES) + z);
                    // Byte `8 * b + t` gathers bit `t` of byte `b` of each word: instance
                    // `8 * (b % 2) + t` of pack `b / 2`, across the eight words.
                    let mut gathered = [0u8; 64];
                    primitives::bits::bit_transpose_64bytes(bytes_of(&words), &mut gathered);
                    for (i, sum) in sums.iter_mut().enumerate() {
                        for p in 0..4 {
                            *sum += tables[4 * block + p][gathered[8 * (2 * p + i / 8) + i % 8] as usize];
                        }
                    }
                }
                for (acc, sum) in acc.iter_mut().zip(sums) {
                    *acc ^= scale.mul_unreduced(sum);
                }
            }
            for (i, acc) in acc.into_iter().enumerate() {
                out[i * 64 + z] = acc.reduce();
            }
        }
    });
    out
}

fn bytes_of(words: &[u64; BLOCK_WORDS]) -> &[u8; 64] {
    // SAFETY: eight words are 64 bytes, and on this little-endian target byte `b` of word `x`
    // is byte `8 * x + b`.
    unsafe { &*words.as_ptr().cast() }
}

/// The sum over rows of the two tables' dot product: its round values at `0` and infinity.
fn round_values(a: &[F192], b: &[F192], width: usize) -> (F192, F192) {
    let mut zero = F192::ZERO;
    let mut infinity = F192::ZERO;
    for (a, b) in a.chunks_exact(2 * width).zip(b.chunks_exact(2 * width)) {
        for j in 0..width {
            zero += a[j] * b[j];
            infinity += (a[j] + a[width + j]) * (b[j] + b[width + j]);
        }
    }
    (zero, infinity)
}

fn fold(table: &[F192], width: usize, rho: F192) -> Vec<F192> {
    table
        .chunks_exact(2 * width)
        .flat_map(|pair| (0..width).map(move |j| pair[j] + rho * (pair[j] + pair[width + j])))
        .collect()
}

/// Bind the leading variable of `scale * sum of a * b` in every round, down to one row of `a`.
fn prove_rounds(
    ps: &mut impl Transmitter,
    mut a: Vec<F192>,
    mut b: Vec<F192>,
    width: usize,
    scale: F192,
    value: &mut F192,
) -> (Vec<F192>, Vec<F192>, Vec<F192>) {
    let mut point = Vec::new();
    while a.len() > width {
        let (zero, infinity) = round_values(&a, &b, width);
        let (zero, infinity) = (scale * zero, scale * infinity);
        let coeffs = [zero, *value + infinity, infinity];
        ps.add_round_poly(&coeffs, false);
        let rho = ps.sample();
        *value = poly_eval(&coeffs, rho);
        point.push(rho);
        a = fold(&a, width, rho);
        b = fold(&b, width, rho);
    }
    (a, b, point)
}

fn verify_rounds(vs: &mut impl Receiver, rounds: usize, value: &mut F192) -> Result<Vec<F192>, VerifyError> {
    let mut point = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let h = vs.next_round_poly(3, *value, None)?;
        let rho = vs.sample();
        *value = poly_eval(&h, rho);
        point.push(rho);
    }
    Ok(point)
}

fn fold_all(mut table: Vec<F192>, width: usize, point: &[F192]) -> Vec<F192> {
    for &rho in point {
        table = fold(&table, width, rho);
    }
    table
}

/// The weight a word-level claim puts on each slot: what [`slot_weights`] gives its bit 0.
/// The word weights of the committed segment outputs: every segment's but the last, whose output
/// is not committed.
fn word_weights(shape: Shape, claim: &Claim) -> Vec<F192> {
    slot_weights(shape, claim, 1, shape.segments() - 1)
        .into_iter()
        .step_by(64)
        .collect()
}

/// Every committed lane as a word, at an instance point, and the part of the word-level `claim`
/// on the committed segment outputs among them. An opening is of the whole stack, so the lanes
/// the claim puts no weight on are evaluated too.
pub fn output_claim(shape: Shape, committed: &[F64], instance: &[F192], claim: &Claim) -> (Vec<F192>, F192) {
    let n = shape.n();
    let mut words = parallel::map_collect(shape.slots(), |slot| mle_eval(&committed[slot * n..][..n], instance));
    words.resize(1 << shape.slot_log(), F192::ZERO);
    let value = dot(&words, &word_weights(shape, claim));
    (words, value)
}

/// Open `value`, the part of the first claim on the committed segment outputs, whose instance
/// weights are `eq(instance, .)` and whose position weights are those of a word.
pub fn open_outputs(
    ps: &mut impl Transmitter,
    shape: Shape,
    instance: &[F192],
    claim: &Claim,
    mut value: F192,
    words: Vec<F192>,
) -> WordOpening {
    let (word, _, slot) = prove_rounds(ps, words, word_weights(shape, claim), 1, F192::ONE, &mut value);
    let word = word[0];
    ps.add_scalar(word);
    WordOpening {
        point: [instance, &slot].concat(),
        value: word,
    }
}

pub fn verify_outputs(
    vs: &mut impl Receiver,
    shape: Shape,
    instance: &[F192],
    claim: &Claim,
    mut value: F192,
) -> Result<WordOpening, VerifyError> {
    let slot = verify_rounds(vs, shape.slot_log(), &mut value)?;
    let word = vs.next_scalar()?;
    if fold_all(word_weights(shape, claim), 1, &slot)[0] * word != value {
        return Err(VerifyError::Opening);
    }
    Ok(WordOpening {
        point: [instance, &slot].concat(),
        value: word,
    })
}

/// Open the claim on the inputs: the instances of a pack first, then the slot.
pub fn open_inputs(ps: &mut impl Transmitter, witness: &Witness, claim: &Claim) -> Opening {
    let shape = witness.shape;
    let pack = &claim.point[..shape.pack_vars()];
    let folded = fold_packs(witness, pack);
    let weights = slot_weights(shape, claim, 0, shape.segments());
    // Per instance of a pack, the weighted sum over slots and positions.
    let per_instance: Vec<F192> = (0..16)
        .map(|i| {
            (0..1usize << shape.slot_log()).fold(F192::ZERO, |acc, slot| {
                acc + dot(&folded[(i + 16 * slot) * 64..][..64], &weights[slot * 64..][..64])
            })
        })
        .collect();
    let mut value = claim.value;
    let (_, mu, low) = prove_rounds(ps, per_instance, claim.mu.to_vec(), 1, F192::ONE, &mut value);
    // The slots of the stack at that instance: entry `(i + 16 * slot) * 64 + z` folds over `i`.
    let mut at_instance = vec![F192::ZERO; 64 << shape.slot_log()];
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

pub fn verify_inputs(vs: &mut impl Receiver, shape: Shape, claim: &Claim) -> Result<Opening, VerifyError> {
    let mut value = claim.value;
    let low = verify_rounds(vs, 4, &mut value)?;
    let mu = dot(&eq_table(&low), &claim.mu);
    let slot = verify_rounds(vs, shape.slot_log(), &mut value)?;
    let slices = vs.next_scalars(64)?;
    if mu
        * dot(
            &fold_all(slot_weights(shape, claim, 0, shape.segments()), 64, &slot),
            &slices,
        )
        != value
    {
        return Err(VerifyError::Opening);
    }
    Ok(Opening {
        point: [&low, &claim.point[..shape.pack_vars()], &slot].concat(),
        slices,
    })
}
