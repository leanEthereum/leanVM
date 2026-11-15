//! Step 3's first [`SKIP`] rounds, over the sixteen packs of a group (half a block position), from one pass over
//! the witness.
//!
//! A round reads the summand at `0`, `1` and infinity in its variable, so the four together read it at every point
//! `p` of `{0, 1, infinity}^4`, summed over the groups `g`, the half, block and segment:
//!
//! ```text
//!     sums[p] = sum over g of eq(point[4..], g) * Q(p, g)
//!     Q(p, g) = sum over positions j of weights[j] * (kappa S[j] + (kappa + S[j + 1]) S[j + 2])
//! ```
//!
//! where `S[j]` is group `g`'s packs at position `j` at `s`, multilinear in `p`, a coordinate at infinity being the
//! sum of the two others. At a binary point, a pack, that is the pack's part of `U` at `s`, which the product pass
//! kept. At a mixed point only `weights[j] * S[j + 1] * S[j + 2]` is left, the rest being of degree one in a
//! coordinate at infinity, and its two extended embeddings multiply in one carry-less product. Written as a
//! polynomial in `s` ([`AtS`]), the weight multiplies it in two more, so a block's sums are binary polynomials,
//! evaluated at `s` once per point.

use primitives::bit_fold::BitFold;
use primitives::field::lanes::Wide8;
use primitives::field::{F128, F128Unreduced, clmul8_low, powers};
use primitives::hash::positions::row_positions;
use primitives::multilinear::{eq_table, poly_eval};
use primitives::transcript::ProverState;
use verifier::keccak::PRODUCT_BITS;

use crate::kernels::{PACKS, Run, embed_run, xor};
use crate::layer::{Layer, Sumcheck};
use crate::protocol::Claim;

/// The rounds the skip proves, and the packs of a group they bind.
pub const SKIP: usize = 4;
const GROUP: usize = 1 << SKIP;
/// The points of `{0, 1, infinity}^SKIP`, infinity as digit 2 and variable `k` the `k`-th digit, and those with a
/// digit at infinity.
const TERNARY: usize = 3usize.pow(SKIP as u32);
const MIXED: usize = TERNARY - GROUP;
/// A block's mixed points, both groups'.
const SLOTS: usize = 2 * MIXED;

/// The point of `{0, 1, infinity}^SKIP` of a pack of a group.
const fn ternary(q: usize) -> usize {
    (q & 1) + 3 * (q >> 1 & 1) + 9 * (q >> 2 & 1) + 27 * (q >> 3 & 1)
}

/// The mixed points in increasing order, each with the points at `0` and `1` along its lowest digit at infinity,
/// whose values sum to its own.
const MIXED_POINTS: [[usize; 3]; MIXED] = {
    let mut out = [[0; 3]; MIXED];
    let (mut i, mut t) = (0, 0);
    while t < TERNARY {
        let (mut k, mut step) = (0, 1);
        while k < SKIP && t / step % 3 != 2 {
            k += 1;
            step *= 3;
        }
        if k < SKIP {
            out[i] = [t, t - 2 * step, t - step];
            i += 1;
        }
        t += 1;
    }
    out
};

/// The summand at every point of `{0, 1, infinity}^SKIP`, by its ternary digits. `per_pack` are the packs' parts of
/// `U` from the product pass.
pub(crate) fn sums(layer: &Layer, claim: &Claim, s: F128, per_pack: &[[F128; PRODUCT_BITS]]) -> Vec<F128> {
    let at = AtS::new(s);
    // Word `k` of each position's weight as a polynomial in `s`, at `words[k][j]`.
    let polys: Vec<[u64; 2]> = claim.weights.iter().map(|&w| at.poly(w).to_limbs()).collect();
    let words = [0, 1].map(|k| polys.iter().map(|p| p[k]).collect::<Vec<u64>>());
    // Each task's weight, for each half: the groups of a block alternate.
    let eq = eq_table(&claim.point[SKIP..]);
    let groups = [0, 1].map(|half| layer.task_weights(&eq.iter().skip(half).step_by(2).copied().collect::<Vec<_>>()));
    // Each worker's scratch rides beside its sums.
    let scratch = || (vec![[[0; 8]; SLOTS]; 5], vec![[Wide8::ZERO; 2]; SLOTS]);
    let (_, mixed) = parallel::fold_reduce(
        layer.n_tasks(),
        || (scratch(), [F128Unreduced::ZERO; TERNARY]),
        |((extended, block), sums), task| {
            block_sums(layer.task(task), &words, extended, block);
            for (half, groups) in groups.iter().enumerate() {
                for (i, &[t, ..]) in MIXED_POINTS.iter().enumerate() {
                    let product = block[MIXED * half + i].map(Wide8::sum);
                    sums[t] ^= at.eval(product).mul_unreduced(groups[task]);
                }
            }
        },
        |(kept, mut a), (_, b)| {
            for (a, b) in a.iter_mut().zip(b) {
                *a ^= b;
            }
            (kept, a)
        },
    );
    let mut sums: Vec<F128> = mixed.iter().map(|s| s.reduce()).collect();
    let half = claim.point[SKIP];
    for q in 0..GROUP {
        sums[ternary(q)] = (F128::ONE + half) * poly_eval(&per_pack[q], s) + half * poly_eval(&per_pack[GROUP + q], s);
    }
    sums
}

/// A block's sums at the mixed points of each group: slot `MIXED * half + i` holds `sum over positions j of
/// weights[j] * S[j + 1] * S[j + 2]` at mixed point `i` of group `half`, as its two partial products with the words
/// of the weights. Lane `i` of a slot holds the positions `z + i` of every run: a row of five runs, which `chi`
/// mixes, has eight consecutive positions' weights per run.
fn block_sums(block: &[u64], words: &[Vec<u64>; 2], extended: &mut [[Run; SLOTS]], out: &mut [[Wide8; 2]]) {
    out.fill([Wide8::ZERO; 2]);
    for r in 0..5 {
        for z in (0..64).step_by(8) {
            let js = row_positions(r, z);
            for (extended, &j) in extended.iter_mut().zip(&js) {
                extend(&embed_run(block, j), extended);
            }
            let w: [[Run; 2]; 5] = js.map(|j| words.each_ref().map(|w| w[j..][..8].try_into().expect("a run")));
            for (p, out) in out.iter_mut().enumerate() {
                let mut sum = [Wide8::ZERO; 2];
                for (x, w) in w.iter().enumerate() {
                    let product = clmul8_low(extended[(x + 1) % 5][p], extended[(x + 2) % 5][p]);
                    sum[0] += Wide8::mul(product, w[0]);
                    sum[1] += Wide8::mul(product, w[1]);
                }
                out[0] += sum[0];
                out[1] += sum[1];
            }
        }
    }
}

/// A run's packs at the mixed points of each group, by slot: along a variable, the value at infinity is the sum of
/// the two others.
fn extend(packs: &[Run; PACKS], out: &mut [Run; SLOTS]) {
    // Both groups at once, group `half` in bits `32 * half ..` of each value.
    let mut values = [[0u64; 8]; TERNARY];
    for q in 0..GROUP {
        values[ternary(q)] = std::array::from_fn(|i| packs[q][i] | packs[GROUP + q][i] << 32);
    }
    for &[t, zero, one] in &MIXED_POINTS {
        values[t] = xor(values[zero], values[one]);
    }
    for half in 0..2 {
        for (i, &[t, ..]) in MIXED_POINTS.iter().enumerate() {
            out[MIXED * half + i] = values[t].map(|v| v >> (32 * half) & 0xffff_ffff);
        }
    }
}

/// Send the skip's rounds from the summand at every point they read.
pub(crate) fn prove_rounds(ps: &mut ProverState, claim: &Claim, mut sums: Vec<F128>, sumcheck: &mut Sumcheck) {
    for i in 0..SKIP {
        // The round's values at `0`, `1` and infinity, summed over the later variables' binary points.
        let later = eq_table(&claim.point[i + 1..SKIP]);
        let at = |d: usize| -> F128 {
            later
                .iter()
                .enumerate()
                .map(|(b, &eq)| eq * sums[d + 3 * ternary(b)])
                .sum()
        };
        let c = sumcheck.round(ps, at(0), Some(at(1)), at(2), claim.point[i]);
        // At `c`, a value along the variable is `v0 + c (v0 + v1) + (c^2 + c) v_infinity`.
        sums = sums
            .as_chunks::<3>()
            .0
            .iter()
            .map(|v| v[0] + c * (v[0] + v[1]) + (c.square() + c) * v[2])
            .collect();
    }
}

/// Coefficients a polynomial [`AtS::eval`] reads may have: a weight's 128 and a product's 47.
const COEFFS: usize = 192;

/// Field elements as binary polynomials at `s`.
struct AtS {
    /// An element's coordinates to the polynomial of degree below 128 whose value at `s` is the element.
    unit: BitFold,
    /// A polynomial's coefficients, [`COEFFS`] of them, to its value at `s`.
    powers: BitFold,
}

impl AtS {
    fn new(s: F128) -> Self {
        // Gauss-Jordan on the powers of `s` below 128, each tagged with its exponent: the reduced rows are the unit
        // vectors, tagged with their polynomials.
        let powers = powers(s, COEFFS);
        let mut rows: Vec<(u128, u128)> = (0..128).map(|i| (u128::from(powers[i]), 1u128 << i)).collect();
        for k in 0..128 {
            let pivot = (k..128)
                .find(|&r| rows[r].0 >> k & 1 == 1)
                .expect("the challenge lies in no proper subfield");
            rows.swap(k, pivot);
            let (value, tag) = rows[k];
            for (r, row) in rows.iter_mut().enumerate() {
                if r != k && row.0 >> k & 1 == 1 {
                    *row = (row.0 ^ value, row.1 ^ tag);
                }
            }
        }
        let unit: Vec<F128> = rows.iter().map(|row| F128::from(row.1)).collect();
        Self {
            unit: BitFold::new(&unit),
            powers: BitFold::new(&powers),
        }
    }

    /// The polynomial of degree below 128 whose value at `s` is `w`, its two words as an element's limbs.
    fn poly(&self, w: F128) -> F128 {
        self.unit.fold_row(&u128::from(w).to_le_bytes())
    }

    /// `low + x^64 high` at `s`, for the two partial products of a weight's words.
    fn eval(&self, [low, high]: [u128; 2]) -> F128 {
        let words = [low as u64, (low >> 64) as u64 ^ high as u64, (high >> 64) as u64];
        self.powers.fold_row(words.map(u64::to_le_bytes).as_flattened())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::field::gf2_64::mul_wide;
    use primitives::test_rng::Rng;

    #[test]
    fn polynomials_take_their_values_at_s() {
        let mut rng = Rng::new(41);
        let s = rng.ext();
        let at = AtS::new(s);
        let eval = |words: &[u64]| -> F128 {
            let powers = powers(s, 64 * words.len());
            (0..64 * words.len())
                .filter(|&i| words[i / 64] >> (i % 64) & 1 == 1)
                .map(|i| powers[i])
                .sum()
        };
        for _ in 0..20 {
            let w = rng.ext();
            let p = at.poly(w).to_limbs();
            assert_eq!(eval(&p), w);
            let product = rng.next_u64() >> 17;
            let partial = [mul_wide(product, p[0]), mul_wide(product, p[1])];
            assert_eq!(at.eval(partial), w * eval(&[product]));
        }
    }
}
