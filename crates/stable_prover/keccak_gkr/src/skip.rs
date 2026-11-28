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
use primitives::field::{F128, F128Unreduced, clmul8_low, mul};
use primitives::hash::positions::row_positions;
use primitives::multilinear::{eq_table, poly_eval};
use primitives::transcript::ProverState;
use verifier::keccak::BITS;

use crate::kernels::{PACKS, Run, embed_run, xor};
use crate::layer::{Layer, Sumcheck};
use crate::product::PACK_SUMS;
use crate::protocol::Claim;

/// The rounds the skip proves, and the packs of a group they bind.
pub const SKIP: usize = 4;
const GROUP: usize = 1 << SKIP;
/// The points of `{0, 1, infinity}^SKIP`, infinity as digit 2 and variable `k` the `k`-th digit, and those with a
/// digit at infinity.
const TERNARY: usize = 3usize.pow(SKIP as u32);
const MIXED: usize = TERNARY - GROUP;
/// A run's packs at every point of each group, group `h`'s point `t` at `TERNARY h + t`.
const SLOTS: usize = 2 * TERNARY;

/// A pack's slot: its group's, at its point of `{0, 1, infinity}^SKIP`.
const fn ternary(q: usize) -> usize {
    (q & 1) + 3 * (q >> 1 & 1) + 9 * (q >> 2 & 1) + 27 * (q >> 3 & 1) + TERNARY * (q >> SKIP & 1)
}

/// The slots of the mixed points of each group, each with the place value of its highest digit at infinity: the
/// points at `0` and `1` there, `2 place` and `place` below it, have values summing to its own. In order of that digit,
/// so a point's two come before it.
const MIXED_POINTS: [(usize, usize); 2 * MIXED] = {
    let mut out = [(0, 0); 2 * MIXED];
    let (mut i, mut place) = (0, 1);
    while place < TERNARY {
        let mut p = 0;
        while p < SLOTS {
            // The highest digit at infinity, or the digit at `place`.
            let mut high = TERNARY / 3;
            while high > place && p % TERNARY / high % 3 != 2 {
                high /= 3;
            }
            if high == place && p % TERNARY / place % 3 == 2 {
                out[i] = (p, place);
                i += 1;
            }
            p += 1;
        }
        place *= 3;
    }
    out
};

/// The runs `x + 1` and `x + 2` of a row of five, for each `x`.
const CHI_RUNS: [[usize; 2]; 5] = [[1, 2], [2, 3], [3, 4], [4, 0], [0, 1]];

/// The summand at every point of `{0, 1, infinity}^SKIP`, by its ternary digits, from the [`COEFFS`] `powers` of
/// `s`. `tasks` are the tasks' weights in `eq(point[SKIP + 1..])`, and `per_pack` the packs' parts of `U` from the
/// product pass.
pub(crate) fn sums(
    layer: &Layer,
    claim: &Claim,
    powers: &[F128],
    tasks: &[F128],
    per_pack: &[F128],
) -> [F128; TERNARY] {
    let at = AtS::new(powers);
    // Word `k` of each position's weight as a polynomial in `s`, at `words[BITS * k + j]`.
    let mut words = [0; 2 * BITS];
    for (j, &w) in claim.weights.iter().enumerate() {
        [words[j], words[BITS + j]] = at.poly(w).to_limbs();
    }
    let mixed = parallel::fold_reduce(
        layer.n_tasks(),
        || [F128Unreduced::ZERO; SLOTS],
        |sums, task| {
            let mut block = [[Wide8::ZERO; 2]; 2 * MIXED];
            block_sums(layer.task(task), &words, &mut block);
            for (&(p, _), &[p0, p1]) in MIXED_POINTS.iter().zip(&block) {
                sums[p] ^= at.eval([p0.sum(), p1.sum()]).mul_unreduced(tasks[task]);
            }
        },
        |mut a, b| {
            for (a, b) in a.iter_mut().zip(b) {
                *a ^= b;
            }
            a
        },
    );
    let mut sums = mixed.map(F128Unreduced::reduce);
    for (q, p) in per_pack.as_chunks::<PACK_SUMS>().0.iter().enumerate() {
        sums[ternary(q)] = poly_eval(p, powers[1]);
    }
    // The two groups of a block, the half being the variable after the skip's.
    let (low, high) = sums.split_at(TERNARY);
    std::array::from_fn(|t| low[t] + mul(claim.point[SKIP], low[t] + high[t]))
}

/// A block's sums at the mixed points of each group: `out[i]` holds `sum over positions j of
/// weights[j] * S[j + 1] * S[j + 2]` at the slot of `MIXED_POINTS[i]`, as its two partial products with the words
/// of the weights. Lane `i` of a slot holds the positions `z + i` of every run: a row of five runs, which `chi`
/// mixes, has eight consecutive positions' weights per run.
fn block_sums(block: &[u64], words: &[u64], out: &mut [[Wide8; 2]; 2 * MIXED]) {
    let mut extended = [[[0; 8]; SLOTS]; 5];
    for r in 0..5 {
        for z in (0..64).step_by(8) {
            let js = row_positions(r, z);
            for (extended, &j) in extended.iter_mut().zip(&js) {
                embed_run(block, j, extended.first_chunk_mut().expect("the packs"));
                // The packs moved to their slots, the last first: each lands at or past its own.
                for q in (0..PACKS).rev() {
                    extended[ternary(q)] = extended[q];
                }
            }
            let w: [[Run; 2]; 5] = js.map(|j| [j, BITS + j].map(|at| words[at..][..8].try_into().expect("a run")));
            for (&(p, place), out) in MIXED_POINTS.iter().zip(out.iter_mut()) {
                // Along a variable, the value at infinity is the sum of the two others.
                for slots in &mut extended {
                    slots[p] = xor(slots[p - 2 * place], slots[p - place]);
                }
                let mut sum = [Wide8::ZERO; 2];
                for (w, &[a, b]) in w.iter().zip(&CHI_RUNS) {
                    let product = clmul8_low(extended[a][p], extended[b][p]);
                    sum[0] += Wide8::mul(product, w[0]);
                    sum[1] += Wide8::mul(product, w[1]);
                }
                out[0] += sum[0];
                out[1] += sum[1];
            }
        }
    }
}

/// Send the skip's rounds from the summand at every point they read.
pub(crate) fn prove_rounds(ps: &mut ProverState, claim: &Claim, mut sums: [F128; TERNARY], sumcheck: &mut Sumcheck) {
    let mut len = TERNARY;
    for i in 0..SKIP {
        // The round's values at `0`, `1` and infinity, summed over the later variables' binary points.
        let later = eq_table(&claim.point[i + 1..SKIP]);
        let mut v = [F128::ZERO; 3];
        for (b, &eq) in later.iter().enumerate() {
            for (d, v) in v.iter_mut().enumerate() {
                *v += mul(eq, sums[d + 3 * ternary(b)]);
            }
        }
        let [zero, one, infinity] = v;
        let c = sumcheck.round(ps, zero, Some(one), infinity, claim.point[i]);
        // At `c`, a value along the variable is `v0 + c (v0 + v1) + (c^2 + c) v_infinity`.
        let c2 = mul(c, c + F128::ONE);
        len /= 3;
        for k in 0..len {
            let v = &sums[3 * k..][..3];
            sums[k] = v[0] + mul(c, v[0] + v[1]) + mul(c2, v[2]);
        }
    }
}

/// Coefficients a polynomial [`AtS::eval`] reads may have: a weight's 128 and a product's 47.
pub const COEFFS: usize = 192;

/// Field elements as binary polynomials at `s`.
struct AtS {
    /// An element's coordinates to the polynomial of degree below 128 whose value at `s` is the element.
    unit: BitFold,
    /// A polynomial's coefficients, [`COEFFS`] of them, to its value at `s`.
    powers: BitFold,
}

impl AtS {
    /// From the [`COEFFS`] powers of `s`.
    fn new(powers: &[F128]) -> Self {
        // Gauss-Jordan on the powers of `s` below 128, each tagged with its exponent: the reduced rows are the unit
        // vectors, tagged with their polynomials.
        let mut rows = [(0u128, 0u128); 128];
        for (i, row) in rows.iter_mut().enumerate() {
            *row = (u128::from(powers[i]), 1 << i);
        }
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
        let unit = rows.map(|row| F128::from(row.1));
        Self {
            unit: BitFold::new(&unit),
            powers: BitFold::new(powers),
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
    use primitives::field::powers;
    use primitives::test_rng::Rng;

    #[test]
    fn polynomials_take_their_values_at_s() {
        let mut rng = Rng::new(41);
        let s = rng.ext();
        let at = AtS::new(&powers(s, COEFFS));
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
