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
use primitives::field::{F128, F128Unreduced, clmul8_low};
use primitives::hash::positions::row_positions;
use primitives::transcript::ProverState;
use verifier::keccak::{BITS, PRODUCT_BITS};

use crate::kernels::{PACKS, Run, embed_run, eq_table, mul, poly_eval, xor};
use crate::layer::{Layer, Sumcheck};
use crate::protocol::Claim;

/// The rounds the skip proves, and the packs of a group they bind.
pub const SKIP: usize = 4;
const GROUP: usize = 1 << SKIP;
/// The points of `{0, 1, infinity}^SKIP`, infinity as digit 2 and variable `k` the `k`-th digit, and those with a
/// digit at infinity.
const TERNARY: usize = 3usize.pow(SKIP as u32);
const MIXED: usize = TERNARY - GROUP;
/// A run's extended packs: its packs, then the mixed points of each group.
const SLOTS: usize = PACKS + 2 * MIXED;

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

/// The slots each mixed point of each group sums, in slot order: those of the points at `0` and `1` along its lowest
/// digit at infinity.
const SOURCES: [[usize; 2]; 2 * MIXED] = {
    // A point's slot in its group: a pack's index, or `GROUP` plus a mixed point's.
    let mut slot = [0; TERNARY];
    let mut q = 0;
    while q < GROUP {
        slot[ternary(q)] = q;
        q += 1;
    }
    let mut i = 0;
    while i < MIXED {
        slot[MIXED_POINTS[i][0]] = GROUP + i;
        i += 1;
    }
    let mut out = [[0; 2]; 2 * MIXED];
    let mut p = 0;
    while p < 2 * MIXED {
        let (half, i) = (p / MIXED, p % MIXED);
        let mut k = 0;
        while k < 2 {
            let s = slot[MIXED_POINTS[i][1 + k]];
            out[p][k] = if s < GROUP {
                GROUP * half + s
            } else {
                PACKS + MIXED * half + s - GROUP
            };
            k += 1;
        }
        p += 1;
    }
    out
};

/// The runs `x + 1` and `x + 2` of a row of five, for each `x`.
const CHI_RUNS: [[usize; 2]; 5] = [[1, 2], [2, 3], [3, 4], [4, 0], [0, 1]];

/// The summand at every point of `{0, 1, infinity}^SKIP`, by its ternary digits, from the [`COEFFS`] `powers` of
/// `s`. `tasks` are the tasks' weights in `eq(point[SKIP + 1..])`, and `per_pack` the packs' parts of `U` from the
/// product pass.
pub(crate) fn sums(layer: &Layer, claim: &Claim, powers: &[F128], tasks: &[F128], per_pack: &[F128]) -> Vec<F128> {
    let at = AtS::new(powers);
    // Word `k` of each position's weight as a polynomial in `s`, at `words[BITS * k + j]`.
    let mut words = vec![0; 2 * BITS];
    for (j, &w) in claim.weights.iter().enumerate() {
        [words[j], words[BITS + j]] = at.poly(w).to_limbs();
    }
    let half = claim.point[SKIP];
    let mixed = parallel::fold_reduce(
        layer.n_tasks(),
        || [F128Unreduced::ZERO; TERNARY],
        |sums, task| {
            let mut block = [[Wide8::ZERO; 2]; 2 * MIXED];
            block_sums(layer.task(task), &words, &mut block);
            // The groups of a block alternate, the half being the first variable.
            let high = mul(half, tasks[task]);
            for (h, weight) in [tasks[task] + high, high].into_iter().enumerate() {
                for (i, &[t, ..]) in MIXED_POINTS.iter().enumerate() {
                    let [p0, p1] = block[MIXED * h + i];
                    sums[t] ^= at.eval([p0.sum(), p1.sum()]).mul_unreduced(weight);
                }
            }
        },
        |mut a, b| {
            for (a, b) in a.iter_mut().zip(b) {
                *a ^= b;
            }
            a
        },
    );
    let mut sums = vec![F128::ZERO; TERNARY];
    for (sum, mixed) in sums.iter_mut().zip(mixed) {
        *sum = mixed.reduce();
    }
    let mut at_s = [F128::ZERO; PACKS];
    for (at_s, p) in at_s.iter_mut().zip(per_pack.as_chunks::<PRODUCT_BITS>().0) {
        *at_s = poly_eval(p, powers[1]);
    }
    for q in 0..GROUP {
        sums[ternary(q)] = at_s[q] + mul(half, at_s[q] + at_s[GROUP + q]);
    }
    sums
}

/// A block's sums at the mixed points of each group: slot `MIXED * half + i` holds `sum over positions j of
/// weights[j] * S[j + 1] * S[j + 2]` at mixed point `i` of group `half`, as its two partial products with the words
/// of the weights. Lane `i` of a slot holds the positions `z + i` of every run: a row of five runs, which `chi`
/// mixes, has eight consecutive positions' weights per run.
fn block_sums(block: &[u64], words: &[u64], out: &mut [[Wide8; 2]; 2 * MIXED]) {
    let mut extended = [[[0; 8]; SLOTS]; 5];
    for r in 0..5 {
        for z in (0..64).step_by(8) {
            let js = row_positions(r, z);
            for (extended, &j) in extended.iter_mut().zip(&js) {
                embed_run(block, j, extended.first_chunk_mut().expect("the packs"));
                extend(extended);
            }
            let w: [[Run; 2]; 5] = js.map(|j| [j, BITS + j].map(|at| words[at..][..8].try_into().expect("a run")));
            for (p, out) in (PACKS..).zip(out.iter_mut()) {
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

/// A run's packs at the mixed points of each group, after its packs: along a variable, the value at infinity is the
/// sum of the two others.
fn extend(slots: &mut [Run; SLOTS]) {
    for (p, &[zero, one]) in (PACKS..).zip(&SOURCES) {
        slots[p] = xor(slots[zero], slots[one]);
    }
}

/// Send the skip's rounds from the summand at every point they read.
pub(crate) fn prove_rounds(ps: &mut ProverState, claim: &Claim, mut sums: Vec<F128>, sumcheck: &mut Sumcheck) {
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
        let len = sums.len() / 3;
        for k in 0..len {
            let v = &sums[3 * k..][..3];
            sums[k] = v[0] + mul(c, v[0] + v[1]) + mul(c2, v[2]);
        }
        sums.truncate(len);
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
