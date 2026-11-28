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
//! coordinate at infinity. With `e[x]` the packs at position `x` of a row of five, which `chi` mixes, and `w[x]` its
//! weight, a row's part is
//!
//! ```text
//!     sum over x of w[x] e[x + 1] e[x + 2]
//!         = e[2] (w[0] e[1] + w[1] e[3]) + e[4] (w[2] e[3] + w[3] e[0]) + e[0] (w[4] e[1])
//! ```
//!
//! whose six factors are linear in the packs, so they extend to the mixed points like them: a point takes three
//! products.

use primitives::field::{F128, F128Unreduced};
use primitives::multilinear::{eq_table, poly_eval};
use primitives::transcript::ProverState;
use verifier::keccak::{PACK, PRODUCT_BITS};

use crate::layer::{Layer, Sumcheck};
use crate::protocol::{Claim, instance_weights};
use crate::witness::BLOCK_WORDS;

/// The rounds the skip proves, and the packs of a group they bind.
pub const SKIP: usize = 4;
const GROUP: usize = 1 << SKIP;
/// The points of `{0, 1, infinity}^SKIP`, infinity as digit 2 and variable `k` the `k`-th digit.
const TERNARY: usize = 3usize.pow(SKIP as u32);

/// The point of `{0, 1, infinity}^SKIP` of a pack of a group.
const fn ternary(q: usize) -> usize {
    (q & 1) + 3 * (q >> 1 & 1) + 9 * (q >> 2 & 1) + 27 * (q >> 3 & 1)
}

/// The place value `3^k` of point `t`'s lowest digit at infinity, if it has one.
fn infinity_step(t: usize) -> Option<usize> {
    (0..SKIP).map(|k| 3usize.pow(k as u32)).find(|&step| t / step % 3 == 2)
}

/// Values at the points of `{0, 1}^SKIP`, by pack, at every point of `{0, 1, infinity}^SKIP`: along a variable, the
/// value at infinity is the sum of the two others.
fn extend(binary: &[F128; GROUP]) -> [F128; TERNARY] {
    let mut out = [F128::ZERO; TERNARY];
    for q in 0..GROUP {
        out[ternary(q)] = binary[q];
    }
    for t in 0..TERNARY {
        if let Some(step) = infinity_step(t) {
            out[t] = out[t - 2 * step] + out[t - step];
        }
    }
    out
}

/// The summand at every point of `{0, 1, infinity}^SKIP`, by its ternary digits. `per_pack` are the packs' parts of
/// `U` from the product pass.
pub(crate) fn sums(layer: &Layer, claim: &Claim, s: F128, per_pack: &[[F128; PRODUCT_BITS]]) -> Vec<F128> {
    // Every pack's embedding at `s`: the instances' weights summed over its set bits.
    let mu = instance_weights(s);
    let mut embed = vec![F128::ZERO; 1 << PACK];
    for bits in 1..embed.len() {
        embed[bits] = embed[bits & (bits - 1)] + mu[bits.trailing_zeros() as usize];
    }
    // Each task's weight, for each half: the groups of a block alternate.
    let eq = eq_table(&claim.point[SKIP..]);
    let groups = [0, 1].map(|half| layer.task_weights(&eq.iter().skip(half).step_by(2).copied().collect::<Vec<_>>()));
    let mut sums = parallel::fold_reduce(
        layer.n_tasks(),
        || vec![F128::ZERO; TERNARY],
        |sums, task| {
            for (half, groups) in groups.iter().enumerate() {
                let group = group_sums(layer.task(task), half, &claim.weights, &embed);
                for (sum, value) in sums.iter_mut().zip(group) {
                    *sum += groups[task] * value;
                }
            }
        },
        |mut a, b| {
            for (a, b) in a.iter_mut().zip(b) {
                *a += b;
            }
            a
        },
    );
    let half = claim.point[SKIP];
    for q in 0..GROUP {
        sums[ternary(q)] = (F128::ONE + half) * poly_eval(&per_pack[q], s) + half * poly_eval(&per_pack[GROUP + q], s);
    }
    sums
}

/// `sum over positions j of weights[j] * S[j + 1] * S[j + 2]` at every mixed point of group `half` of a block, zero
/// at the binary points. `embed` is each pack's embedding at `s`.
fn group_sums(block: &[u64], half: usize, weights: &[F128], embed: &[F128]) -> [F128; TERNARY] {
    let mut sums = [F128Unreduced::ZERO; TERNARY];
    for (y, z) in (0..5).flat_map(|y| (0..64).map(move |z| (y, z))) {
        // Position `x` of the row: lane `x + 5 y`, bit `z`.
        let j = |x: usize| 64 * (x + 5 * y) + z;
        let w = |x: usize| weights[j(x)];
        let e: [[F128; GROUP]; 5] = std::array::from_fn(|x| {
            let position = &block[j(x) * BLOCK_WORDS..][..BLOCK_WORDS];
            std::array::from_fn(|q| {
                let pack = GROUP * half + q;
                embed[(position[pack * PACK / 64] >> (pack * PACK % 64)) as u16 as usize]
            })
        });
        let factors = [
            (e[2], std::array::from_fn(|q| w(0) * e[1][q] + w(1) * e[3][q])),
            (e[4], std::array::from_fn(|q| w(2) * e[3][q] + w(3) * e[0][q])),
            (e[0], std::array::from_fn(|q| w(4) * e[1][q])),
        ];
        for (a, b) in &factors {
            let (a, b) = (extend(a), extend(b));
            for t in (0..TERNARY).filter(|&t| infinity_step(t).is_some()) {
                sums[t] ^= a[t].mul_unreduced(b[t]);
            }
        }
    }
    sums.map(F128Unreduced::reduce)
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
