//! The grand product via GKR (§sec:gkr): given leaves `v_0…v_{2^μ-1}`, prove the
//! root `P = ∏ v_k` of the product tree, reducing the root to one leaf evaluation
//! `Ṽ_0(ζ)`. Two binary levels are contracted at a time: a radix-four layer has
//! relation `V_i(x)=∏_{a,b∈{0,1}}V_{i-2}(a,b,x)`. Its normalized eq-trick
//! sumcheck has degree four. An odd-depth tree starts with one binary layer.
//! Leaves and every layer are `E`-valued (the bus fingerprints mix `K`-columns
//! into `E` upstream, [`crate::leaf`]).
//!
//! A tree's leaves are a prefix of its `2^μ` (every block's rows, padding rows included), the rest the identity, and
//! every level is held the same way: a prefix covering every non-identity value, rounded up to whole pairs of rows. An identity pair of rows adds only
//! its eq weight to a round polynomial's constant, which never travels, and folds to an identity row, so no
//! round reads or writes past the held prefix.

use crate::leaf::N_BUS_TREES as TREES;
use crate::transcript::ProverState;
use primitives::field::{Acc8, F128, F128x8};
use primitives::multilinear::{eq_table, interp};

/// Groups of eight pairs per parallel task.
const CHUNK: usize = 1 << 7;

/// The result of a batched grand-product proof: the leaf evaluations, all reduced to one shared point.
pub struct Products {
    pub point: Vec<F128>,
    pub values: [F128; TREES],
}

/// A sumcheck round's grind: its polynomial is `eq` times a product of four lines, degree five. In the bus's last
/// layer the challenge is also a coordinate of `ζ`, which the table sumcheck's zerocheck reads, one more: six, as
/// many bits.
pub const ROUND_GRIND: u32 = fiat_shamir::grinding_bits(4 + 1);
const _: () = assert!(fiat_shamir::grinding_bits(4 + 1 + 1) == ROUND_GRIND);

/// The grind before a layer's `y`, its `step` coordinates: the children's multilinear has degree `step` in them.
/// The last layer's are `ζ`'s first coordinates, which the bus's zerocheck also reads, `step` more (every table
/// sumcheck spans at least two variables, the KECCAK table's floor).
pub fn y_grind(step: usize, last: bool) -> u32 {
    fiat_shamir::grinding_bits((step << usize::from(last)) as u128)
}

fn add4(a: [F128; 4], b: [F128; 4]) -> [F128; 4] {
    std::array::from_fn(|i| a[i] + b[i])
}

/// Eight lanes, lane `p` being `value(p)`.
#[inline(always)]
fn lanes(value: impl Fn(usize) -> F128) -> F128x8 {
    F128x8::from_array(&std::array::from_fn(value))
}

/// `values[start..start + N]`, the identity past the end.
#[inline(always)]
fn padded<const N: usize>(values: &[F128], start: usize) -> [F128; N] {
    match values.get(start..start + N) {
        Some(run) => run.try_into().unwrap(),
        None => std::array::from_fn(|i| values.get(start + i).copied().unwrap_or(F128::ONE)),
    }
}

/// The level above `values`: `out[i] = ∏ values[4i..4i + 4]`, the values past the end being the identity.
fn next_level(values: &[F128]) -> Vec<F128> {
    let n = values.len().div_ceil(4);
    let mut next = parallel::map_collect(n.div_ceil(8), |k| {
        let v: [F128; 32] = padded(values, 32 * k);
        let child = |c: usize| lanes(|p| v[4 * p + c]);
        ((child(0) * child(1)) * (child(2) * child(3))).to_array()
    })
    .into_flattened();
    next.truncate(n);
    next
}

/// Eight pairs of rows, `g[j]` lane `p` being value `j` of pair `p`: `g[c]` child `c` of its lower row and
/// `g[4 + c]` of its upper.
type Group = [F128x8; 8];

/// Group `k` of a layer, the identity past its end.
#[inline(always)]
fn group(values: &[F128], k: usize) -> Group {
    let v: [F128; 64] = padded(values, 64 * k);
    std::array::from_fn(|j| lanes(|p| v[8 * p + j]))
}

/// Add eight pairs' terms of `q(X) = eq·∏_c (a_c + s_c·X)` to `acc`, as `[q(0) + q(1), c2, c3, c4]`. The weight
/// scales child 0's line, and with it every product. An identity pair adds nothing: its `q` is a constant.
///
/// Karatsuba throughout: in characteristic two, `x_i·y_j + x_j·y_i = (x_i + x_j)·(y_i + y_j) + x_i·y_i + x_j·y_j`.
#[inline(always)]
fn add_message(g: &Group, eq: F128x8, acc: &mut [Acc8; 4]) {
    // Children 0 and 1 make the quadratic `left`, children 2 and 3 `right`, by coefficient.
    let a0 = eq * g[0];
    let d0 = eq * (g[0] + g[4]);
    let left0 = a0 * g[1];
    let left2 = d0 * (g[1] + g[5]);
    let left1 = (a0 + d0) * g[5] + left0 + left2;
    let right0 = g[2] * g[3];
    let right2 = (g[2] + g[6]) * (g[3] + g[7]);
    let right1 = g[6] * g[7] + right0 + right2;
    let c0 = left0.mul_unreduced(right0);
    let c4 = left2.mul_unreduced(right2);
    let middle = left1.mul_unreduced(right1);
    let at_one = (left0 + left1 + left2).mul_unreduced(right0 + right1 + right2);
    let cross_even = (left0 + left2).mul_unreduced(right0 + right2);
    let cross_high = (left1 + left2).mul_unreduced(right1 + right2);
    acc[0] += c0 + at_one;
    acc[1] += cross_even + c0 + c4 + middle;
    acc[2] += cross_high + middle + c4;
    acc[3] += c4;
}

/// The round polynomial `q(X) = Σ_p eq[p]·∏_c V(c, 2p + X)` of a layer whose row `r` holds its four children at
/// `values[4r..4r + 4]`, as `[q(0) + q(1), c2, c3, c4]`. The pairs past `values` are identity pairs, which add
/// nothing.
fn round_message(values: &[F128], eq: &[F128]) -> [F128; 4] {
    let groups = values.len().div_ceil(64);
    parallel::map_reduce(
        groups.div_ceil(CHUNK),
        || [F128::ZERO; 4],
        |task| {
            let mut acc = [Acc8::ZERO; 4];
            for k in task * CHUNK..groups.min((task + 1) * CHUNK) {
                let eq = lanes(|p| eq.get(8 * k + p).copied().unwrap_or(F128::ZERO));
                add_message(&group(values, k), eq, &mut acc);
            }
            acc.map(Acc8::sum)
        },
        add4,
    )
}

/// Bind the lowest row variable to `r`: row `i` becomes `interp(row 2i, row 2i + 1, r)`, child by child. The
/// output is padded with identity rows to whole groups of eight values.
fn fold(values: &[F128], r: F128) -> Vec<F128> {
    let r = F128x8::splat(r);
    parallel::map_collect(values.len().div_ceil(16), |k| {
        // Rows `2k` and `2k + 1` of the output, from pairs `2k` and `2k + 1`.
        let v: [F128; 16] = padded(values, 16 * k);
        let lo = lanes(|i| v[8 * (i / 4) + i % 4]);
        let hi = lanes(|i| v[8 * (i / 4) + 4 + i % 4]);
        (lo + r * (lo + hi)).to_array()
    })
    .into_flattened()
}

/// Prove the bus's identity-padded grand products as one RLC-batched radix-four GKR: push, pull, then count. Push
/// and pull have one product by construction, so one root is sent for both, then the count's.
///
/// Per layer: a grind and the combiner `λ` (degree two in it), the sumcheck rounds (each its coefficients `c1..c4`,
/// then its grind and challenge), the trees' children, then a grind and `y`.
pub(crate) fn prove_products(leaves: [Vec<F128>; TREES], ps: &mut ProverState) -> Products {
    let mu = crate::log2_ceil_usize(leaves[0].len());
    assert!(
        leaves.iter().all(|lane| !lane.is_empty() && lane.len() <= 1 << mu),
        "batched trees must be nonempty prefixes of the first tree's logical tree"
    );
    // Levels `0, 2, 4, …` of each tree. The last has one node, or two when `μ` is odd.
    let mut levels: [Vec<Vec<F128>>; TREES] = leaves.map(|values| {
        let mut levels = vec![values];
        for _ in 0..mu / 2 {
            let next = next_level(levels.last().unwrap());
            levels.push(next);
        }
        levels
    });
    let tops = levels.each_mut().map(|levels| {
        let mut top = levels.pop().unwrap();
        top.resize(1 << (mu % 2), F128::ONE);
        top
    });
    let roots: [F128; TREES] = tops.each_ref().map(|top| top.iter().copied().product());
    assert_eq!(roots[0], roots[1], "push and pull products must agree");
    ps.add_scalar(roots[0]);
    ps.add_scalar(roots[2]);
    let mut point = Vec::new();
    let mut values = roots;

    let mut layer = mu;
    while layer > 0 {
        ps.grind(fiat_shamir::grinding_bits(TREES as u128 - 1));
        let lambda = ps.sample();
        if layer % 2 == 1 {
            // The root-most layer of an odd-depth tree is binary: its two children are the top level.
            for top in &tops {
                ps.add_scalars(top);
            }
            ps.grind(y_grind(1, layer == 1));
            let challenge = ps.sample();
            for (value, top) in values.iter_mut().zip(&tops) {
                *value = interp(top[0], top[1], challenge);
            }
            point = vec![challenge];
            layer -= 1;
            continue;
        }

        let mut trees = levels.each_mut().map(|levels| levels.pop().unwrap());
        let round_count = mu - layer;
        let mut round_point = Vec::with_capacity(round_count);
        for round in 0..round_count {
            // Round `j` weights its pairs by `eq(point[1 + j..], ·)`.
            let eq = eq_table(&point[1 + round..]);
            let messages = trees.each_ref().map(|tree| round_message(tree, &eq));
            // `Σ_t λ^t message_t`, by Horner.
            let mut coeffs: [F128; 4] = std::array::from_fn(|k| {
                messages
                    .iter()
                    .rev()
                    .fold(F128::ZERO, |acc, message| message[k] + lambda * acc)
            });
            // `q(0) + q(1) = c1 + c2 + c3 + c4`. The claim fixes `c0`, so only `c1..c4` travel.
            coeffs[0] = coeffs.iter().copied().sum();
            ps.add_scalars(&coeffs);
            ps.grind(ROUND_GRIND);
            let challenge = ps.sample();
            round_point.push(challenge);
            trees = trees.map(|tree| fold(&tree, challenge));
        }

        for tree in &mut trees {
            tree.resize(4, F128::ONE);
            ps.add_scalars(tree);
        }
        ps.grind(y_grind(2, layer == 2));
        let low_challenge = ps.sample();
        let high_challenge = ps.sample();
        for (value, tail) in values.iter_mut().zip(&trees) {
            *value = interp(
                interp(tail[0], tail[1], low_challenge),
                interp(tail[2], tail[3], low_challenge),
                high_challenge,
            );
        }
        point = vec![low_challenge, high_challenge];
        point.extend_from_slice(&round_point);
        layer -= 2;
    }

    Products { point, values }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mle_eval_e(table: &[F128], point: &[F128]) -> F128 {
        assert_eq!(table.len(), 1 << point.len());
        let mut folded = table.to_vec();
        for &challenge in point {
            let half = folded.len() / 2;
            for row in 0..half {
                folded[row] = interp(folded[2 * row], folded[2 * row + 1], challenge);
            }
            folded.truncate(half);
        }
        folded[0]
    }

    fn element(i: usize, salt: usize) -> F128 {
        F128::new((17 * i + salt + 1) as u64, (i * i + 3) as u64)
    }

    #[test]
    fn quartic_round_message_matches_direct_evaluation() {
        for width in [2, 4, 8, 16, 1 << 11] {
            let below: Vec<F128> = (0..4 * width).map(|i| element(i, width)).collect();
            let point: Vec<F128> = (0..width.ilog2() - 1).map(|i| element(31 * i as usize, 5)).collect();
            let equality = eq_table(&point);
            let message = round_message(&below, &equality);
            let direct = |x: F128| {
                (0..width / 2)
                    .map(|row| {
                        let values =
                            [0, 1, 2, 3].map(|child| interp(below[8 * row + child], below[8 * row + 4 + child], x));
                        equality[row] * values[0] * values[1] * values[2] * values[3]
                    })
                    .sum::<F128>()
            };
            let [sum, c2, c3, c4] = message;
            let coeffs = [direct(F128::ZERO), sum + c2 + c3 + c4, c2, c3, c4];
            for x in [F128::ZERO, F128::ONE, F128::Y, F128::Y.square(), F128::Y + F128::ONE] {
                assert_eq!(primitives::multilinear::poly_eval(&coeffs, x), direct(x));
            }
        }
    }

    fn product(lane: &[F128]) -> F128 {
        lane.iter().copied().product()
    }

    /// Rescale lane 1's last leaf so its product matches lane 0's, as the bus's two sides do.
    fn balance(leaves: &mut [Vec<F128>; 3]) {
        let last = leaves[1].len() - 1;
        leaves[1][last] = F128::ONE;
        leaves[1][last] = product(&leaves[0]) * product(&leaves[1]).inv();
    }

    #[test]
    fn radix_four_claims_are_true_at_even_and_odd_depths() {
        for mu in 0..=10 {
            let mut leaves: [Vec<F128>; 3] = [0, 1, 2].map(|lane| {
                (0..1usize << mu)
                    .map(|row| F128::new((1 + row + lane * 100_003) as u64, (row + lane) as u64))
                    .collect()
            });
            balance(&mut leaves);
            let mut ps = ProverState::from_label(b"radix-four-gkr-test");
            let proved = prove_products(leaves.clone(), &mut ps);
            let stream = ps.into_proof().stream;
            assert_eq!(stream[..2], [product(&leaves[0]), product(&leaves[2])]);
            for lane in 0..3 {
                assert_eq!(proved.values[lane], mle_eval_e(&leaves[lane], &proved.point));
            }
        }
    }

    #[test]
    fn identity_suffix_matches_dense_padding() {
        for mu in 3..=10 {
            let lengths = [(1usize << mu) - 3, (1usize << (mu - 1)) + 1, (1usize << (mu - 2)) + 3];
            let mut leaves: [Vec<F128>; 3] = std::array::from_fn(|lane| {
                (0..lengths[lane])
                    .map(|row| F128::new((3 + row + lane * 10_007) as u64, (row + lane) as u64))
                    .collect()
            });
            balance(&mut leaves);
            let dense = leaves.each_ref().map(|lane| {
                let mut padded = lane.clone();
                padded.resize(1 << mu, F128::ONE);
                padded
            });
            let mut sparse_ps = ProverState::from_label(b"sparse-radix-four-gkr-test");
            let proved = prove_products(leaves, &mut sparse_ps);
            for lane in 0..3 {
                assert_eq!(proved.values[lane], mle_eval_e(&dense[lane], &proved.point));
            }
            let proof = sparse_ps.into_proof();
            assert_eq!(proof.stream[..2], [product(&dense[0]), product(&dense[2])]);
            let mut dense_ps = ProverState::from_label(b"sparse-radix-four-gkr-test");
            let dense_proved = prove_products(dense, &mut dense_ps);
            assert_eq!(dense_proved.point, proved.point);
            assert_eq!(dense_proved.values, proved.values);
            assert_eq!(dense_ps.into_proof().stream, proof.stream);
        }
    }
}
