//! The grand product via GKR (§sec:gkr): given leaves `v_0…v_{2^μ-1}`, prove the
//! root `P = ∏ v_k` of the product tree, reducing the root to one leaf evaluation
//! `Ṽ_0(ζ)`. Two binary levels are contracted at a time: a radix-four layer has
//! relation `V_i(x)=∏_{a,b∈{0,1}}V_{i-2}(a,b,x)`. Its normalized eq-trick
//! sumcheck has degree four. An odd-depth tree starts with one binary layer.
//! Leaves and every layer are `E`-valued (the bus fingerprints mix `K`-columns
//! into `E` upstream, [`crate::leaf`]).

use crate::leaf::N_BUS_TREES as TREES;
use crate::transcript::ProverState;
use primitives::field::F128;
use primitives::multilinear::{eq_table, interp};

/// Rows per parallel task.
const CHUNK: usize = 1 << 10;

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

fn add5(a: [F128; 5], b: [F128; 5]) -> [F128; 5] {
    std::array::from_fn(|i| a[i] + b[i])
}

/// The level above `values`: `out[i] = ∏ values[4i..4i + 4]`.
fn next_level(values: &[F128]) -> Vec<F128> {
    let mut next = vec![F128::ZERO; values.len() / 4];
    parallel::chunks_mut(&mut next, CHUNK, |task, out| {
        let src = values[4 * task * CHUNK..].as_chunks::<4>().0;
        for (slot, four) in out.iter_mut().zip(src) {
            *slot = four.iter().copied().product();
        }
    });
    next
}

/// The coefficients of `∏_c (a_c + s_c·X)` for four lines `[a_c, s_c]`.
fn product_of_lines(lines: [[F128; 2]; 4]) -> [F128; 5] {
    let quadratic = |[a, s]: [F128; 2], [b, t]: [F128; 2]| [a * b, a * t + s * b, s * t];
    let (p, q) = (quadratic(lines[0], lines[1]), quadratic(lines[2], lines[3]));
    let mut out = [F128::ZERO; 5];
    for i in 0..3 {
        for j in 0..3 {
            out[i + j] += p[i] * q[j];
        }
    }
    out
}

/// The round polynomial `q(X) = Σ_p eq[p]·∏_c V(c, 2p + X)` of a layer whose row `r` holds its four children at
/// `values[4r..4r + 4]`, as its five coefficients, constant first.
fn round_message(values: &[F128], eq: &[F128]) -> [F128; 5] {
    let pairs = values.len() / 8;
    debug_assert_eq!(eq.len(), pairs);
    let pair = |p: usize| {
        let (lo, hi) = (&values[8 * p..8 * p + 4], &values[8 * p + 4..8 * p + 8]);
        let mut lines: [[F128; 2]; 4] = std::array::from_fn(|c| [lo[c], lo[c] + hi[c]]);
        lines[0] = lines[0].map(|v| eq[p] * v);
        product_of_lines(lines)
    };
    parallel::map_reduce(
        pairs.div_ceil(CHUNK),
        || [F128::ZERO; 5],
        |task| {
            (task * CHUNK..pairs.min((task + 1) * CHUNK))
                .map(pair)
                .fold([F128::ZERO; 5], add5)
        },
        add5,
    )
}

/// Bind the lowest row variable to `r`: row `i` becomes `interp(row 2i, row 2i + 1, r)`, child by child.
fn fold(values: &[F128], r: F128) -> Vec<F128> {
    let mut next = vec![F128::ZERO; values.len() / 2];
    parallel::chunks_mut(&mut next, 4 * CHUNK, |task, out| {
        let src = values[8 * task * CHUNK..].as_chunks::<8>().0;
        for (row, pair) in out.as_chunks_mut::<4>().0.iter_mut().zip(src) {
            for c in 0..4 {
                row[c] = interp(pair[c], pair[4 + c], r);
            }
        }
    });
    next
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
    // Levels `0, 2, 4, …` of each tree, its leaves padded with the identity to `2^μ`. The last has one node, or
    // two when `μ` is odd.
    let mut levels: [Vec<Vec<F128>>; TREES] = leaves.map(|mut values| {
        values.resize(1 << mu, F128::ONE);
        let mut levels = vec![values];
        while levels.last().unwrap().len() >= 4 {
            let next = next_level(levels.last().unwrap());
            levels.push(next);
        }
        levels
    });
    let tops = levels.each_mut().map(|levels| levels.pop().unwrap());
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
            let coeffs: [F128; 5] = std::array::from_fn(|k| {
                messages
                    .iter()
                    .rev()
                    .fold(F128::ZERO, |acc, message| message[k] + lambda * acc)
            });
            // The claim fixes `c0`, so only `c1..c4` travel.
            ps.add_scalars(&coeffs[1..]);
            ps.grind(ROUND_GRIND);
            let challenge = ps.sample();
            round_point.push(challenge);
            trees = trees.map(|tree| fold(&tree, challenge));
        }

        for tree in &trees {
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
            for x in [F128::ZERO, F128::ONE, F128::Y, F128::Y.square(), F128::Y + F128::ONE] {
                assert_eq!(primitives::multilinear::poly_eval(&message, x), direct(x));
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
