//! The bus's grand products by GKR (§sec:gkr): the push, pull and count trees in one batched pass, reducing each
//! root to a claim on its leaves `Ṽ_0(ζ)`, all at one point `ζ`.
//!
//! Two binary levels are contracted at a time, a node being the product of its four grandchildren:
//! `V_i(x) = ∏_{a,b} V_{i-2}(a, b, x)`. A claim on `Ṽ_i(r)` is the sum over `x` of `eq(r, x)·∏_{a,b} Ṽ_{i-2}(a, b, x)`,
//! which a sumcheck reduces to the four values `Ṽ_{i-2}(a, b, χ)`, the trees' sumchecks batched by a combiner `λ`.
//! The prover sends them and two challenges `(u_0, u_1)` combine them into the next claim `Ṽ_{i-2}(u_0, u_1, χ)`. An
//! odd-depth tree starts with one binary layer.
//!
//! The layer below a claim is held as rows of four children, row `x` holding `V_{i-2}(·, ·, x)`, and only as the
//! prefix that covers its non-identity rows. An identity pair of rows adds only its eq weight to a round
//! polynomial's constant, which never travels, and folds to an identity row, so no pass reads past the prefix. The
//! bus's padding rows make long runs of identity leaves inside it, which the bus hands over as `Ones`: no pass
//! reads them either.

use std::ops::Range;

use crate::eq::SplitEq;
use crate::leaf::N_BUS_TREES as TREES;
use primitives::field::{Acc8, F128, F128x8};
use primitives::multilinear::interp;
use primitives::transcript::ProverState;

/// Runs of rows known to be the identity, sorted and disjoint.
pub(crate) type Ones = Vec<Range<usize>>;

/// The grind of a sumcheck round: its polynomial is `eq` times a product of four lines, degree five. In the last
/// layer the challenge is also a coordinate of `ζ`, which the table sumcheck's zerocheck reads, one more: six, as
/// many bits.
pub const ROUND_GRIND: u32 = fiat_shamir::grinding_bits(4 + 1);
const _: () = assert!(fiat_shamir::grinding_bits(4 + 1 + 1) == ROUND_GRIND);

/// The grind before a layer's `(u_0, u_1)`, or the binary layer's `u_0`, its `step` coordinates: the children's
/// multilinear has degree `step` in them. The last layer's are `ζ`'s first coordinates, which the zerocheck also
/// reads, `step` more (every table sumcheck spans at least two variables, the KECCAK table's floor).
pub fn y_grind(step: usize, last: bool) -> u32 {
    fiat_shamir::grinding_bits((step << usize::from(last)) as u128)
}

/// Prove the bus's grand products as one batched radix-four GKR: push, pull, then count. Push and pull have one
/// product by construction, so one root is sent for both, then the count's. `ones` are each tree's runs of leaves
/// known to be the identity. Returns the leaf claims it ends on: the shared point and every tree's value there.
///
/// Per layer: a grind and the combiner `λ`, the sumcheck rounds, the trees' children, then a grind and `(u_0, u_1)`.
pub(crate) fn prove_products(
    leaves: [Vec<F128>; TREES],
    ones: [Ones; TREES],
    ps: &mut ProverState,
) -> (Vec<F128>, [F128; TREES]) {
    let mu = crate::log2_ceil_usize(leaves[0].len());
    assert!(
        leaves.iter().all(|tree| !tree.is_empty() && tree.len() <= 1 << mu),
        "batched trees must be nonempty prefixes of the first tree's logical tree"
    );
    // Levels `0, 2, 4, …` of each tree, read as rows of four, up to the top, which has one node, or two when `μ` is
    // odd. A level's rows known to be the identity are the nodes two levels up made of identity leaves only.
    let mut trees = leaves.into_iter().zip(ones);
    let mut levels: [Vec<(Vec<F128>, Ones)>; TREES] = std::array::from_fn(|_| {
        let (leaves, ones) = trees.next().unwrap();
        let row_ones = |level: usize| coarsen(&ones, 4 << (2 * level));
        let mut levels = vec![(leaves, row_ones(0))];
        while levels.len() <= mu / 2 {
            let (values, ones) = levels.last().unwrap();
            let next = products(values, ones);
            levels.push((next, row_ones(levels.len())));
        }
        levels
    });
    let tops = levels.each_mut().map(|levels| {
        let (mut top, _) = levels.pop().unwrap();
        top.resize(1 << (mu % 2), F128::ONE);
        top
    });
    let roots: [F128; TREES] = tops.each_ref().map(|top| top.iter().copied().product());
    assert_eq!(roots[0], roots[1], "push and pull products must agree");
    ps.add_scalar(roots[0]);
    ps.add_scalar(roots[2]);
    let (mut point, mut values) = (Vec::new(), roots);

    if mu % 2 == 1 {
        // The root-most layer is binary, its two children the top level, with no sumcheck rounds.
        // Its `λ` is drawn as every layer's, though it batches nothing.
        ps.grind(fiat_shamir::grinding_bits(TREES as u128 - 1));
        let _: F128 = ps.sample();
        for top in &tops {
            ps.add_scalars(top);
        }
        ps.grind(y_grind(1, mu == 1));
        let u = ps.sample();
        values = tops.each_ref().map(|top| interp(top[0], top[1], u));
        point = vec![u];
    }
    while !levels[0].is_empty() {
        let layer = Layer::new(levels.each_mut().map(|levels| levels.pop().unwrap()));
        ps.grind(fiat_shamir::grinding_bits(TREES as u128 - 1));
        let lambda = ps.sample();
        let (chi, mut children) = layer.sumcheck(&point, lambda, ps);
        for children in &mut children {
            children.resize(4, F128::ONE);
            ps.add_scalars(children);
        }
        ps.grind(y_grind(2, levels[0].is_empty()));
        let (u0, u1) = (ps.sample(), ps.sample());
        values = children
            .each_ref()
            .map(|c| interp(interp(c[0], c[1], u0), interp(c[2], c[3], u0), u1));
        point = [vec![u0, u1], chi].concat();
    }
    (point, values)
}

/// The rows of a level `by` times coarser all of whose rows are in `ones`.
fn coarsen(ones: &[Range<usize>], by: usize) -> Ones {
    ones.iter()
        .map(|r| r.start.div_ceil(by)..r.end / by)
        .filter(|r| !r.is_empty())
        .collect()
}

/// Whether the `n` rows from `first` all lie in `ones`.
#[inline(always)]
fn known(ones: &[Range<usize>], first: usize, n: usize) -> bool {
    let i = ones.partition_point(|r| r.end < first + n);
    ones.get(i).is_some_and(|r| r.start <= first)
}

/// The level two above `values`: each row's product, the rows past the end and those in `ones` the identity.
fn products(values: &[F128], ones: &[Range<usize>]) -> Vec<F128> {
    let n = values.len().div_ceil(4);
    let eight = |k: usize| {
        if known(ones, 8 * k, 8) {
            return [F128::ONE; 8];
        }
        let v: [F128; 32] = padded(values, 32 * k);
        let child = |c: usize| lanes(|p| v[4 * p + c]);
        ((child(0) * child(1)) * (child(2) * child(3))).to_array()
    };
    let mut next = if n < 8 * crate::SERIAL_BELOW {
        (0..n.div_ceil(8)).map(eight).collect::<Vec<_>>()
    } else {
        parallel::map_collect(n.div_ceil(8), eight)
    }
    .into_flattened();
    next.truncate(n);
    next
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

/// A round's messages: per tree, `[q(0) + q(1), c2, c3, c4]` of its round polynomial `q`.
type Messages = [[F128; 4]; TREES];

fn add_messages(a: Messages, b: Messages) -> Messages {
    std::array::from_fn(|t| std::array::from_fn(|c| a[t][c] + b[t][c]))
}

/// The three trees' layer below the claim, during its sumcheck. A round binds the lowest row variable: a fold makes
/// row `i` `interp(row 2i, row 2i + 1, χ)`, child by child.
struct Layer {
    /// Each tree's held rows, four children a row.
    rows: [Vec<F128>; TREES],
    /// Each tree's rows known to be the identity.
    ones: [Ones; TREES],
    /// Each tree's buffer the next fold writes, reused round after round.
    spare: [Vec<F128>; TREES],
    /// The first round's challenge, which the rows are not yet folded by: the second round's fold applies both, so
    /// a layer is read three times and written once, at a quarter of its size, the second round's messages read
    /// through the pending fold.
    pending: Option<F128>,
}

/// Rows per group: the unit of every pass, eight pairs of rows, which the lanes take one pair each.
const GROUP: usize = 16;

impl Layer {
    fn new(levels: [(Vec<F128>, Ones); TREES]) -> Self {
        let [a, b, c] = levels;
        Self {
            rows: [a.0, b.0, c.0],
            ones: [a.1, b.1, c.1],
            spare: Default::default(),
            pending: None,
        }
    }

    /// The sumcheck rounds of the claim on `Ṽ_i(point)`, the trees batched by `λ`: their challenges `χ`, and each
    /// tree's children at the end, its rows folded to one.
    fn sumcheck(mut self, point: &[F128], lambda: F128, ps: &mut ProverState) -> (Vec<F128>, [Vec<F128>; TREES]) {
        let rounds = point.len();
        let mut chi = Vec::with_capacity(rounds);
        // Round `j` binds `point[j]`'s variable and weights each pair of rows by `eq(point[j + 1..], ·)`; the
        // verifier multiplies in the line `eq(point[j], X)`.
        let mut messages = match rounds {
            0 => [[F128::ZERO; 4]; TREES],
            _ => self.messages(&SplitEq::new(&point[1..])),
        };
        for j in 0..rounds {
            let mut coeffs: [F128; 4] = std::array::from_fn(|c| {
                // `Σ_t λ^t message_t`, by Horner.
                messages.iter().rev().fold(F128::ZERO, |acc, m| m[c] + lambda * acc)
            });
            // `c1 = (q(0) + q(1)) + c2 + c3 + c4`: the claim fixes `c0`, so only `c1..c4` travel.
            coeffs[0] = coeffs.iter().copied().sum();
            ps.add_scalars(&coeffs);
            ps.grind(ROUND_GRIND);
            let r = ps.sample();
            chi.push(r);
            let next = (j + 1 < rounds).then(|| SplitEq::new(&point[j + 2..]));
            messages = match (j, &next) {
                (0, Some(eq)) => {
                    self.pending = Some(r);
                    self.messages(eq)
                }
                _ => self.fold(r, next.as_ref()),
            };
        }
        (chi, self.rows)
    }

    /// The challenges the rows are folded by when read, as lanes: the pending one, then `r` if given.
    fn folds(&self, r: Option<F128>) -> Vec<F128x8> {
        self.pending.into_iter().chain(r).map(F128x8::splat).collect()
    }

    /// Each tree's round polynomial, the pairs of its rows (as folded by `pending`) weighted by `eq`.
    fn messages(&self, eq: &SplitEq) -> Messages {
        let folds = self.folds(None);
        let span = GROUP << folds.len();
        let groups = self.rows.each_ref().map(|rows| rows.len().div_ceil(4 * span));
        // The trees' groups end to end, tree `t`'s from `first[t]`, a task a chunk of them.
        let first: [usize; TREES] = std::array::from_fn(|t| groups[..t].iter().sum());
        let total = groups.iter().sum();
        let chunk = crate::chunk(total);
        parallel::map_reduce(
            total.div_ceil(chunk),
            || [[F128::ZERO; 4]; TREES],
            |task| {
                std::array::from_fn(|t| {
                    let mut acc = [Acc8::ZERO; 4];
                    let start = (task * chunk).max(first[t]) - first[t];
                    let end = ((task + 1) * chunk).min(first[t] + groups[t]).saturating_sub(first[t]);
                    for k in start..end {
                        if !known(&self.ones[t], span * k, span) {
                            let mut group = [F128::ONE; 4 * GROUP];
                            fold_group(&self.rows[t], k, &folds, &mut group);
                            add_message(&group, eq.lanes(k), &mut acc);
                        }
                    }
                    acc.map(Acc8::sum)
                })
            },
            add_messages,
        )
    }

    /// Bind the lowest row variable to `r`, after the pending challenge if any, writing the folded rows over the
    /// spare buffers, which then hold the rows they replace. With `next`, also the next round's messages, from the
    /// folded rows while they are at hand.
    fn fold(&mut self, r: F128, next: Option<&SplitEq>) -> Messages {
        let folds = self.folds(Some(r));
        self.pending = None;
        let span = GROUP << folds.len();
        for (rows, spare) in self.rows.iter().zip(&mut self.spare) {
            let len = 4 * GROUP * rows.len().div_ceil(4 * span);
            if spare.len() < len {
                *spare = crate::filled(len, F128::ONE);
            }
            spare.truncate(len);
        }
        let chunk = crate::chunk(self.spare.iter().map(|spare| spare.len() / (4 * GROUP)).sum());
        let (rows, ones) = (&self.rows, &self.ones);
        let messages = parallel::map_reduce_chunks_mut(
            self.spare.each_mut().map(|spare| spare.as_mut_slice()),
            [4 * GROUP * chunk; TREES],
            || [[F128::ZERO; 4]; TREES],
            |messages, task, outs| {
                for (t, out) in outs.into_iter().enumerate() {
                    let mut acc = [Acc8::ZERO; 4];
                    for (j, group) in out.as_chunks_mut().0.iter_mut().enumerate() {
                        let k = task * chunk + j;
                        if known(&ones[t], span * k, span) {
                            *group = [F128::ONE; 4 * GROUP];
                            continue;
                        }
                        fold_group(&rows[t], k, &folds, group);
                        if let Some(eq) = next {
                            add_message(group, eq.lanes(k), &mut acc);
                        }
                    }
                    for (m, acc) in messages[t].iter_mut().zip(acc) {
                        *m += acc.sum();
                    }
                }
            },
            add_messages,
        );
        std::mem::swap(&mut self.rows, &mut self.spare);
        for ones in &mut self.ones {
            *ones = coarsen(ones, 1 << folds.len());
        }
        messages
    }
}

/// Group `k` of `rows` folded by each of `folds` in turn, written over `out`: the [`GROUP`] rows folded from the
/// `GROUP << folds.len()` rows from `(GROUP << folds.len())·k`, the identity past the end of `rows`.
#[inline(always)]
fn fold_group(rows: &[F128], k: usize, folds: &[F128x8], out: &mut [F128; 4 * GROUP]) {
    match *folds {
        [] => *out = padded(rows, 4 * GROUP * k),
        [r] => fold_rows(rows, 8 * GROUP * k, r, out),
        [r0, r1] => {
            let mut half = [F128::ONE; 8 * GROUP];
            fold_rows(rows, 16 * GROUP * k, r0, &mut half);
            fold_rows(&half, 0, r1, out);
        }
        _ => unreachable!("a fold applies at most two challenges"),
    }
}

/// `out`'s row `i` is `interp(row 2i, row 2i + 1, r)` of the rows from `rows[start]`, child by child, two output rows
/// at a time.
#[inline(always)]
fn fold_rows(rows: &[F128], start: usize, r: F128x8, out: &mut [F128]) {
    for (i, out) in out.as_chunks_mut::<8>().0.iter_mut().enumerate() {
        let pairs: [F128; 16] = padded(rows, start + 16 * i);
        // Lane `l` takes child `l mod 4` of the pair `l / 4`.
        let lo = lanes(|l| pairs[8 * (l / 4) + l % 4]);
        let hi = lanes(|l| pairs[8 * (l / 4) + 4 + l % 4]);
        *out = (lo + r * (lo + hi)).to_array();
    }
}

/// Add a group's terms of `q(X) = eq·∏_c (a_c + s_c·X)` to `acc`, as `[q(0) + q(1), c2, c3, c4]`: lane `p` takes the
/// pair of rows `2p, 2p + 1`, its child `c` the line from `a_c` (the lower row's) to `a_c + s_c` (the upper's). The
/// weight scales child 0's line, and with it the product.
///
/// Karatsuba throughout: in characteristic two, `x_i·y_j + x_j·y_i = (x_i + x_j)·(y_i + y_j) + x_i·y_i + x_j·y_j`.
#[inline(always)]
fn add_message(group: &[F128; 4 * GROUP], eq: F128x8, acc: &mut [Acc8; 4]) {
    // `g[c]` is child `c` of each pair's lower row, `g[4 + c]` of its upper.
    let g: [F128x8; 8] = std::array::from_fn(|j| lanes(|p| group[8 * p + j]));
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpu::to_scalar;
    use primitives::multilinear::eq_table;

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
        for width in [2, 4, 8, 16, 1 << 13] {
            let below: Vec<F128> = (0..4 * width).map(|i| element(i, width)).collect();
            let point: Vec<F128> = (0..width.ilog2() - 1).map(|i| element(31 * i as usize, 5)).collect();
            let equality = eq_table(&point);
            let layer = Layer::new([0, 1, 2].map(|_| (below.clone(), Ones::new())));
            let message = layer.messages(&SplitEq::new(&point))[2];
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
            let (point, values) = prove_products(leaves.clone(), Default::default(), &mut ps);
            let stream = ps.into_proof().stream;
            assert_eq!(
                stream[..2],
                [product(&leaves[0]), product(&leaves[2])].map(|x| to_scalar(&x))
            );
            for lane in 0..3 {
                assert_eq!(values[lane], mle_eval_e(&leaves[lane], &point));
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
            let proved = prove_products(leaves, Default::default(), &mut sparse_ps);
            let (point, values) = &proved;
            for lane in 0..3 {
                assert_eq!(values[lane], mle_eval_e(&dense[lane], point));
            }
            let proof = sparse_ps.into_proof();
            assert_eq!(
                proof.stream[..2],
                [product(&dense[0]), product(&dense[2])].map(|x| to_scalar(&x))
            );
            let mut dense_ps = ProverState::from_label(b"sparse-radix-four-gkr-test");
            assert_eq!(prove_products(dense, Default::default(), &mut dense_ps), proved);
            assert_eq!(dense_ps.into_proof().stream, proof.stream);
        }
    }

    /// Runs of identity leaves passed as known prove as when they are read.
    #[test]
    fn known_identity_runs_prove_as_read() {
        for mu in [5, 8, 11] {
            let n = 1usize << mu;
            let runs = [n / 8 + 3..n / 2 - 5, n / 2 + 64.min(n / 4)..3 * n / 4];
            let mut leaves: [Vec<F128>; 3] = [0, 1, 2].map(|lane| {
                (0..n)
                    .map(|i| match runs.iter().any(|r| r.contains(&i)) {
                        true => F128::ONE,
                        false => F128::new((7 + i + lane * 1_009) as u64, (i * lane + 1) as u64),
                    })
                    .collect()
            });
            balance(&mut leaves);
            let prove = |ones: [Ones; 3]| {
                let mut ps = ProverState::from_label(b"known-identity-runs");
                (prove_products(leaves.clone(), ones, &mut ps), ps.into_proof().stream)
            };
            assert!(
                prove(Default::default()) == prove([0, 1, 2].map(|_| runs.to_vec())),
                "mu {mu}"
            );
        }
    }
}
