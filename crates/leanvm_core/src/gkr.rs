//! The grand product via GKR (§sec:gkr).
//!
//! Given leaves `v_0, ..., v_{2^mu - 1}`, the prover shows the root `P = prod_k v_k` of their product tree.
//! The proof reduces that root to one evaluation of the leaves' multilinear extension.
//!
//! Each layer contracts two binary levels into one radix-four step:
//!
//! ```text
//!     V_{i+2}(x) = prod_{a, b in {0, 1}} V_i(a, b, x)
//! ```
//!
//! Its sumcheck has degree four, and a tree of odd depth starts with one binary layer.
//!
//! The leaves and every level are `E`-valued: the bus fingerprints mix `K` columns into `E` upstream.

mod lanes;
mod layer;

use self::lanes::{Lane, Lanes};
use self::layer::{EQ_LOW_VARS, Grid, Layer};
use crate::PAR_THRESHOLD;
use fiat_shamir::arith::Verifier;
use fiat_shamir::transcript::{Challenger, ProverState, TranscriptError, Transmitter};
use primitives::field::{F192, mul2};
use primitives::multilinear::{SplitEq, interp};
use std::mem::MaybeUninit;
use thiserror::Error;

/// Why the bus's grand-product GKR rejects.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum GkrError {
    /// The proof stream is malformed.
    #[error(transparent)]
    Transcript(#[from] TranscriptError),
    /// A layer's sumcheck does not end at the product of the next layer's claims.
    #[error("the GKR layer {layer} does not reduce to the next")]
    LayerMismatch { layer: usize },
}

/// The result of a batched grand-product proof: the two trees' leaf evaluations, at one shared point.
pub struct Products<E = F192> {
    pub point: Vec<E>,
    pub values: [E; 2],
}

/// The next radix-four level: entry `k` is the product of `current[4k..4k + 4]`, ones past the end.
///
/// The vector has room for whole rows of four, the shape a layer pads a level to, so that padding never copies it.
pub(crate) fn next_level(current: &[F192]) -> Vec<F192> {
    /// Rows per parallel task.
    const CHUNK: usize = 256;

    let rows = current.len().div_ceil(4);
    let mut next = Vec::with_capacity(rows.next_multiple_of(4));

    // Whole groups of rows go through the lanes, row `l` of a group in lane `l`.
    let (groups, tail) = next.spare_capacity_mut()[..rows].split_at_mut(current.len() / 4 / Lane::WIDTH * Lane::WIDTH);
    let fill = |first_row: usize, out: &mut [MaybeUninit<F192>]| {
        for (g, out) in out.as_chunks_mut::<{ Lane::WIDTH }>().0.iter_mut().enumerate() {
            let [a, b, c, d] = Lane::gather(&current[4 * (first_row + Lane::WIDTH * g)..], 4);
            Lanes::store((a * b) * (c * d), out);
        }
    };
    if groups.len() >= PAR_THRESHOLD {
        parallel::chunks_mut(groups, CHUNK, |task, out| fill(CHUNK * task, out));
    } else {
        fill(0, groups);
    }

    // The rows past the last whole group, the last one possibly ragged.
    let first_tail = rows - tail.len();
    for (i, slot) in tail.iter_mut().enumerate() {
        slot.write(padded_product(current, first_tail + i));
    }

    // SAFETY: the groups and the tail together cover the first `rows` slots.
    unsafe { next.set_len(rows) };
    next
}

/// Entry `row` of the next level: the product of `current[4 * row..]`'s first four, ones past its end.
pub(crate) fn padded_product(current: &[F192], row: usize) -> F192 {
    let child = |c: usize| current.get(4 * row + c).copied().unwrap_or(F192::ONE);
    let [left, right] = mul2([child(0), child(2)], [child(1), child(3)]);
    left * right
}

/// The levels a radix-four GKR reads: every second level of a product tree, the leaves first.
struct Tree {
    levels: Vec<Vec<F192>>,
}

impl Tree {
    /// The tree of depth `mu` over `leaves`, whose first product level `first` the caller built alongside them.
    fn new(leaves: Vec<F192>, first: Vec<F192>, mu: usize) -> Self {
        assert!(!leaves.is_empty() && leaves.len() <= 1 << mu);
        assert_eq!(
            first.len(),
            leaves.len().div_ceil(4),
            "the first level is the leaves' products"
        );

        // Level `2i` is entry `i`, up to the root or, for an odd depth, the root's two children.
        let mut levels = vec![leaves];
        if mu >= 2 {
            levels.push(first);
        }
        while 2 * levels.len() <= mu {
            let next = next_level(levels.last().expect("the leaves"));
            levels.push(next);
        }
        Self { levels }
    }

    /// The top level's two entries, the second one when it is implicit.
    fn children_of_root(top: &[F192]) -> [F192; 2] {
        match *top {
            [left, right] => [left, right],
            [left] => [left, F192::ONE],
            _ => unreachable!("the root's children have at most two explicit nodes"),
        }
    }

    fn root(&self, mu: usize) -> F192 {
        let top = self.levels.last().expect("the leaves");
        if mu.is_multiple_of(2) {
            top[0]
        } else {
            let [left, right] = Self::children_of_root(top);
            left * right
        }
    }
}

/// One layer of each tree, proven as one sumcheck under a batching challenge.
struct LayerPair {
    layers: [Layer; 2],
    lambda: F192,
}

impl LayerPair {
    /// Sends one round's two messages as their combination by `lambda`, and returns the round's challenge.
    fn send(&self, messages: [[F192; 4]; 2], ps: &mut ProverState) -> F192 {
        let [first, second] = messages;
        ps.add_scalars(&std::array::from_fn::<_, 4, _>(|k| first[k] + self.lambda * second[k]));
        ps.sample()
    }

    /// Reduces the claims on the level two above at `point` to claims on this level.
    ///
    /// Returns the new point and the two trees' values there.
    ///
    /// Round `j` weighs its rows by `eq(point[j + 1..], .)`, and the verifier restores `eq(point[j], X)`.
    fn prove(mut self, point: &[F192], ps: &mut ProverState) -> (Vec<F192>, [F192; 2]) {
        let rounds = point.len();
        let eq = |from: usize| SplitEq::with_low_vars(&point[from..], EQ_LOW_VARS);
        let mut challenges = Vec::with_capacity(rounds);

        // Two rounds per pass over the layer: rounds `j` and `j + 1` read one polynomial of their two variables.
        let mut grids = (rounds >= 2).then(|| self.layers.each_ref().map(|layer| layer.grid(&eq(2))));
        while let Some(grid) = grids {
            let j = challenges.len();
            let r0 = self.send(grid.each_ref().map(|g| g.first_round(point[j + 1])), ps);
            let r1 = self.send(grid.each_ref().map(|g| g.second_round(r0)), ps);
            challenges.extend([r0, r1]);

            // The fold reads the layer once more and sums the next two rounds' polynomial, if any.
            let next = (j + 4 <= rounds).then(|| eq(j + 4));
            let [first, second] = self.layers.each_mut().map(|layer| layer.fold([r0, r1], next.as_ref()));
            grids = first.zip(second).map(<[Grid; 2]>::from);
        }

        // An odd number of rounds leaves one, over two rows.
        if challenges.len() < rounds {
            let r = self.send(self.layers.each_ref().map(Layer::last_round), ps);
            challenges.push(r);
            for layer in &mut self.layers {
                layer.fold_last(r);
            }
        }

        // The one row left: its four children are the claims on this level.
        let children = self.layers.each_ref().map(Layer::children);
        for row in &children {
            ps.add_scalars(row);
        }
        let (low, high) = (ps.sample(), ps.sample());
        let values = children.map(|[a, b, c, d]| interp(interp(a, b, low), interp(c, d, low), high));
        let point = [low, high].into_iter().chain(challenges).collect();
        (point, values)
    }
}

/// Prove two identity-padded grand products as one radix-four GKR batched by a random combination, over the
/// depth of the taller tree.
///
/// The two trees share a product by construction, as the bus's two sides do.
/// One root is sent for both, so no verifier can be handed an unbalanced pair to check.
///
/// Each tree comes as its leaves and their first product level, from the next-level builder.
pub fn prove_products(trees: [(Vec<F192>, Vec<F192>); 2], ps: &mut ProverState) -> Products {
    let mu = trees
        .iter()
        .map(|(leaves, _)| crate::log2_ceil_usize(leaves.len()))
        .max()
        .expect("two trees");
    let mut trees = trees.map(|(leaves, first)| Tree::new(leaves, first, mu));
    let roots = trees.each_ref().map(|tree| tree.root(mu));
    assert_eq!(roots[0], roots[1], "the bus needs the two products to agree");
    ps.add_scalar(roots[0]);
    let mut lambda = ps.sample();
    let mut point = Vec::new();
    let mut values = roots;

    // The top level is the root itself, or for an odd depth the root's two children.
    let tops = trees.each_mut().map(|tree| tree.levels.pop().expect("the leaves"));
    if !mu.is_multiple_of(2) {
        let children = tops.map(|top| Tree::children_of_root(&top));
        for pair in &children {
            ps.add_scalars(pair);
        }
        let r = ps.sample();
        values = children.map(|[left, right]| interp(left, right, r));
        lambda = ps.sample();
        point = vec![r];
    }

    while let [Some(first), Some(second)] = trees.each_mut().map(|tree| tree.levels.pop()) {
        let pair = LayerPair {
            layers: [Layer::new(first), Layer::new(second)],
            lambda,
        };
        (point, values) = pair.prove(&point, ps);
        lambda = ps.sample();
    }

    Products { point, values }
}

/// Verify the batched radix-four proof of two trees of depth `mu`.
///
/// # Errors
///
/// Returns the first layer whose sumcheck does not end at the next layer's claims, or a malformed stream.
pub fn verify_products<V: Verifier>(v: &mut V, mu: usize) -> Result<Products<V::E>, GkrError> {
    // One root for both balancing trees, so their equality is structural.
    // There is no unbalanced pair a prover could state, and nothing for the caller to check.
    let root = v.next_scalar()?;
    let mut lambda = v.sample();
    let mut point = Vec::new();
    let mut values = [root; 2];

    let mut layer = mu;
    while layer > 0 {
        let mut claim = v.poly_eval(&values, lambda);

        // The binary layer of an odd depth: two children per tree, no sumcheck.
        if layer % 2 == 1 {
            let mut children = [[root; 2]; 2];
            for value in children.iter_mut().flatten() {
                *value = v.next_scalar()?;
            }
            let products = children.map(|[left, right]| v.mul(left, right));
            let expected = v.poly_eval(&products, lambda);
            v.ensure_eq(claim, expected, || GkrError::LayerMismatch { layer })?;
            let r = v.sample();
            for (value, [left, right]) in values.iter_mut().zip(children) {
                *value = v.interp(left, right, r);
            }
            lambda = v.sample();
            point = vec![r];
            layer -= 1;
            continue;
        }

        // A radix-four layer: one quartic per variable of the level above.
        let mut challenges = Vec::with_capacity(point.len());
        for &eq_point in &point {
            let message = v.next_round_poly(5, claim, Some(eq_point))?;
            let r = v.sample();
            challenges.push(r);
            claim = v.poly_eval(&message, r);
        }
        let mut children = [[root; 4]; 2];
        for value in children.iter_mut().flatten() {
            *value = v.next_scalar()?;
        }
        let products = children.map(|row| v.product(&row));
        let expected = v.poly_eval(&products, lambda);
        v.ensure_eq(claim, expected, || GkrError::LayerMismatch { layer })?;
        let (low, high) = (v.sample(), v.sample());
        for (value, [a, b, c, d]) in values.iter_mut().zip(children) {
            let (left, right) = (v.interp(a, b, low), v.interp(c, d, low));
            *value = v.interp(left, right, high);
        }
        lambda = v.sample();
        point = [low, high].into_iter().chain(challenges).collect();
        layer -= 2;
    }

    Ok(Products { point, values })
}

#[cfg(test)]
mod tests {
    use super::*;
    use fiat_shamir::transcript::VerifierState;

    /// The multilinear extension of `table` at `point`, folding the lowest variable first.
    fn mle(table: &[F192], point: &[F192]) -> F192 {
        assert_eq!(table.len(), 1 << point.len());
        let mut folded = table.to_vec();
        for &r in point {
            folded = folded
                .as_chunks::<2>()
                .0
                .iter()
                .map(|&[low, high]| interp(low, high, r))
                .collect();
        }
        folded[0]
    }

    /// Proves the two trees, checks each leaf claim against its dense extension, and verifies the proof.
    fn roundtrip(label: &[u8], leaves: &[Vec<F192>; 2], mu: usize) -> Vec<F192> {
        let mut ps = ProverState::from_label(label);
        let proved = prove_products(leaves.each_ref().map(|l| (l.clone(), next_level(l))), &mut ps);
        for (tree, leaves) in leaves.iter().enumerate() {
            let mut dense = leaves.clone();
            dense.resize(1 << mu, F192::ONE);
            assert_eq!(proved.values[tree], mle(&dense, &proved.point), "mu={mu}");
        }

        let proof = ps.into_proof();
        let mut vs = VerifierState::from_label(label, &proof);
        let verified = verify_products(&mut vs, mu).expect("GKR verifies");
        assert_eq!(verified.point, proved.point);
        assert_eq!(verified.values, proved.values);
        vs.finish().expect("proof stream is consumed");
        proof.stream
    }

    #[test]
    fn radix_four_roundtrip_at_even_and_odd_depths() {
        // Invariant: every depth, even or odd, proves and verifies to the leaves' extension.
        //
        // Fixture state: the second tree is the first reversed, so the two share their product.
        for mu in 0..=12 {
            let first: Vec<F192> = (0..1usize << mu)
                .map(|row| F192::new((1 + row) as u64, row as u64, 0))
                .collect();
            let reversed = first.iter().rev().copied().collect();
            roundtrip(b"radix-four-gkr-test", &[first, reversed], mu);
        }
    }

    #[test]
    fn implicit_identity_suffix_matches_dense_padding() {
        // Invariant: leaving the identity padding implicit changes nothing in the proof.
        //
        // Fixture state: two ragged trees, whose dense twins pad them with ones to 2^mu.
        //
        //     sparse:  [v_0, ..., v_{n-1}]
        //     dense:   [v_0, ..., v_{n-1}, 1, ..., 1]
        //     -> the same proof stream, word for word
        for mu in 3..=12 {
            let lengths = [(1usize << mu) - 3, (1usize << (mu - 1)) + 1];
            let mut leaves: [Vec<F192>; 2] = std::array::from_fn(|tree| {
                (0..lengths[tree])
                    .map(|row| F192::new((3 + row + tree * 10_007) as u64, row as u64, tree as u64))
                    .collect()
            });

            // The second tree's last leaf makes up the difference, so the two share their product.
            let product = |leaves: &[F192]| leaves.iter().fold(F192::ONE, |p, &v| p * v);
            let last = leaves[1].len() - 1;
            leaves[1][last] = product(&leaves[0]) * product(&leaves[1][..last]).inv();

            let dense = leaves.each_ref().map(|tree| {
                let mut padded = tree.clone();
                padded.resize(1 << mu, F192::ONE);
                padded
            });
            let label = b"sparse-radix-four-gkr-test";
            assert_eq!(roundtrip(label, &leaves, mu), roundtrip(label, &dense, mu), "mu={mu}");
        }
    }

    #[test]
    fn next_level_is_the_padded_products() {
        // Invariant: the lanes' products are the four-tuples' products, ones past the end.
        //
        // Fixture state: lengths around the lane width and across the parallel threshold.
        for len in [1, 3, 4, 5, 15, 16, 17, 63, 64, 65, 4 * PAR_THRESHOLD * 4 + 7] {
            let current: Vec<F192> = (0..len).map(|i| F192::new(i as u64 + 2, 3 * i as u64, 1)).collect();
            let want: Vec<F192> = (0..len.div_ceil(4)).map(|row| padded_product(&current, row)).collect();
            assert_eq!(next_level(&current), want, "len={len}");
        }
    }
}
