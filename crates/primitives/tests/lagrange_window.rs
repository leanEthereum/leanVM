//! The skip domain's Lagrange weights divide by ONE denominator rather than one per node, because every
//! barycentric denominator over an aligned window of the φ₈ table is the same field element:
//! φ₈ is F2-linear on its index, so `nodes[a] + nodes[b] = φ₈(a ^ b)` (a coset's offset cancels)
//! and `b ↦ a ^ b` only permutes the window. Should `PHI_8_BASIS` ever stop being the image of a
//! basis, the identity dies silently and every flock skip round is quietly wrong, so it is pinned
//! here against the per-node computation it replaced.
use primitives::PrimeCharacteristicRing;

use primitives::multilinear::{barycentric_sum, skip_lagrange_weights, window_denominator};
use primitives::test_util::Rng;
use primitives::{F192, PHI_8_TABLE_192 as PHI_8_TABLE};

/// The pre-change denominator: `∏_{k≠i} (nodes[i] + nodes[k])`, inverted, one per node.
fn per_node(nodes: &[F192], i: usize) -> F192 {
    let mut denominator = F192::ONE;
    for k in 0..nodes.len() {
        if k != i {
            denominator *= nodes[i] + nodes[k];
        }
    }
    denominator.invert_or_zero()
}

#[test]
fn one_denominator_per_window_size() {
    for log_size in 1..=8 {
        let size = 1usize << log_size;
        let shared = window_denominator(size);
        for base in (0..PHI_8_TABLE.len()).step_by(size) {
            let nodes = &PHI_8_TABLE[base..base + size];
            for i in 0..size {
                assert_eq!(per_node(nodes, i), shared, "size {size}, base {base}, node {i}");
            }
        }
    }
}

/// The linear-time weights and evaluation agree with the definition, `∏_{k≠i} (p + nodes[k]) /
/// (nodes[i] + nodes[k])` for node `i` at `p`, at random points and at every node, for every window
/// size, on the prefix and on a coset.
#[test]
fn barycentric_forms_match_the_definition() {
    let mut rng = Rng::new(0xBA7C_E417);
    for log_size in 0..=8 {
        let size = 1usize << log_size;
        for base in [0, size].into_iter().filter(|&base| base + size <= PHI_8_TABLE.len()) {
            let nodes = &PHI_8_TABLE[base..base + size];
            let denominators: Vec<F192> = (0..size).map(|i| per_node(nodes, i)).collect();
            let values = rng.ext_vec(size);
            let points: Vec<F192> = rng.ext_vec(4).into_iter().chain(nodes.iter().copied()).collect();
            for p in points {
                let weights: Vec<F192> = (0..size)
                    .map(|i| {
                        let others = nodes.iter().enumerate().filter(|&(k, _)| k != i);
                        others.fold(denominators[i], |acc, (_, &node)| acc * (p + node))
                    })
                    .collect();
                let want = weights
                    .iter()
                    .zip(&values)
                    .fold(F192::ZERO, |acc, (&w, &v)| acc + w * v);
                let got = barycentric_sum(nodes, &values, p, window_denominator(size));
                assert_eq!(got, want, "size {size}, base {base}");
                if base == 0 {
                    assert_eq!(skip_lagrange_weights(log_size, p), weights, "size {size}");
                }
            }
        }
    }
}
