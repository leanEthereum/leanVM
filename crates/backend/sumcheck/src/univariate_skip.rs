//! Primitives for a univariate-skip round of a batched sumcheck
//! (Gruen, eprint 2024/108 §5-6).
//!
//! Domain convention: the base-window node for cube point `x ∈ {0,1}^k`
//! (big-endian bit order, matching `eval_eq` indexing) is the small integer
//! `x` itself: `node_x = F::from_usize(x)`. Extended targets continue at
//! `2^k, 2^k + 1, …` ascending. This integer window keeps all skip-kernel
//! evaluation points small (cheap base-field multiplications) and makes the
//! python-verifier / zkDSL mirrors trivial (`bits(i) ↔ node i`), at no cost
//! compared to a multiplicative subgroup: the skipped sum is non-zero here,
//! so no "free zero" evaluations exist either way.

use field::*;
use poly::{PF, eval_eq, lagrange_basis_evals};
use zk_alloc::ArenaVec;

/// The `2^k` base-window nodes, indexed by cube point `x ∈ 0..2^k`.
pub fn skip_domain_points<F: Field>(k: usize) -> Vec<F> {
    (0..1usize << k).map(F::from_usize).collect()
}

/// All evaluation nodes of the skip-round polynomial: the `2^k` window nodes
/// followed by the extended targets, `(2^k − 1)·air_degree + 1` nodes total
/// (enough to determine a polynomial of degree `(2^k − 1)·air_degree`).
pub fn skip_all_nodes<F: Field>(k: usize, air_degree: usize) -> Vec<F> {
    let n_nodes = ((1usize << k) - 1) * air_degree + 1;
    debug_assert!(n_nodes >= 1 << k);
    (0..n_nodes).map(F::from_usize).collect()
}

/// For each target `z` (typically `skip_all_nodes[2^k..]`), the `2^k` Lagrange
/// basis coefficients `L_x(z)` over the base window. Runs once per prove.
pub fn lagrange_coeffs_for_targets<F: Field>(k: usize, targets: &[F]) -> Vec<Vec<F>> {
    lagrange_basis_evals(&skip_domain_points::<F>(k), targets)
}

/// `L_x(r0)` for all `2^k` window nodes, at an extension-field point `r0`.
/// Used for the `2^k → 1` column fold after the skip challenge and as the
/// tensor tail of the WHIR opening weights.
pub fn lagrange_weights_at<F: Field, EF: ExtensionField<F>>(k: usize, r0: EF) -> Vec<EF> {
    let nodes = skip_domain_points::<F>(k);
    let n = nodes.len();
    let den_invs: Vec<F> = (0..n)
        .map(|i| {
            (0..n)
                .filter(|&j| j != i)
                .map(|j| nodes[i] - nodes[j])
                .fold(F::ONE, |acc, d| acc * d)
                .inverse()
        })
        .collect();
    (0..n)
        .map(|i| {
            let num = (0..n)
                .filter(|&j| j != i)
                .map(|j| r0 - EF::from(nodes[j]))
                .fold(EF::ONE, |acc, d| acc * d);
            num * den_invs[i]
        })
        .collect()
}

/// `eq(eq_top, bits(x))` for `x ∈ 0..2^k` — the window values of the eq kernel
/// `ê` (the part of the zerocheck eq factor carried by the skipped variables).
pub fn e_hat_on_window<EF: ExtensionField<PF<EF>>>(eq_top: &[EF]) -> ArenaVec<EF> {
    eval_eq(eq_top)
}

/// `ê(r0) = Σ_x eq(eq_top, bits(x)) · L_x(r0)`: the degree-`(2^k − 1)`
/// univariate extension of the eq kernel over the window, at `r0`.
pub fn e_hat_at<EF: ExtensionField<PF<EF>>>(eq_top: &[EF], r0: EF) -> EF {
    let weights = lagrange_weights_at::<PF<EF>, EF>(eq_top.len(), r0);
    e_hat_on_window(eq_top)
        .iter()
        .zip(&weights)
        .map(|(&e, &w)| e * w)
        .fold(EF::ZERO, |acc, t| acc + t)
}

#[cfg(test)]
mod tests {
    use koala_bear::{KoalaBear, QuinticExtensionFieldKB};

    use super::*;

    type F = KoalaBear;
    type EF = QuinticExtensionFieldKB;

    /// Deterministic scattered field elements (the assertions below are
    /// polynomial identities — any distinct values exercise them).
    fn test_scalar_f(i: usize) -> F {
        F::from_usize(3).exp_u64(7 * i as u64 + 5)
    }
    fn test_scalar_ef(i: usize) -> EF {
        EF::from_basis_coefficients_fn(|j| test_scalar_f(13 * i + j))
    }

    #[test]
    fn test_lagrange_weights_delta_on_nodes() {
        for k in [3, 4] {
            let nodes = skip_domain_points::<F>(k);
            for (y, &node_y) in nodes.iter().enumerate() {
                let weights = lagrange_weights_at::<F, EF>(k, EF::from(node_y));
                for (x, &w) in weights.iter().enumerate() {
                    let expected = if x == y { EF::ONE } else { EF::ZERO };
                    assert_eq!(w, expected, "k={k} x={x} y={y}");
                }
            }
        }
    }

    #[test]
    fn test_lagrange_coeffs_for_targets_reconstruct() {
        // A degree-(2^k − 1) polynomial is reconstructed exactly at the targets
        // from its window values.
        let k = 3;
        let coeffs: Vec<F> = (0..1 << k).map(test_scalar_f).collect();
        let poly_eval = |x: F| coeffs.iter().rfold(F::ZERO, |acc, &c| acc * x + c);
        let all_nodes = skip_all_nodes::<F>(k, 5);
        let window = &all_nodes[..1 << k];
        let targets = &all_nodes[1 << k..];
        assert_eq!(all_nodes.len(), 7 * 5 + 1);
        let lags = lagrange_coeffs_for_targets::<F>(k, targets);
        for (t, &z) in targets.iter().enumerate() {
            let interp = lags[t]
                .iter()
                .zip(window)
                .map(|(&l, &w)| l * poly_eval(w))
                .fold(F::ZERO, |a, b| a + b);
            assert_eq!(interp, poly_eval(z));
        }
    }

    #[test]
    fn test_e_hat_matches_eq_on_window() {
        for k in [3, 4] {
            let eq_top: Vec<EF> = (0..k).map(test_scalar_ef).collect();
            let window = e_hat_on_window(&eq_top);
            for x in 0..1usize << k {
                let at_node = e_hat_at(&eq_top, EF::from_usize(x));
                assert_eq!(at_node, window[x], "k={k} x={x}");
            }
            // And at a random point, ê is consistent with the Lagrange weights.
            let r0: EF = test_scalar_ef(40 + k);
            let weights = lagrange_weights_at::<F, EF>(k, r0);
            let direct = window
                .iter()
                .zip(&weights)
                .map(|(&e, &w)| e * w)
                .fold(EF::ZERO, |a, b| a + b);
            assert_eq!(e_hat_at(&eq_top, r0), direct);
        }
    }
}
