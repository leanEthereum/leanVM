// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// CREDIT: https://github.com/binius-zk/binius64, Apache-2.0.
// Copyright 2025 The Binius Developers
// Copyright 2025 Irreducible, Inc.
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// The rectangular (f = 64, e = 128) generalization of binius64's DP24 ring switch, and a port of its
// `crates/math/src/tensor_algebra.rs`.

//! Ring switching (Annex A): a claim on the bits of the packed witness, at an `E`-point, becomes a claim on the
//! packed `K` words against a transparent `E`-valued weight.
//!
//! A claim on `q_keccak`, `2^n` words of 64 bits each, is its 64 bit slices at a suffix point `r`,
//! `s_hat_v[i] = sum_y eq(r, y) bit_i(q[y])`, which the caller has sent and checked. Their tensor-algebra transpose is
//! 128 `K` elements `t_w` (`transpose_s_hat`). After the challenges of an F_2-linear map `Phi: E -> E`
//! (`coordinate_weights`), the claim is
//!
//! ```text
//!     sum_y Phi(eq(r, y)) q[y] = sum_w Phi(b_w) t_w
//! ```
//!
//! over the coordinate basis `b_w` of `E`: a weighted claim on the packed words, which the stacked opening proves. A
//! nonzero error in the slices survives with probability at most `2 / |E|` (`coordinate_weights`).

use primitives::bit_fold::BitFold;
use primitives::field::{F64, F128};
use primitives::multilinear::eq_table_serial;

/// The degree of `E` over F_2.
pub(crate) const DEGREE_E: usize = 128;

/// The challenges of the batching map: `f_0..f_7`, then `g_0..g_7`.
pub(crate) const MAP_CHALLENGES: usize = 16;

/// `Phi(b_w)` for every coordinate basis element `b_w = x^i y^j` of `E`, `w = 64 j + i` (the order of
/// [`transpose_s_hat`]), where
///
/// ```text
///     Psi(v) = sum_(b<8) g_b v^(2^b),    Phi(v) = sum_(p<8) f_p Psi(v)^(2^(8p)).
/// ```
///
/// `Phi` is F_2-linear, so `sum_w Phi(b_w) t_w = sum_j x^j Phi(y_j)` for the row view `y` and the column view `t` of
/// the same tensor-algebra element: a verifier evaluates the batched claim from the sixteen challenges, as the
/// recursion guest does. Expanding puts one term at every Frobenius exponent below 64:
/// `Phi(v) = sum_(k<64) C_k v^(2^k)` with `C_(8p+b) = f_p g_b^(2^(8p))`.
///
/// ## Soundness
///
/// Let `delta != 0` be the prover's error on the transposed columns, fixed before the challenges. The check misses
/// it iff `sum_w Phi(b_w) delta_w = sum_(k<64) C_k V_k = 0` with `V_k = sum_w b_w^(2^k) delta_w`. Writing
/// `w = 64 j + i` and `b_w = x^i Y^j`,
///
/// ```text
///     V_k = R_(0,k) + Y^(2^k) R_(1,k),   R_(j,k) = sum_(i<64) x^(i 2^k) delta_(64j+i) in K.
/// ```
///
/// `Y^(2^k)` is not in `K` (squaring is a bijection of `K`, so `Y^(2^k)` in `K` would put `Y` in `K`) and
/// `[E:K] = 2`, so `{1, Y^(2^k)}` is a `K`-basis and `V_k = 0` forces both `R_(j,k) = 0`. At fixed `j` those 64
/// equations say that `D_j(U) = sum_(i<64) delta_(64j+i) U^i`, of degree at most 63, vanishes at the 64 distinct
/// points `x, x^2, x^4, ..., x^(2^63)` (`x` has degree 64 over F_2), so `D_j = 0` and `delta = 0`: some `V_k != 0`.
/// Grouped by `p`, the discrepancy is `sum_p f_p M_p` with
/// `M_p = sum_b g_b^(2^(8p)) V_(8p+b) = (sum_b g_b V_(8p+b)^(2^(-8p)))^(2^(8p))`. For a `p` with some
/// `V_(8p+b) != 0`, the inner form is a nonzero linear form in the `g_b`, zero with probability `1 / |E|`, and
/// otherwise the outer one is nonzero in the `f_p`, zero with probability `1 / |E|`: `2 / |E|` in all.
///
/// The 64 terms are also the floor: the weights must separate any nonzero error on the 128 transposed `K` columns,
/// `|S|` `E`-equations, that is `2 |S|` `K`-equations, in 128 `K`-unknowns, and with `2 |S| < 128` a nonzero error
/// lies in the kernel for every choice of coefficients.
pub(crate) fn coordinate_weights(challenges: &[F128; MAP_CHALLENGES]) -> [F128; DEGREE_E] {
    std::array::from_fn(|w| apply_map(F128::from(1u128 << w), challenges))
}

/// `Phi(value)` of [`coordinate_weights`], stage by stage.
fn apply_map(value: F128, challenges: &[F128; MAP_CHALLENGES]) -> F128 {
    let (f, g) = challenges.split_at(MAP_CHALLENGES / 2);
    let mut frobenius = value;
    let mut psi = F128::ZERO;
    for &g_b in g {
        psi += g_b * frobenius;
        frobenius = frobenius.square();
    }
    let mut phi = F128::ZERO;
    for &f_p in f {
        phi += f_p * psi;
        for _ in 0..8 {
            psi = psi.square();
        }
    }
    phi
}

/// The rectangular tensor-algebra transpose: the row view `s_hat_v` of a `K (x) E` element, 64 `E` elements, to its
/// column view, 128 `K` elements: bit `i` of `s_hat_u[w]` is bit `w` of `s_hat_v[i]`.
pub(crate) fn transpose_s_hat(s_hat_v: &[F128; 64]) -> [F64; DEGREE_E] {
    let mut s_hat_u = [F64::ZERO; DEGREE_E];
    for (i, elem) in s_hat_v.iter().enumerate() {
        // Scan the set bits only.
        let mut bits = u128::from(*elem);
        while bits != 0 {
            s_hat_u[bits.trailing_zeros() as usize].0 |= 1u64 << i;
            bits &= bits - 1;
        }
    }
    s_hat_u
}

/// A ring claim's weight `Phi(eq(point, y))` over its suffix domain, `Phi` an F_2-linear map given by its images of
/// the coordinate basis, the claim's batching scalar included.
pub(crate) struct RingWeight {
    pub(crate) phi: [F128; DEGREE_E],
    pub(crate) point: Vec<F128>,
}

impl RingWeight {
    /// `Phi(value)`.
    pub(crate) fn apply(&self, value: F128) -> F128 {
        let mut bits = u128::from(value);
        let mut acc = F128::ZERO;
        while bits != 0 {
            acc += self.phi[bits.trailing_zeros() as usize];
            bits &= bits - 1;
        }
        acc
    }
}

/// `Phi(eq(point, y))` ready to be written out: `eq` as a low and a high table, `Phi` as a bit fold of the products.
pub(crate) struct RingFold {
    eq_lo: Vec<F128>,
    eq_hi: Vec<F128>,
    fold: BitFold,
}

impl RingFold {
    pub(crate) fn new(phi: [F128; DEGREE_E], point: &[F128]) -> Self {
        let lo = (point.len() / 2).clamp(4.min(point.len()), point.len());
        Self {
            eq_lo: eq_table_serial(&point[..lo]),
            eq_hi: eq_table_serial(&point[lo..]),
            fold: BitFold::new(&phi),
        }
    }

    /// `out[j] += Phi(eq(point, start + j))`.
    pub(crate) fn add_chunk(&self, start: usize, out: &mut [F128]) {
        let block_len = self.eq_lo.len();
        assert!(start + out.len() <= block_len * self.eq_hi.len());
        let mut done = 0;
        while done < out.len() {
            let index = start + done;
            let lo = index % block_len;
            let len = (block_len - lo).min(out.len() - done);
            let e_hi = self.eq_hi[index / block_len];
            for (out, &e_lo) in out[done..done + len].iter_mut().zip(&self.eq_lo[lo..lo + len]) {
                *out += self.fold.fold_row(&u128::from(e_lo * e_hi).to_le_bytes());
            }
            done += len;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    /// Bit `w` of an `E` element in the basis `x^i y^j`, `w = 64 j + i`.
    fn ext_bit(e: F128, w: usize) -> u64 {
        (u128::from(e) >> w & 1) as u64
    }

    #[test]
    fn rect_transpose_bit_relation() {
        let mut rng = Rng::new(1);
        let s_hat_v = std::array::from_fn(|_| rng.ext());
        let s_hat_u = transpose_s_hat(&s_hat_v);
        for i in 0..64 {
            for w in 0..DEGREE_E {
                assert_eq!(
                    (s_hat_u[w].0 >> i) & 1,
                    ext_bit(s_hat_v[i], w),
                    "bit ({i}, {w}) not transposed"
                );
            }
        }
    }

    /// The written-out ring weight is `Phi` applied to every `eq` entry, at any start.
    #[test]
    fn ring_fold_writes_phi_of_eq() {
        let mut rng = Rng::new(0xdec0_de01_2345_6789);
        for vars in [0, 3, 10] {
            let weight = RingWeight {
                phi: std::array::from_fn(|_| rng.ext()),
                point: rng.ext_vec(vars),
            };
            let want: Vec<F128> = eq_table_serial(&weight.point)
                .iter()
                .map(|&e| weight.apply(e))
                .collect();
            let fold = RingFold::new(weight.phi, &weight.point);
            for start in [0, want.len() / 3] {
                let mut got = vec![F128::ZERO; want.len() - start];
                fold.add_chunk(start, &mut got);
                assert_eq!(got, want[start..], "vars {vars}, start {start}");
            }
        }
    }

    /// The contract between the native opener and every verifier that batches from `Phi`'s challenges (the recursion
    /// guest, the Lean verifier): weighting the column view by [`coordinate_weights`] equals applying `Phi` to the row
    /// view and combining with `x^j`.
    #[test]
    fn column_weights_match_the_row_side_linearized_map() {
        let mut rng = Rng::new(0xF00D_BEEF_1234_5678);
        for _ in 0..4 {
            let challenges = std::array::from_fn(|_| rng.ext());
            let s_hat_v: [F128; 64] = std::array::from_fn(|_| rng.ext());
            let weights = coordinate_weights(&challenges);
            let lhs: F128 = transpose_s_hat(&s_hat_v)
                .iter()
                .zip(weights)
                .map(|(&t, w)| w.mul_base(t))
                .sum();
            let x = F128::new(2, 0);
            let (mut rhs, mut x_pow) = (F128::ZERO, F128::ONE);
            for y in &s_hat_v {
                rhs += x_pow * apply_map(*y, &challenges);
                x_pow *= x;
            }
            assert_eq!(lhs, rhs, "column weights and row-side Phi disagree");
        }
    }

    /// The two-stage evaluation against the expanded form `sum_k C_k v^(2^k)` with `C_(8p+b) = f_p g_b^(2^(8p))`, the
    /// coefficient table a verifier builds.
    #[test]
    fn map_expands_to_its_coefficients() {
        let mut rng = Rng::new(0x1234_5678_9abc_def0);
        for _ in 0..4 {
            let challenges: [F128; MAP_CHALLENGES] = std::array::from_fn(|_| rng.ext());
            let (f, g) = challenges.split_at(MAP_CHALLENGES / 2);
            let value = rng.ext();
            let (mut expanded, mut frobenius) = (F128::ZERO, value);
            for k in 0..64 {
                let mut g_b = g[k % 8];
                for _ in 0..8 * (k / 8) {
                    g_b = g_b.square();
                }
                expanded += f[k / 8] * g_b * frobenius;
                frobenius = frobenius.square();
            }
            assert_eq!(apply_map(value, &challenges), expanded);
        }
    }
}
