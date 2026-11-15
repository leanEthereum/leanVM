// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The LCH novel basis over `K` (standard basis `v_i = x^i`), and the induction of a level's query weights onto the
//! message's coefficients.

use primitives::field::{Acc8, F64, F64x8, F128, F128x8};

/// `s_k(v_k)` for `k = 0..=log_n`, `v_k = x^k`: the subspace polynomials' normalizers, the verifier's.
pub(crate) fn subspace_roots(log_n: usize) -> Vec<F64> {
    verifier::subspace_roots(log_n).into_iter().map(|k| F64(k.0)).collect()
}

/// `basis_poly[j] = sum_i w_i X_j(q_i)` over the `2^log_msg_cols` coefficients `j`: the queries' column weights,
/// batched by `weights`.
///
/// `X_j` is the product of `What_k` over the bits `k` of `j`, so it splits into a factor `L(j_lo)` on the low bits
/// and `H(j_hi)` on the high ones, and a run of coefficients that share `j_hi` is `sum_i (w_i H_i(j_hi)) L_i(j_lo)`.
pub(crate) fn induce_basis(log_msg_cols: usize, queries: &[usize], weights: &[F128]) -> Vec<F128> {
    assert_eq!(queries.len(), weights.len());
    let lo = log_msg_cols / 2;
    let tables = parallel::map_collect(queries.len(), |i| {
        let what = novel_basis_at(F64(queries[i] as u64), log_msg_cols);
        let mut low = tensor(&what[..lo]);
        // Whole lanes of eight, zero past the table.
        low.resize(low.len().next_multiple_of(8), F64::ZERO);
        (low, tensor(&what[lo..log_msg_cols]))
    });
    let mut basis = parallel::filled(1 << log_msg_cols, F128::ZERO);
    parallel::chunks_mut(&mut basis, 1 << lo, |j_hi, out| {
        let mut acc = vec![Acc8::ZERO; out.len().div_ceil(8)];
        for ((low, high), &w) in tables.iter().zip(weights) {
            let scale = F128x8::splat(w.mul_base(high[j_hi]));
            for (acc, low) in acc.iter_mut().zip(low.as_chunks::<8>().0) {
                *acc += scale.mul_base_unreduced(F64x8::from_array(low));
            }
        }
        for (o, acc) in out.chunks_mut(8).zip(acc) {
            o.copy_from_slice(&acc.reduce().to_array()[..o.len()]);
        }
    });
    basis
}

/// `t[j] = prod_k s[k]^(bit k of j)`.
fn tensor(s: &[F64]) -> Vec<F64> {
    let mut t = vec![F64::ONE];
    for &x in s {
        t.extend_from_within(..);
        let half = t.len() / 2;
        t[half..].iter_mut().for_each(|v| *v *= x);
    }
    t
}

/// `What_i(x) = s_i(x) / s_i(v_i)` for `i <= mu`.
pub(crate) fn novel_basis_at(x: F64, mu: usize) -> Vec<F64> {
    let roots = subspace_roots(mu);
    let mut s = x;
    roots
        .iter()
        .map(|&root| {
            let what = s * root.inv();
            s *= s + root;
            what
        })
        .collect()
}

/// `X_c(x)` from `what = What_i(x)` for every bit `i` of `c`.
fn novel_x_c(c: usize, what: &[F64]) -> F64 {
    (0..usize::BITS as usize)
        .filter(|&i| (c >> i) & 1 == 1)
        .map(|i| what[i])
        .product()
}

/// `sum_j p[j] X_(first + j)(x)`, from `what = What_i(x)` for every bit `i` of the indices: what the coefficients
/// from `first` on add to a polynomial at `x`.
pub(crate) fn novel_sum_at(p: &[F128], first: usize, what: &[F64]) -> F128 {
    p.iter()
        .enumerate()
        .map(|(j, &v)| v.mul_base(novel_x_c(first + j, what)))
        .sum()
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::field::powers;
    use primitives::test_rng::Rng;

    /// The induced basis is the query weights times each coefficient's basis polynomial at the query, written out,
    /// repeated positions included.
    #[test]
    fn induce_matches_the_basis_written_out() {
        let mut rng = Rng::new(9);
        for (log_msg_cols, log_inv_rate, n_queries) in [(0usize, 1usize, 3usize), (6, 2, 40), (7, 3, 40), (12, 2, 30)] {
            let block_len = 1usize << (log_msg_cols + log_inv_rate);
            let mut queries: Vec<usize> = (0..n_queries).map(|_| rng.next_u64() as usize % block_len).collect();
            queries.push(queries[0]);
            let weights = powers(rng.ext(), queries.len());
            let what: Vec<Vec<F64>> = queries
                .iter()
                .map(|&q| novel_basis_at(F64(q as u64), log_msg_cols))
                .collect();
            let want: Vec<F128> = (0..1usize << log_msg_cols)
                .map(|j| {
                    what.iter()
                        .zip(&weights)
                        .map(|(what, &w)| w.mul_base(novel_x_c(j, what)))
                        .sum()
                })
                .collect();
            assert_eq!(
                induce_basis(log_msg_cols, &queries, &weights),
                want,
                "log_msg_cols={log_msg_cols}, rate={log_inv_rate}"
            );
        }
    }
}
