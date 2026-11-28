// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The LCH novel basis over `K` (standard basis `v_i = x^i`), and the induction of a level's query weights onto the
//! message's coefficients.

use primitives::field::{Acc8, F64, F64x8, F128, F128x8, axpy};

use crate::xmul::novel_basis_at;

/// `basis[j] += lambda eq[j] + sum_i w_i X_j(q_i)` over the `2^log_msg_cols` coefficients `j`: the OOD claim's
/// weight and the queries' column weights, batched by `weights`.
///
/// `X_j` is the product of `What_k` over the bits `k` of `j`, so it splits into a factor `L(j_lo)` on the low bits
/// and `H(j_hi)` on the high ones, and a run of coefficients that share `j_hi` is `sum_i (w_i H_i(j_hi)) L_i(j_lo)`.
pub(crate) fn induce_basis(
    basis: &mut [F128],
    lambda: F128,
    eq: &[F128],
    log_msg_cols: usize,
    queries: &[usize],
    weights: &[F128],
) {
    assert_eq!(queries.len(), weights.len());
    assert!(basis.len() == 1 << log_msg_cols && eq.len() == basis.len());
    let lo = log_msg_cols / 2;
    // Per query, `L` and `w H`.
    let tables = parallel::map_collect(queries.len(), |i| {
        let what = novel_basis_at(log_msg_cols, queries[i]);
        let mut low = tensor(&what[..lo]);
        // Whole lanes of eight, zero past the table.
        low.resize(low.len().next_multiple_of(8), F64::ZERO);
        let high: Vec<F128> = tensor(&what[lo..log_msg_cols])
            .into_iter()
            .map(|h| weights[i].mul_base(h))
            .collect();
        (low, high)
    });
    parallel::chunks_mut(basis, 1 << lo, |j_hi, out| {
        axpy(out, lambda, &eq[j_hi << lo..][..out.len()]);
        for (k, out) in out.chunks_mut(8).enumerate() {
            let mut acc = Acc8::ZERO;
            for (low, high) in &tables {
                acc += F128x8::splat(high[j_hi]).mul_base_unreduced(F64x8::load(&low[8 * k..][..8]));
            }
            for (o, induced) in out.iter_mut().zip(acc.reduce().to_array()) {
                *o += induced;
            }
        }
    });
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

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use primitives::field::powers;
    use primitives::test_rng::Rng;

    /// `X_c(x)` from `what = What_i(x)` for every bit `i` of `c`.
    fn novel_x_c(c: usize, what: &[F64]) -> F64 {
        (0..usize::BITS as usize)
            .filter(|&i| (c >> i) & 1 == 1)
            .map(|i| what[i])
            .product()
    }

    /// `sum_j p[j] X_j(x)`, from `what = What_i(x)` for every bit `i` of the indices: the polynomial of novel-basis
    /// coefficients `p` at `x`.
    pub(crate) fn novel_sum_at(p: &[F128], what: &[F64]) -> F128 {
        p.iter().enumerate().map(|(j, &v)| v.mul_base(novel_x_c(j, what))).sum()
    }

    /// The induced basis is the query weights times each coefficient's basis polynomial at the query, written out,
    /// repeated positions included, added with the scaled `eq` to the weight.
    #[test]
    fn induce_matches_the_basis_written_out() {
        let mut rng = Rng::new(9);
        for (log_msg_cols, log_inv_rate, n_queries) in [(0usize, 1usize, 3usize), (6, 2, 40), (7, 3, 40), (12, 2, 30)] {
            let block_len = 1usize << (log_msg_cols + log_inv_rate);
            let mut queries: Vec<usize> = (0..n_queries).map(|_| rng.next_u64() as usize % block_len).collect();
            queries.push(queries[0]);
            let weights = powers(rng.ext(), queries.len());
            let what: Vec<Vec<F64>> = queries.iter().map(|&q| novel_basis_at(log_msg_cols, q)).collect();
            let (mut basis, lambda, eq) = (
                rng.ext_vec(1 << log_msg_cols),
                rng.ext(),
                rng.ext_vec(1 << log_msg_cols),
            );
            let want: Vec<F128> = (0..1usize << log_msg_cols)
                .map(|j| {
                    let induced: F128 = what
                        .iter()
                        .zip(&weights)
                        .map(|(what, &w)| w.mul_base(novel_x_c(j, what)))
                        .sum();
                    basis[j] + lambda * eq[j] + induced
                })
                .collect();
            induce_basis(&mut basis, lambda, &eq, log_msg_cols, &queries, &weights);
            assert_eq!(basis, want, "log_msg_cols={log_msg_cols}, rate={log_inv_rate}");
        }
    }
}
