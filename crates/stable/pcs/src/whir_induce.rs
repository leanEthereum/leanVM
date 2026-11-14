// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The LCH novel basis over `K` (standard basis `v_i = x^i`), and the induction of a level's query weights onto the
//! message's coefficients.

use crate::ntt::{AdditiveNttF64, words_mut};
use primitives::field::{F64, F128};

fn next_s(s: F64, s_at_root: F64) -> F64 {
    s * s + s_at_root * s
}

/// `sks_vks[k] = s_k(v_k)` for `k = 0..=log_n`, over K. Public for the recursion harness, which dumps
/// these vanishing-polynomial values as guest hints (base-field, embedded into
/// `E` with its `y` limb zero).
pub fn eval_sk_at_vks(log_n: usize) -> Vec<F64> {
    let mut sks_vks = vec![F64::ZERO; log_n + 1];
    sks_vks[0] = F64::ONE;
    if log_n == 0 {
        return sks_vks;
    }
    let mut layer: Vec<F64> = (1..=log_n).map(|i| F64(1u64 << i)).collect();
    let mut cur_len = log_n;
    for i in 0..log_n {
        for j in 0..cur_len {
            let sk_at_vk = next_s(layer[j], sks_vks[i]);
            if j == 0 {
                sks_vks[i + 1] = sk_at_vk;
            } else {
                layer[j - 1] = sk_at_vk;
            }
        }
        cur_len -= 1;
    }
    sks_vks
}

/// `basis_poly[j] = sum_i w_i X_j(q_i)` over the `2^log_msg_cols` coefficients `j`: the queries' column weights,
/// batched by `weights`.
///
/// The codeword at `q` is the forward transform of the zero-padded message, so this is the transposed transform of
/// the weights scattered onto their positions, cut to the message's coefficients.
pub(crate) fn induce_basis(log_msg_cols: usize, log_inv_rate: usize, queries: &[usize], weights: &[F128]) -> Vec<F128> {
    let log_d = log_msg_cols + log_inv_rate;
    let _span = tracing::info_span!("NTT", kind = "transpose induce", log_domain = log_d).entered();
    let mut data = vec![F128::ZERO; 1 << log_d];
    for (&q, &w) in queries.iter().zip(weights) {
        data[q] += w;
    }
    AdditiveNttF64::standard(log_d).transpose_transform(words_mut(&mut data), 2);
    data.truncate(1 << log_msg_cols);
    data
}

/// `W-hat_i(x) = s_i(x) / s_i(v_i)` for `i <= mu`.
pub(crate) fn novel_basis_at(x: F64, mu: usize) -> Vec<F64> {
    let sks_vks = eval_sk_at_vks(mu);
    let mut out = vec![x; mu + 1];
    for i in 1..out.len() {
        out[i] = next_s(out[i - 1], sks_vks[i - 1]);
    }
    for (v, &s) in out.iter_mut().zip(&sks_vks) {
        *v *= if s.is_zero() { F64::ZERO } else { s.inv() };
    }
    out
}

/// `X_c(x)` from `what = W-hat_i(x)` for every bit `i` of `c`.
fn novel_x_c(c: usize, what: &[F64]) -> F64 {
    (0..usize::BITS as usize)
        .filter(|&i| (c >> i) & 1 == 1)
        .map(|i| what[i])
        .product()
}

/// `sum_j p[j] X_(first + j)(x)`, from `what = W-hat_i(x)` for every bit `i` of the indices: what the coefficients
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
                induce_basis(log_msg_cols, log_inv_rate, &queries, &weights),
                want,
                "log_msg_cols={log_msg_cols}, rate={log_inv_rate}"
            );
        }
    }
}
