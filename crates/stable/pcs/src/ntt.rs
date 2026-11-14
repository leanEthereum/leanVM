// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! The additive NTT (Lin-Chung-Han novel polynomial basis), the Reed-Solomon encoder of every WHIR commitment.
//!
//! - A buffer is `2^log_d` rows of `num_ntts` words, and each word of a row is one lane: an independent transform.
//! - Layer `i` cuts the rows into `2^i` blocks and pairs each block's top half with its bottom half, row by row, under
//!   one twiddle per block: layer 0 pairs rows half the domain apart, the last layer adjacent rows.
//! - A codeword is `2^r` copies of the message, `r` the log inverse rate, transformed from layer `r` on.
//! - An `E` element is two `K` words and the twiddles lie in `K`, so an `E`-valued encode is the base transform over
//!   twice the lanes ([`words`]).

use primitives::field::{F64, F128};
use primitives::log2_strict_usize;

/// Table of the normalized subspace polynomials at the basis, rows end to end.
///
/// - Row `i` holds `s_i(b_j)` for every basis element `b_j` with `j >= i`, so `l - i` values.
/// - Each row is scaled so that its first entry is one.
fn generate_evals_from_subspace(basis: &[F64]) -> Vec<F64> {
    let l = basis.len();
    let mut evals = Vec::with_capacity(l * (l + 1) / 2);
    evals.extend_from_slice(basis);
    let mut prev = 0;
    for i in 1..l {
        for k in 1..=l - i {
            let (v, first) = (evals[prev + k], evals[prev]);
            evals.push(v * (v + first));
        }
        prev += l - i + 1;
    }
    let mut rest = &mut evals[..];
    for i in 0..l {
        let (row, tail) = rest.split_at_mut(l - i);
        let inv = row[0].inv();
        row.iter_mut().for_each(|v| *v *= inv);
        rest = tail;
    }
    evals
}

/// `Σ_j bit_j(idx) · basis[j]`.
fn span_get(basis: &[F64], idx: usize) -> F64 {
    basis
        .iter()
        .enumerate()
        .filter(|(j, _)| (idx >> j) & 1 == 1)
        .map(|(_, &b)| b)
        .sum()
}

/// `u' = u + v t; v' = v + u'` over a pair of rows.
fn butterfly(top: &mut [F64], bot: &mut [F64], t: F64) {
    for (u, v) in top.iter_mut().zip(bot.iter_mut()) {
        *u += *v * t;
        *v += *u;
    }
}

/// The transpose of [`butterfly`]: `s = u + v; u' = s; v' = s t + v`.
pub(crate) fn transpose_butterfly(top: &mut [F64], bot: &mut [F64], t: F64) {
    for (u, v) in top.iter_mut().zip(bot.iter_mut()) {
        *u += *v;
        *v += *u * t;
    }
}

/// A slice of `E` elements as its `K` words, low limb first.
pub(crate) fn words(v: &[F128]) -> &[F64] {
    primitives::cast_slice(v)
}

/// A slice of `E` elements as its `K` words, low limb first.
pub(crate) fn words_mut(v: &mut [F128]) -> &mut [F64] {
    primitives::cast_slice_mut(v)
}

/// Words a task copies or fills at a time.
const CHUNK: usize = 1 << 14;

/// Additive NTT over F_{2^64} on the standard polynomial-basis subspace `{1, x, x^2, ...}`: the integers under
/// their natural encoding.
#[derive(Clone, Debug)]
pub struct AdditiveNttF64 {
    /// The rows of [`generate_evals_from_subspace`], end to end.
    evals: Vec<F64>,
    /// The basis dimension: the log of the largest domain.
    dim: usize,
}

impl AdditiveNttF64 {
    /// Standard NTT with basis `{1, x, …, x^(dim-1)}`. Requires `dim ≤ 63` so the evaluation domain (and the
    /// twiddles) stay inside F_{2^64} without wrap; far beyond any codeword size in use.
    pub fn standard(dim: usize) -> Self {
        assert!(dim <= 63, "standard NTT requires dim ≤ 63");
        let basis: Vec<F64> = (0..dim).map(|i| F64(1u64 << i)).collect();
        Self {
            evals: generate_evals_from_subspace(&basis),
            dim,
        }
    }

    /// Row `i`, which starts after `l + (l - 1) + ... + (l - i + 1)` values.
    fn row(&self, i: usize) -> &[F64] {
        let l = self.dim;
        let start = i * l - i * i.saturating_sub(1) / 2;
        &self.evals[start..start + l - i]
    }

    /// Twiddle of one block at one layer: `s_i(sum_j bit_j(block) * b_(i+1+j))`, with `i = dim - layer - 1`. The
    /// normalized `s_i` is F_2-linear, so this is a subset sum of row `i` of the table.
    pub fn twiddle(&self, layer: usize, block: usize) -> F64 {
        span_get(&self.row(self.dim - layer - 1)[1..], block)
    }

    /// Layers `start..log_d` over `data`, `2^log_d` rows of `num_ntts` words.
    ///
    /// While a layer has fewer blocks than the pool has tasks, each of its butterflies is split across the pool.
    /// Then every block of the layer runs the rest on its own, depth first, so a block's last layers run in cache.
    pub(crate) fn transform(&self, data: &mut [F64], num_ntts: usize, start: usize) {
        let log_d = log2_strict_usize(data.len() / num_ntts);
        assert!(log_d <= self.dim && start <= log_d);
        let tasks = 4 * parallel::num_threads();
        let mut layer = start;
        while layer < log_d && 1 << layer < tasks {
            let half = num_ntts << (log_d - layer - 1);
            for (b, block) in data.chunks_exact_mut(2 * half).enumerate() {
                let (top, bot) = block.split_at_mut(half);
                let t = self.twiddle(layer, b);
                let chunk = CHUNK.min(half);
                parallel::map_reduce_chunks_mut(
                    [top, bot],
                    [chunk; 2],
                    || (),
                    || (),
                    |(), (), _, [top, bot]| butterfly(top, bot, t),
                    |(), ()| (),
                );
            }
            layer += 1;
        }
        if layer < log_d {
            parallel::chunks_mut(data, num_ntts << (log_d - layer), |b, block| {
                self.transform_block(block, num_ntts, layer, b);
            });
        }
    }

    /// Layers `layer..` over block `index` of `layer`, depth first.
    fn transform_block(&self, block: &mut [F64], num_ntts: usize, layer: usize, index: usize) {
        if block.len() == num_ntts {
            return;
        }
        let (top, bot) = block.split_at_mut(block.len() / 2);
        butterfly(top, bot, self.twiddle(layer, index));
        self.transform_block(top, num_ntts, layer + 1, 2 * index);
        self.transform_block(bot, num_ntts, layer + 1, 2 * index + 1);
    }

    /// RS-encode the row-major message in the first `2^-log_inv_rate` of `data`, `num_ntts` lanes a row: every coset
    /// becomes a copy of it, then the transform runs from layer `log_inv_rate`.
    pub fn encode_interleaved_in_place(&self, data: &mut [F64], num_ntts: usize, log_inv_rate: usize) {
        let (msg, rest) = data.split_at_mut(data.len() >> log_inv_rate);
        let msg = &*msg;
        let chunk = CHUNK.min(msg.len());
        parallel::chunks_mut(rest, chunk, |i, out| {
            let at = i * chunk % msg.len();
            out.copy_from_slice(&msg[at..at + out.len()]);
        });
        self.transform(data, num_ntts, log_inv_rate);
    }

    /// The codeword of a row-major message held apart, `num_ntts` lanes a row.
    pub(crate) fn encode_rows(&self, msg: &[F64], num_ntts: usize, log_inv_rate: usize) -> Vec<F64> {
        let mut data = vec![F64::ZERO; msg.len() << log_inv_rate];
        data[..msg.len()].copy_from_slice(msg);
        self.encode_interleaved_in_place(&mut data, num_ntts, log_inv_rate);
        data
    }

    /// The codeword of a lane-major message, `n_lanes` blocks of `2^log_rows` words: a row of the codeword holds one
    /// word of every block, block `n_lanes - 1 - t` in lane `t`.
    pub(crate) fn encode_lane_major(&self, msg: &[F64], n_lanes: usize, log_inv_rate: usize) -> Vec<F64> {
        let msg_rows = msg.len() / n_lanes;
        assert_eq!(msg.len(), n_lanes * msg_rows, "the message is n_lanes lane blocks");
        let rows_per_task = (CHUNK / n_lanes).max(1);
        let mut data = vec![F64::ZERO; msg.len() << log_inv_rate];
        parallel::chunks_mut(&mut data, rows_per_task * n_lanes, |i, out| {
            for (k, row) in out.chunks_exact_mut(n_lanes).enumerate() {
                let r = (i * rows_per_task + k) % msg_rows;
                for (t, word) in row.iter_mut().enumerate() {
                    *word = msg[(n_lanes - 1 - t) * msg_rows + r];
                }
            }
        });
        self.transform(&mut data, n_lanes, log_inv_rate);
        data
    }

    /// Recover novel-basis coefficients from evaluations with a scalar inverse NTT.
    pub fn inverse_transform(&self, data: &mut [F64]) {
        let log_d = log2_strict_usize(data.len());
        assert!(log_d <= self.dim);
        for layer in (0..log_d).rev() {
            let half = 1usize << (log_d - layer - 1);
            for (b, block) in data.chunks_exact_mut(2 * half).enumerate() {
                let t = self.twiddle(layer, b);
                let (top, bot) = block.split_at_mut(half);
                for (u, v) in top.iter_mut().zip(bot.iter_mut()) {
                    *v += *u;
                    *u += *v * t;
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    /// Reference: one butterfly at a time over `num_ntts` interleaved lanes, layers from `start`.
    fn forward_scalar(ntt: &AdditiveNttF64, data: &mut [F64], num_ntts: usize, start: usize) {
        let log_d = log2_strict_usize(data.len() / num_ntts);
        for layer in start..log_d {
            let half = 1usize << (log_d - layer - 1);
            for block in 0..1usize << layer {
                let t = ntt.twiddle(layer, block);
                for row in block * 2 * half..block * 2 * half + half {
                    for lane in 0..num_ntts {
                        let (top, bot) = (row * num_ntts + lane, (row + half) * num_ntts + lane);
                        let new_u = data[top] + data[bot] * t;
                        data[bot] += new_u;
                        data[top] = new_u;
                    }
                }
            }
        }
    }

    fn random(rng: &mut Rng, n: usize) -> Vec<F64> {
        (0..n).map(|_| F64(rng.next_u64())).collect()
    }

    /// The transform and the encodes equal the scalar reference on replicated messages, and the inverse undoes it.
    #[test]
    fn encodes_match_the_scalar_transform() {
        let ntt = AdditiveNttF64::standard(16);
        let mut rng = Rng::new(0xC0FFEE);
        for (log_d, lanes, rate) in [
            (1usize, 1usize, 0usize),
            (3, 1, 1),
            (7, 3, 0),
            (8, 40, 1),
            (12, 8, 2),
            (14, 5, 1),
            (16, 2, 4),
            (4, 2, 4),
        ] {
            let context = format!("log_d={log_d}, lanes={lanes}, rate={rate}");
            let msg = random(&mut rng, (lanes << log_d) >> rate);
            let mut want: Vec<F64> = msg.iter().copied().cycle().take(msg.len() << rate).collect();
            forward_scalar(&ntt, &mut want, lanes, rate);

            let mut got = vec![F64::ZERO; msg.len() << rate];
            got[..msg.len()].copy_from_slice(&msg);
            ntt.encode_interleaved_in_place(&mut got, lanes, rate);
            assert_eq!(got, want, "in place, {context}");
            assert_eq!(ntt.encode_rows(&msg, lanes, rate), want, "held apart, {context}");

            if lanes == 1 && rate == 0 {
                ntt.inverse_transform(&mut got);
                assert_eq!(got, msg, "inverse, {context}");
            }
        }
    }

    /// Lane `t` of the lane-major encode is the single-lane codeword of message block `n_lanes - 1 - t`.
    #[test]
    fn lane_major_encode_matches_per_lane_reference() {
        let mut rng = Rng::new(0x1A2E);
        for (log_rows, rate, n_lanes) in [(2usize, 1usize, 3usize), (3, 1, 1), (5, 2, 7), (9, 1, 5), (12, 2, 37)] {
            let ntt = AdditiveNttF64::standard(log_rows + rate);
            let rows = 1usize << log_rows;
            let msg = random(&mut rng, rows * n_lanes);
            let got = ntt.encode_lane_major(&msg, n_lanes, rate);
            for t in 0..n_lanes {
                let block = &msg[(n_lanes - 1 - t) * rows..][..rows];
                let mut want: Vec<F64> = block.iter().copied().cycle().take(rows << rate).collect();
                forward_scalar(&ntt, &mut want, 1, rate);
                let lane: Vec<F64> = got.iter().skip(t).step_by(n_lanes).copied().collect();
                assert_eq!(
                    lane, want,
                    "lane {t}, log_rows={log_rows}, rate={rate}, n_lanes={n_lanes}"
                );
            }
        }
    }

    /// An `E`-valued encode, as twice the `K` lanes, equals the transform with true `E` by `K` products.
    #[test]
    fn extension_encode_matches_the_extension_transform() {
        let mut rng = Rng::new(0xE128);
        for (log_d, lanes, rate) in [(3usize, 1usize, 1usize), (8, 4, 2), (12, 16, 1), (4, 2, 4)] {
            let ntt = AdditiveNttF64::standard(log_d);
            let msg = rng.ext_vec((lanes << log_d) >> rate);
            let mut want: Vec<F128> = msg.iter().copied().cycle().take(msg.len() << rate).collect();
            for layer in rate..log_d {
                let half = 1usize << (log_d - layer - 1);
                for block in 0..1usize << layer {
                    let t = ntt.twiddle(layer, block);
                    for i in block * 2 * half * lanes..(block * 2 + 1) * half * lanes {
                        let new_u = want[i] + want[i + half * lanes].mul_base(t);
                        want[i + half * lanes] += new_u;
                        want[i] = new_u;
                    }
                }
            }
            let got = ntt.encode_rows(words(&msg), 2 * lanes, rate);
            assert_eq!(got, words(&want), "log_d={log_d}, lanes={lanes}, rate={rate}");
        }
    }
}
