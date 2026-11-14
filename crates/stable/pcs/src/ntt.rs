// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! The additive NTT (Lin-Chung-Han novel polynomial basis), the Reed-Solomon encoder of every WHIR commitment.
//!
//! - A buffer is `2^log_d` rows of `num_ntts` words, and each word of a row is one lane: an independent transform.
//! - Layer `i` cuts the rows into `2^i` blocks and pairs each block's top half with its bottom half, row by row, under
//!   one twiddle per block: layer 0 pairs rows half the domain apart, the last layer adjacent rows.
//! - A codeword is `2^r` copies of the message, `r` the log inverse rate, transformed from layer `r` on.
//! - An `E` element is two `K` words and the twiddles lie in `K`, so an `E`-valued encode is the base transform over
//!   twice the lanes (`words`).

use core::ops::{Add, Mul};

use primitives::field::{F64, F64x8, F128};
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

/// `step` on every word pair of two rows under twiddle `t`: eight words at a time, then the rest one by one.
#[inline(always)]
fn zip_rows(
    top: &mut [F64],
    bot: &mut [F64],
    t: F64,
    step8: impl Fn(F64x8, F64x8, F64x8) -> (F64x8, F64x8),
    step: impl Fn(F64, F64, F64) -> (F64, F64),
) {
    let ((top8, top1), (bot8, bot1)) = (top.as_chunks_mut::<8>(), bot.as_chunks_mut::<8>());
    let t8 = F64x8::splat(t);
    for (u, v) in top8.iter_mut().zip(bot8) {
        let (eu, ev) = step8(F64x8::from_array(u), F64x8::from_array(v), t8);
        (*u, *v) = (eu.to_array(), ev.to_array());
    }
    for (u, v) in top1.iter_mut().zip(bot1) {
        (*u, *v) = step(*u, *v, t);
    }
}

/// `u' = u + v t; v' = v + u'`.
#[inline(always)]
fn forward<T: Copy + Add<Output = T> + Mul<Output = T>>(u: T, v: T, t: T) -> (T, T) {
    let u = u + v * t;
    (u, v + u)
}

/// The inverse of [`forward`]: `v' = v + u; u' = u + v' t`.
#[inline(always)]
fn inverse<T: Copy + Add<Output = T> + Mul<Output = T>>(u: T, v: T, t: T) -> (T, T) {
    let v = v + u;
    (u + v * t, v)
}

/// [`forward`] over a pair of rows.
fn butterfly(top: &mut [F64], bot: &mut [F64], t: F64) {
    zip_rows(top, bot, t, forward, forward);
}

/// A slice of `E` elements as its `K` words, low limb first.
pub(crate) fn words(v: &[F128]) -> &[F64] {
    primitives::cast_slice(v)
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
    /// The layers whose blocks are fewer than the pool has tasks run together in one pass ([`Self::top_layers`]).
    /// Then every block of the next layer runs the rest on its own, depth first, so a block's last layers run in cache.
    pub(crate) fn transform(&self, data: &mut [F64], num_ntts: usize, start: usize) {
        let (log_d, split) = self.split(data, num_ntts, start);
        self.top_layers(data, num_ntts << (log_d - split), start, split);
        parallel::chunks_mut(data, num_ntts << (log_d - split), |b, block| {
            self.transform_block(block, num_ntts, split, b);
        });
    }

    /// `log_d`, and the first layer from `start` with as many blocks as the pool has tasks, `start` for a buffer too
    /// small to share out.
    fn split(&self, data: &[F64], num_ntts: usize, start: usize) -> (usize, usize) {
        let log_d = log2_strict_usize(data.len() / num_ntts);
        assert!(log_d <= self.dim && start <= log_d);
        if data.len() < CHUNK {
            return (log_d, start);
        }
        let tasks = 4 * parallel::num_threads();
        (
            log_d,
            (start..log_d).find(|&layer| 1 << layer >= tasks).unwrap_or(log_d),
        )
    }

    /// Layers `start..split` in one pass.
    ///
    /// Those layers pair rows that differ in their block of `split`, of `slab` words, so they act on each group of
    /// `2^(split - start)` rows at one place in every block of `split` inside a block of `start`. A task takes the
    /// same run of words of each block of such a group and runs all the layers on it.
    fn top_layers(&self, data: &mut [F64], slab: usize, start: usize, split: usize) {
        let g = split - start;
        if g == 0 {
            return;
        }
        let chunk = (CHUNK >> g).max(64);
        let mut tasks = Vec::new();
        for (b, block) in data.chunks_exact_mut(slab << g).enumerate() {
            let mut slabs: Vec<_> = block.chunks_exact_mut(slab).map(|s| s.chunks_mut(chunk)).collect();
            for _ in 0..slab.div_ceil(chunk) {
                let runs: Vec<&mut [F64]> = slabs.iter_mut().map(|s| s.next().expect("equal slabs")).collect();
                tasks.push((b, runs));
            }
        }
        parallel::chunks_mut(&mut tasks, 1, |_, task| {
            let (b, runs) = &mut task[0];
            for i in 0..g {
                // Layer `start + i` pairs the runs `2^(g - 1 - i)` apart, under one twiddle per `2^(g - i)` runs.
                let half = 1 << (g - 1 - i);
                for j in (0..1usize << g).filter(|j| j & half == 0) {
                    let t = self.twiddle(start + i, *b << i | j >> (g - i));
                    let (lo, hi) = runs.split_at_mut(j + half);
                    butterfly(lo[j], hi[0], t);
                }
            }
        });
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
        // A chunk of the replicas may straddle two of them: its copy wraps at the message's end.
        parallel::chunks_mut(rest, CHUNK, |i, mut out| {
            let mut at = i * CHUNK % msg.len();
            while !out.is_empty() {
                let n = out.len().min(msg.len() - at);
                out[..n].copy_from_slice(&msg[at..at + n]);
                (out, at) = (&mut out[n..], 0);
            }
        });
        self.transform(data, num_ntts, log_inv_rate);
    }

    /// The codeword of a row-major message held apart, `num_ntts` lanes a row.
    pub(crate) fn encode_rows(&self, msg: &[F64], num_ntts: usize, log_inv_rate: usize) -> Vec<F64> {
        // Every coset a copy of the message, eight words at a time, so the buffer is written once.
        let mut data = parallel::map_collect((msg.len() << log_inv_rate).div_ceil(8), |i| {
            let mut at = 8 * i % msg.len();
            core::array::from_fn::<_, 8, _>(|_| {
                let word = msg[at];
                at = (at + 1) % msg.len();
                word
            })
        })
        .into_flattened();
        data.truncate(msg.len() << log_inv_rate);
        self.transform(&mut data, num_ntts, log_inv_rate);
        data
    }

    /// The codeword of a lane-major message, `n_lanes` blocks of `2^log_rows` words: a row of the codeword holds one
    /// word of every block, block `n_lanes - 1 - t` in lane `t`.
    pub(crate) fn encode_lane_major(&self, msg: &[F64], n_lanes: usize, log_inv_rate: usize) -> Vec<F64> {
        let msg_rows = msg.len() / n_lanes;
        assert_eq!(msg.len(), n_lanes * msg_rows, "the message is n_lanes lane blocks");
        // Eight words at a time, walking rows and lanes from the first, so the buffer is written once.
        let mut data = parallel::map_collect((msg.len() << log_inv_rate).div_ceil(8), |i| {
            let (mut r, mut t) = (8 * i / n_lanes % msg_rows, 8 * i % n_lanes);
            core::array::from_fn::<_, 8, _>(|_| {
                let word = msg[(n_lanes - 1 - t) * msg_rows + r];
                t += 1;
                if t == n_lanes {
                    (r, t) = ((r + 1) % msg_rows, 0);
                }
                word
            })
        })
        .into_flattened();
        data.truncate(msg.len() << log_inv_rate);
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
                zip_rows(top, bot, t, inverse, inverse);
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
            (14, 5, 2),
            (11, 37, 2),
            (13, 40, 4),
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
