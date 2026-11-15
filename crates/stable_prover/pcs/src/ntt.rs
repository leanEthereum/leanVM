// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! The additive NTT (Lin-Chung-Han novel polynomial basis, Annex D), the Reed-Solomon encoder of every WHIR commitment.
//!
//! - A buffer is `2^log_d` rows of `num_ntts` words, and each word of a row is one lane: an independent transform.
//! - Layer `i` cuts the rows into `2^i` blocks and pairs each block's top half with its bottom half, row by row, under
//!   one twiddle per block: layer 0 pairs rows half the domain apart, the last layer adjacent rows.
//! - A codeword is `2^r` copies of the message, `r` the log inverse rate, transformed from layer `r` on.
//! - An `E` element is two `K` words and the twiddles lie in `K`, so an `E`-valued encode is the base transform over
//!   twice the lanes.
//!
//! A transform runs in two phases, so that a large buffer takes few passes over memory:
//!
//! 1. The layers with fewer blocks than the pool has tasks run together, in one pass.
//! 2. Then each block of the next layer runs the rest on its own, depth first: three layers per pass while the block is
//!    larger than a task's `CHUNK`, then one at a time, in cache. Once a block of at most `CHUNK` words has all its
//!    layers, it goes to the caller's sink while still in cache: the commitments hash it into Merkle leaves there.

use core::ops::{Add, Mul};

use primitives::field::{F64, F64x8};
use primitives::log2_strict_usize;

/// Words of a block that a task transforms in cache and hands to the sink.
const CHUNK: usize = 1 << 14;

/// Words of each block a multi-layer pass takes at a time, so that they stay in L1 through every layer.
const RUN: usize = 1 << 7;

/// Words of a codeword that its first, parallel write produces at a time.
const ITEM: usize = 1 << 12;

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

/// [`forward`] over a pair of rows.
fn butterfly(top: &mut [F64], bot: &mut [F64], t: F64) {
    zip_rows(top, bot, t, forward, forward);
}

/// The words of `msg` repeated end to end, from word `at`, over `out`.
fn copy_cyclic(msg: &[F64], at: usize, mut out: &mut [F64]) {
    let mut at = at % msg.len();
    while !out.is_empty() {
        let n = out.len().min(msg.len() - at);
        out[..n].copy_from_slice(&msg[at..at + n]);
        (out, at) = (&mut out[n..], 0);
    }
}

/// A buffer of `len` words written once, by the pool, [`ITEM`] words at a time: `fill(w, out)` writes the words from
/// `w`, and may run past `len`. It saves the zero fill of a buffer then overwritten.
fn written(len: usize, fill: impl Fn(usize, &mut [F64]) + Sync) -> Vec<F64> {
    crate::collect_chunks(len, |i| {
        let mut out = [F64::ZERO; ITEM];
        fill(i * ITEM, &mut out);
        out
    })
}

/// Additive NTT over `K` on the standard polynomial-basis subspace `{1, x, x^2, ...}`: the integers under their
/// natural encoding.
#[derive(Clone, Debug)]
pub struct AdditiveNttF64 {
    /// Row `i` holds the normalized subspace polynomial `s_i` at `x^j` for every `j > i`, rows end to end.
    rows: Vec<F64>,
    /// The basis dimension: the log of the largest domain.
    dim: usize,
}

impl AdditiveNttF64 {
    /// The transform on domains of up to `2^dim` points, `dim <= 63` so that the domain stays in `K`.
    pub fn standard(dim: usize) -> Self {
        assert!(dim <= 63, "standard NTT requires dim <= 63");
        // `s_0(v) = v` and `s_(i+1)(v) = s_i(v) (s_i(v) + s_i(x^i))`; row `i` is scaled so that `s_i(x^i) = 1`, which
        // it leaves out.
        let mut rows = Vec::with_capacity(dim * (dim + 1) / 2);
        let mut s: Vec<F64> = (0..dim).map(|j| F64(1 << j)).collect();
        while let Some((&first, rest)) = s.split_first() {
            let inv = first.inv();
            rows.extend(rest.iter().map(|&v| v * inv));
            s = rest.iter().map(|&v| v * (v + first)).collect();
        }
        Self { rows, dim }
    }

    /// Twiddle of one block at one layer: `s_i(sum_j bit_j(block) x^(i+1+j))`, `i = dim - layer - 1`. The normalized
    /// `s_i` is F_2-linear, so this is a subset sum of row `i`.
    pub fn twiddle(&self, layer: usize, block: usize) -> F64 {
        let i = self.dim - layer - 1;
        // Row `i` starts after `(dim - 1) + (dim - 2) + ... + (dim - i)` values.
        let row = &self.rows[i * self.dim - i * (i + 1) / 2..][..layer];
        row.iter()
            .enumerate()
            .filter(|(j, _)| (block >> j) & 1 == 1)
            .map(|(_, &s)| s)
            .sum()
    }

    /// Layers `start..log_d` over `data`, `2^log_d` rows of `num_ntts` words, handing `done` each block of finished
    /// rows while it is still in cache, with the run of `out`, one element per row, at the same place.
    fn transform<O: Send>(
        &self,
        data: &mut [F64],
        num_ntts: usize,
        start: usize,
        out: &mut [O],
        done: impl Fn(&[F64], &mut [O]) + Sync,
    ) {
        let log_d = log2_strict_usize(data.len() / num_ntts);
        assert!(log_d <= self.dim && start <= log_d);
        assert_eq!(data.len(), out.len() * num_ntts, "one output per row");
        // The first layer with as many blocks as the pool has tasks, `start` for a buffer too small to share out.
        let tasks = 4 * parallel::num_threads();
        let split = if data.len() < CHUNK {
            start
        } else {
            (start..log_d).find(|&layer| 1 << layer >= tasks).unwrap_or(log_d)
        };
        self.top_layers(data, num_ntts << (log_d - split), start, split);
        let rows = 1 << (log_d - split);
        let mut blocks: Vec<_> = data
            .chunks_exact_mut(rows * num_ntts)
            .zip(out.chunks_exact_mut(rows))
            .collect();
        parallel::chunks_mut(&mut blocks, 1, |b, block| {
            let (block, out) = &mut block[0];
            self.transform_block(block, out, num_ntts, split, b, &done);
        });
    }

    /// Layers `start..split` in one pass, the blocks of `split` being `slab` words.
    ///
    /// Those layers pair rows at one place in different blocks of `split` inside one block of `start`, so a task takes
    /// the same run of words of each of those blocks and runs all the layers on it.
    fn top_layers(&self, data: &mut [F64], slab: usize, start: usize, split: usize) {
        let g = split - start;
        if g == 0 {
            return;
        }
        let run = (CHUNK >> g).max(64);
        let mut tasks = Vec::new();
        for (b, block) in data.chunks_exact_mut(slab << g).enumerate() {
            let mut slabs: Vec<_> = block.chunks_exact_mut(slab).map(|s| s.chunks_mut(run)).collect();
            for _ in 0..slab.div_ceil(run) {
                let runs: Vec<&mut [F64]> = slabs.iter_mut().map(|s| s.next().expect("equal slabs")).collect();
                tasks.push((b, runs));
            }
        }
        parallel::chunks_mut(&mut tasks, 1, |_, task| {
            let (b, runs) = &mut task[0];
            self.layers(runs, start, *b);
        });
    }

    /// Layers `layer..layer + g` over block `index` of `layer`, on equal runs of words at one place in each of its `2^g`
    /// blocks of `layer + g`, [`RUN`] words of each at a time.
    fn layers(&self, runs: &mut [&mut [F64]], layer: usize, index: usize) {
        let g = runs.len().ilog2() as usize;
        // Layer `layer + i` pairs the runs `2^(g - 1 - i)` apart, under one twiddle per `2^(g - i)` runs.
        let pairs: Vec<(usize, usize, F64)> = (0..g)
            .flat_map(|i| {
                let half = 1 << (g - 1 - i);
                (0..1usize << g)
                    .filter(move |j| j & half == 0)
                    .map(move |j| (j, half, self.twiddle(layer + i, index << i | j >> (g - i))))
            })
            .collect();
        let len = runs[0].len();
        for at in (0..len).step_by(RUN) {
            let at = at..(at + RUN).min(len);
            for &(j, half, t) in &pairs {
                let (lo, hi) = runs.split_at_mut(j + half);
                butterfly(&mut lo[j][at.clone()], &mut hi[0][at.clone()], t);
            }
        }
    }

    /// Layers `layer..` over block `index` of `layer`, depth first: three per pass while the block is larger than a
    /// task's [`CHUNK`], as each pass goes to memory, then the rest in cache, after which the block goes to `done`.
    fn transform_block<O>(
        &self,
        block: &mut [F64],
        out: &mut [O],
        num_ntts: usize,
        layer: usize,
        index: usize,
        done: &impl Fn(&[F64], &mut [O]),
    ) {
        let rows = block.len() / num_ntts;
        if block.len() <= CHUNK || rows == 1 {
            self.transform_in_cache(block, num_ntts, layer, index);
            return done(block, out);
        }
        let g = rows.ilog2().min(3) as usize;
        let sub = block.len() >> g;
        self.layers(&mut block.chunks_exact_mut(sub).collect::<Vec<_>>(), layer, index);
        for (j, (block, out)) in block
            .chunks_exact_mut(sub)
            .zip(out.chunks_exact_mut(rows >> g))
            .enumerate()
        {
            self.transform_block(block, out, num_ntts, layer + g, index << g | j, done);
        }
    }

    /// Layers `layer..` over block `index` of `layer`, one at a time, depth first.
    fn transform_in_cache(&self, block: &mut [F64], num_ntts: usize, layer: usize, index: usize) {
        if block.len() > num_ntts {
            let (top, bot) = block.split_at_mut(block.len() / 2);
            butterfly(top, bot, self.twiddle(layer, index));
            self.transform_in_cache(top, num_ntts, layer + 1, 2 * index);
            self.transform_in_cache(bot, num_ntts, layer + 1, 2 * index + 1);
        }
    }

    /// RS-encode the row-major message in the first `2^-log_inv_rate` of `data`, `num_ntts` lanes a row: every coset
    /// becomes a copy of it, then the transform runs from layer `log_inv_rate`.
    pub fn encode_interleaved_in_place(&self, data: &mut [F64], num_ntts: usize, log_inv_rate: usize) {
        let (msg, rest) = data.split_at_mut(data.len() >> log_inv_rate);
        parallel::chunks_mut(rest, CHUNK, |i, out| copy_cyclic(msg, i * CHUNK, out));
        let rows = data.len() / num_ntts;
        self.transform(data, num_ntts, log_inv_rate, &mut vec![(); rows], |_, _| {});
    }

    /// The codeword of a row-major message held apart, `num_ntts` lanes a row, each block of its rows handed to `done`
    /// once finished, with their outputs in `out`, one per row.
    pub(crate) fn encode_rows<O: Send>(
        &self,
        msg: &[F64],
        num_ntts: usize,
        log_inv_rate: usize,
        out: &mut [O],
        done: impl Fn(&[F64], &mut [O]) + Sync,
    ) -> Vec<F64> {
        let mut data = written(msg.len() << log_inv_rate, |w, out| copy_cyclic(msg, w, out));
        self.transform(&mut data, num_ntts, log_inv_rate, out, done);
        data
    }

    /// The codeword of a lane-major message, `n_lanes` blocks of `2^log_rows` words: a row of the codeword holds one
    /// word of every block, block `n_lanes - 1 - t` in lane `t`. Its rows go to `done` as in [`Self::encode_rows`].
    pub(crate) fn encode_lane_major<O: Send>(
        &self,
        msg: &[F64],
        n_lanes: usize,
        log_inv_rate: usize,
        out: &mut [O],
        done: impl Fn(&[F64], &mut [O]) + Sync,
    ) -> Vec<F64> {
        let msg_rows = msg.len() / n_lanes;
        assert!(
            msg.len() == n_lanes * msg_rows && msg_rows.is_power_of_two(),
            "the message is n_lanes lane blocks"
        );
        // A piece of the codeword reads each lane block along the rows it covers: the blocks lie a power of two apart,
        // and reading them across would keep evicting each other from the cache.
        let mut data = written(msg.len() << log_inv_rate, |w, out| {
            for (t, block) in msg.chunks_exact(msg_rows).rev().enumerate() {
                for r in w / n_lanes..(w + out.len()).div_ceil(n_lanes) {
                    if let Some(o) = (r * n_lanes + t).checked_sub(w).and_then(|i| out.get_mut(i)) {
                        *o = block[r & (msg_rows - 1)];
                    }
                }
            }
        });
        self.transform(&mut data, n_lanes, log_inv_rate, out, done);
        data
    }

    /// Recover novel-basis coefficients from evaluations, `num_ntts` lanes a row, on one thread.
    pub fn inverse_transform(&self, data: &mut [F64], num_ntts: usize) {
        let log_d = log2_strict_usize(data.len() / num_ntts);
        assert!(log_d <= self.dim);
        for layer in (0..log_d).rev() {
            let half = num_ntts << (log_d - layer - 1);
            for (b, block) in data.chunks_exact_mut(2 * half).enumerate() {
                let (top, bot) = block.split_at_mut(half);
                zip_rows(top, bot, self.twiddle(layer, b), inverse, inverse);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::field::F128;
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

    /// The codeword `encode` returns, checked against the rows its sink was handed: each row once, finished.
    fn sunk(
        rows: usize,
        num_ntts: usize,
        encode: impl FnOnce(&mut [Vec<F64>], &(dyn Fn(&[F64], &mut [Vec<F64>]) + Sync)) -> Vec<F64>,
    ) -> Vec<F64> {
        let mut seen = vec![Vec::new(); rows];
        let codeword = encode(&mut seen, &|rows, out| {
            for (row, o) in rows.chunks_exact(num_ntts).zip(out) {
                *o = row.to_vec();
            }
        });
        assert_eq!(seen.concat(), codeword, "the sink sees every finished row");
        codeword
    }

    fn random(rng: &mut Rng, n: usize) -> Vec<F64> {
        (0..n).map(|_| F64(rng.next_u64())).collect()
    }

    /// The twiddles are the subset sums of the normalized subspace polynomials, written out from their definition.
    #[test]
    fn twiddles_match_the_subspace_polynomials() {
        let dim = 12;
        let ntt = AdditiveNttF64::standard(dim);
        // `s_i(v) = prod_(u in span(1, x, ..., x^(i-1))) (v + u)`, normalized at `x^i`.
        let s = |i: usize, v: F64| (0..1u64 << i).fold(F64::ONE, |acc, u| acc * (v + F64(u)));
        for layer in 0..dim {
            let i = dim - layer - 1;
            for block in [0, 1, 5, (1 << layer) - 1] {
                let point = F64(((block as u64) << (i + 1)) & ((1 << dim) - 1));
                assert_eq!(
                    ntt.twiddle(layer, block),
                    s(i, point) * s(i, F64(1 << i)).inv(),
                    "layer {layer}"
                );
            }
        }
    }

    /// The transform and the encodes equal the scalar reference on replicated messages, and the inverse undoes it.
    #[test]
    fn encodes_match_the_scalar_transform() {
        let ntt = AdditiveNttF64::standard(18);
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
            (18, 24, 1),
        ] {
            let context = format!("log_d={log_d}, lanes={lanes}, rate={rate}");
            let msg = random(&mut rng, (lanes << log_d) >> rate);
            let mut want: Vec<F64> = msg.iter().copied().cycle().take(msg.len() << rate).collect();
            forward_scalar(&ntt, &mut want, lanes, rate);

            let mut got = vec![F64::ZERO; msg.len() << rate];
            got[..msg.len()].copy_from_slice(&msg);
            ntt.encode_interleaved_in_place(&mut got, lanes, rate);
            assert_eq!(got, want, "in place, {context}");
            let held = sunk(1 << log_d, lanes, |out, done| {
                ntt.encode_rows(&msg, lanes, rate, out, done)
            });
            assert_eq!(held, want, "held apart, {context}");

            if lanes == 1 && rate == 0 {
                ntt.inverse_transform(&mut got, 1);
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
            let got = sunk(rows << rate, n_lanes, |out, done| {
                ntt.encode_lane_major(&msg, n_lanes, rate, out, done)
            });
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
            let got = sunk(1 << log_d, 2 * lanes, |out, done| {
                ntt.encode_rows(primitives::cast_slice(&msg), 2 * lanes, rate, out, done)
            });
            assert_eq!(
                got,
                primitives::cast_slice::<F128, F64>(&want),
                "log_d={log_d}, lanes={lanes}, rate={rate}"
            );
        }
    }
}
