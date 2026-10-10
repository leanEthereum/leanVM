// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Additive NTT over `K = GF(2^64)` in the Lin-Chung-Han novel polynomial basis.
//!
//! It is the Reed-Solomon encoder of every WHIR commitment.
//!
//! - Layers run neighbors-last: layer 0 pairs rows half the domain apart.
//! - Many independent transforms, the lanes, share one buffer: word `row * n + lane` for `n` lanes.
//! - A large transform is bound by memory bandwidth, so the driver minimizes its sweeps of the buffer.
//!
//! # Extension-field messages
//!
//! Deeper WHIR levels encode a folded witness over `E = GF(2^192)` on the same domain, with the same twiddles in `K`.
//!
//! ```text
//!     an E element is three K coefficients:   a = (a_0, a_1, a_2)
//!
//!     twiddle t in K:     a * t  =  (a_0 * t, a_1 * t, a_2 * t)
//!     addition:           a + b  =  (a_0 + b_0, a_1 + b_1, a_2 + b_2)
//!
//!     so one E lane is three independent K lanes:
//!     row = [ a_0 a_1 a_2 | b_0 b_1 b_2 | ... ]   n E lanes  =  3n K lanes
//! ```
//!
//! Every butterfly acts on each coefficient alone, so an E encode is the base transform over `3n` lanes.

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
use core::arch::aarch64::*;
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "vpclmulqdq",
    target_feature = "avx2",
    not(target_feature = "avx512f")
))]
use core::arch::x86_64::*;
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
use core::arch::x86_64::*;
use parallel::SendPtr;
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
use primitives::field::gf2_64::aarch64::reduce_pair_pmull4;
use primitives::field::gf2_64::{mul_wide, reduce};
use primitives::field::{F64, F192};
use primitives::log2_strict_usize;
use primitives::stream::Stream;
use std::cell::RefCell;

/// Table of the normalized subspace polynomials at the basis `b_0, b_1, ...`.
///
/// ```text
///     W_0(x) = x
///     W_i(x) = W_(i-1)(x) * (W_(i-1)(x) + W_(i-1)(b_(i-1)))
///     s_i(x) = W_i(x) / W_i(b_i)
/// ```
///
/// - Row `i` holds `s_i(b_j)` for every `j >= i`, in order of `j`, so its first entry is one.
/// - The rows are built from the unnormalized `W_i`, then each is divided by its first entry.
fn generate_evals_from_subspace(basis: &[F64]) -> Vec<Vec<F64>> {
    let l = basis.len();
    let mut evals: Vec<Vec<F64>> = Vec::with_capacity(l);
    evals.push(basis.to_vec());
    for i in 1..l {
        let mut row = Vec::with_capacity(l - i);
        for k in 1..evals[i - 1].len() {
            let val = evals[i - 1][k] * (evals[i - 1][k] + evals[i - 1][0]);
            row.push(val);
        }
        evals.push(row);
    }
    for row in evals.iter_mut() {
        let inv = row[0].inv();
        for v in row.iter_mut() {
            *v *= inv;
        }
    }
    evals
}

/// How much the subset sum of `row` changes from index `i - 1` to index `i`: its first `tz(i) + 1` entries summed.
///
/// Going from `i - 1` to `i` flips exactly bits `0..=tz(i)`, and in characteristic 2 each flip adds its entry.
#[inline]
fn step(row: &[F64], i: usize) -> F64 {
    row[..=i.trailing_zeros() as usize]
        .iter()
        .fold(F64::ZERO, |acc, &v| acc + v)
}

/// The subset sum `sum_j bit_j(idx) * basis[j]`.
#[inline]
fn span_get(basis: &[F64], idx: usize) -> F64 {
    let mut acc = F64::ZERO;
    for (j, &b) in basis.iter().enumerate() {
        if (idx >> j) & 1 == 1 {
            acc += b;
        }
    }
    acc
}

/// Receives a finished block of codeword rows as `(first_row, rows)`, the rows row-major.
pub(crate) type RowSink<'a> = dyn Fn(usize, &[F64]) + Sync + 'a;

// An E element is exactly three K words, with no padding, so the two views line up.
const _: () = assert!(size_of::<F192>() == 3 * size_of::<F64>());
const _: () = assert!(align_of::<F192>() == align_of::<F64>());

/// An E slice viewed as its K words: a row of `n` E lanes becomes `3n` K lanes.
const fn ext_words(msg: &[F192]) -> &[F64] {
    // SAFETY: an E element is three K words with no padding and the same alignment, as asserted above.
    // So the view covers exactly the slice's memory, and any word is a valid K element.
    unsafe { std::slice::from_raw_parts(msg.as_ptr().cast::<F64>(), 3 * msg.len()) }
}

/// Additive NTT over `K` on the `F_2`-subspace spanned by `1, x, ..., x^(dim-1)`.
///
/// - Under the integer encoding of `K`, that subspace is the points `0..2^dim`.
/// - Codeword row `p` holds the lanes' values at the point `p`.
/// - Layer `l`'s twiddles are those of the full `2^dim`-point domain, so a codeword must be exactly `2^dim` rows.
#[derive(Clone, Debug)]
pub struct AdditiveNttF64 {
    /// Row `i` holds the normalized `s_i` at the basis elements `b_i, b_(i+1), ...`, for `i < dim`.
    evals: Vec<Vec<F64>>,
}

impl AdditiveNttF64 {
    /// The transform on the subspace spanned by `basis`.
    fn new(basis: &[F64]) -> Self {
        Self {
            evals: generate_evals_from_subspace(basis),
        }
    }

    /// The transform on the standard basis `1, x, ..., x^(dim-1)`: a domain of `2^dim` points.
    ///
    /// # Panics
    ///
    /// Panics if `dim > 63`, far beyond any codeword in use.
    pub fn standard(dim: usize) -> Self {
        assert!(dim <= 63, "standard NTT requires dim ≤ 63");
        let basis: Vec<F64> = (0..dim).map(|i| F64(1u64 << i)).collect();
        Self::new(&basis)
    }

    /// `dim`, the log of the domain's size.
    pub(crate) const fn log_domain_size(&self) -> usize {
        self.evals.len()
    }

    /// Twiddle of one block at one layer.
    ///
    /// - It is `s_i(sum_j bit_j(block) * b_(i+1+j))`, with `i = dim - layer - 1`.
    /// - The normalized `s_i` is F_2-linear, so this is a subset sum of row `i` of the table.
    pub(crate) fn twiddle(&self, layer: usize, block: usize) -> F64 {
        let v = &self.evals[self.log_domain_size() - layer - 1];
        span_get(&v[1..], block)
    }

    /// The seven twiddles of a radix-8 group, breadth-first.
    ///
    /// They are layer `layer`'s for `block`, then `layer + 1`'s for both halves, then `layer + 2`'s for the quarters.
    ///
    /// - A twiddle is a subset sum over the bits of its block index, so it is `F_2`-linear in that index.
    /// - The deeper blocks are `2 * block + h` and `4 * block + q`.
    /// - Each deeper twiddle is then `block`'s part plus one fixed table entry per bit set in `h` or `q`.
    /// - So one scan of `block`'s bits over the three table rows replaces seven scans.
    pub(crate) fn twiddles_radix8(&self, layer: usize, block: usize) -> [F64; 7] {
        let l = self.log_domain_size();
        let (v0, v1, v2) = (
            &self.evals[l - layer - 1],
            &self.evals[l - layer - 2],
            &self.evals[l - layer - 3],
        );
        let (mut t0, mut a, mut c) = (F64::ZERO, F64::ZERO, F64::ZERO);
        for j in 0..layer {
            if (block >> j) & 1 == 1 {
                t0 += v0[1 + j];
                a += v1[2 + j];
                c += v2[3 + j];
            }
        }
        let (d, e0, e1) = (v1[1], v2[1], v2[2]);
        [t0, a, a + d, c, c + e0, c + e1, c + e0 + e1]
    }

    /// Reed-Solomon encode, in place, a message already stored in the codeword's first replica.
    ///
    /// # Overview
    ///
    /// - The message fills the first `1 / 2^r` of `data`, with `r = log_inv_rate`.
    /// - It is row-major: word `row * num_ntts + lane`.
    /// - The buffer ends as `2^r` replicas of it, replica `c` transformed from layer `r` on as block `c`.
    ///
    /// # Why the replication is free
    ///
    /// - A butterfly whose bottom input is zero copies its top input to both outputs.
    /// - So the first `r` layers on the zero-padded message leave `2^r` copies of it.
    /// - The first pass therefore reads its rows from the message itself.
    /// - No pass fills the replicas only to read them back.
    ///
    /// # Why the transpose stays separate
    ///
    /// - A lane-major caller transposes its message into place first.
    /// - The transpose wants one long contiguous run per lane.
    /// - The first pass wants hundreds of scattered rows at once.
    ///
    /// # Panics
    ///
    /// Panics unless `data` is a power-of-two number of rows of `num_ntts` words, the domain's size or less.
    /// Also panics if `log_inv_rate` exceeds the log of that row count.
    pub fn encode_interleaved_in_place(&self, data: &mut [F64], num_ntts: usize, log_inv_rate: usize) {
        // The message is the buffer's own first replica.
        let msg = SendPtr(data.as_mut_ptr());
        self.transform(data, num_ntts, log_inv_rate, Some(msg), None);
    }

    /// Encode in place as above, handing `on_rows` every finished block of rows.
    ///
    /// - It is called as `on_rows(first_row, rows)`, from pool tasks.
    /// - Each row is handed over exactly once, already final.
    /// - Blocks are aligned, and all of one power-of-two size.
    /// - Where the deep pass splits into several tasks, a block goes over while its rows are still in cache.
    pub(crate) fn encode_interleaved_in_place_with(
        &self,
        data: &mut [F64],
        num_ntts: usize,
        log_inv_rate: usize,
        on_rows: &RowSink<'_>,
    ) {
        let msg = SendPtr(data.as_mut_ptr());
        self.transform(data, num_ntts, log_inv_rate, Some(msg), Some(on_rows));
    }

    /// Reed-Solomon encode a message held in a buffer of its own, handing `on_rows` every codeword row, keeping none.
    ///
    /// - Replica `c` of the codeword is the message transformed from layer `r` on, under the twiddles of block `c`.
    /// - The rows go over in aligned blocks of one power-of-two size, each row once, as for the in-place encode.
    /// - No codeword is kept: a caller that needs a row again recomputes it from the message.
    ///
    /// # Plan
    ///
    /// ```text
    ///     replica fits the L3 budget:  one task per run of replicas, each built in scratch from the message
    ///     larger replica:              one or more replicas a round, in one buffer reused by every round:
    ///                                  gathered passes reading the message, then deep sub-blocks in place
    /// ```
    ///
    /// # Panics
    ///
    /// Panics unless the message is a power-of-two number of rows, and the codeword fits the domain.
    pub(crate) fn encode_rows_with(&self, msg: &[F64], num_ntts: usize, log_inv_rate: usize, on_rows: &RowSink<'_>) {
        assert!(num_ntts > 0);
        assert_eq!(msg.len() % num_ntts, 0);
        let log_rows = log2_strict_usize(msg.len() / num_ntts);
        let start = log_inv_rate;
        let log_d = log_rows + start;
        assert!(log_d <= self.log_domain_size());
        // How many rows, as a log, a cache budget holds.
        let fit = |words: usize| (words / num_ntts).max(1).ilog2() as usize;

        if log_rows <= fit(L3_WORDS) {
            // A task takes whole replicas, enough of them for `2^MIN_TASK_LOG` rows where the rate allows.
            let log_group = MIN_TASK_LOG.saturating_sub(log_rows).min(start);
            parallel::for_each(1 << (start - log_group), |task| {
                with_scratch(msg.len() << log_group, |scratch| {
                    let first = task << log_group;
                    for (i, replica) in scratch.chunks_exact_mut(msg.len()).enumerate() {
                        replica.copy_from_slice(msg);
                        self.run_layers(replica, log_d, num_ntts, start, log_d, start, first + i);
                    }
                    on_rows(first << log_rows, scratch);
                });
            });
            return;
        }

        // A round builds a run of consecutive replicas.
        // Its first gathered pass reads each message row once for all of them.
        let log_batch = ((REPLICA_ROUND_WORDS / msg.len()).max(1).ilog2() as usize).min(start);
        // Deep sub-blocks fit L2, and a round cuts into several per worker, since each round ends in a barrier.
        // The layers before them run as gathered passes.
        let fit2 = fit(L2_WORDS);
        let log_tasks = (ROUND_SUBS_PER_WORKER * parallel::num_threads())
            .next_power_of_two()
            .ilog2() as usize;
        let log_sub = fit2
            .min((log_rows + log_batch).saturating_sub(log_tasks))
            .clamp(1, log_rows);
        let deep_start = log_d - log_sub;
        let mut round = Box::new_uninit_slice(msg.len() << log_batch);
        // SAFETY: every round writes each word, by its first gathered pass or by a copy, before any pass reads it.
        let round = unsafe { primitives::write_only(&mut round) };
        let src = SendPtr(msg.as_ptr().cast_mut());
        for first in (0..1usize << start).step_by(1 << log_batch) {
            let mut src = Some(src);
            let mut layer = start;
            while layer < deep_start {
                let g = (deep_start - layer).min(fit2);
                let first_block = first << (layer - start);
                self.gathered_pass(round, log_d, num_ntts, layer, g, first_block, src.take(), false);
                layer += g;
            }
            // Sub-blocks as large as a replica leave no gathered layer, so the round starts as copies of the message.
            if let Some(m) = src {
                replicate(round, m, msg.len());
            }
            let first_sub = first << (deep_start - start);
            parallel::chunks_mut(round, num_ntts << log_sub, |i, sub| {
                self.run_layers(sub, log_d, num_ntts, deep_start, log_d, deep_start, first_sub + i);
                on_rows((first_sub + i) << log_sub, sub);
            });
        }
    }

    /// The codeword rows at `positions` that the row-only encode makes of `msg`, computed from the message alone.
    ///
    /// - Each lane is a polynomial in the novel basis, its coefficients the lane's words in row order.
    /// - Basis polynomial `i` at a point is the product of the normalized `s_k` there, over the bits `k` set in `i`.
    /// - Position `p` is the point whose bits are those of `p`, so a row is one evaluation per lane.
    /// - The result is one row of `num_ntts` words per position, in the order of `positions`.
    ///
    /// # Algorithm
    ///
    /// A coefficient index splits into its `low` low bits and the rest, `i = i_hi * 2^low + i_lo`:
    ///
    /// ```text
    ///     row(p)       = sum_hi  (prod_{k >= low, bit k of i set} s_k(p))  *  sum_lo low_p[i_lo] * msg[i]
    ///                            \______ one K scalar per i_hi ______/
    ///
    ///     low_p[i_lo]  = prod_{k < low, bit k of i_lo set} s_k(p)
    /// ```
    ///
    /// - Each position's low table is built once: `2^low` words of K.
    /// - A task takes one `i_hi` and reads its `2^low` message rows once for every position.
    /// - Its sums stay unreduced until each is reduced once and scaled.
    ///
    /// # Panics
    ///
    /// Panics unless the message is a power-of-two number of rows and every position lies inside the domain.
    pub(crate) fn rows_at(&self, msg: &[F64], num_ntts: usize, positions: &[usize]) -> Vec<F64> {
        /// Most low index bits tabulated per position: a table of at most `2^10` words, 8 KiB of K.
        const LOW_BITS: usize = 10;
        /// Fewest low bits, so that a task reads long runs of contiguous rows.
        const MIN_LOW_BITS: usize = 6;
        assert!(num_ntts > 0);
        assert_eq!(msg.len() % num_ntts, 0);
        let log_rows = log2_strict_usize(msg.len() / num_ntts);
        // Four tasks per worker where the message has rows enough.
        let log_tasks = (4 * parallel::num_threads()).next_power_of_two().ilog2() as usize;
        let low = log_rows
            .saturating_sub(log_tasks)
            .clamp(MIN_LOW_BITS, LOW_BITS)
            .min(log_rows);
        assert!(positions.iter().all(|&p| p >> self.log_domain_size() == 0));

        // Each position's subspace polynomials, then its products over the low bits.
        //
        //     low_p[0] = 1,   low_p[j + 2^k] = low_p[j] * s_k(p)   for j < 2^k
        let factors: Vec<Vec<F64>> = positions
            .iter()
            .map(|&p| (0..log_rows).map(|k| span_get(&self.evals[k], p >> k)).collect())
            .collect();
        let tables: Vec<Vec<F64>> = factors
            .iter()
            .map(|s| {
                let mut table = vec![F64::ONE; 1 << low];
                for (k, &s_k) in s[..low].iter().enumerate() {
                    let (lo, hi) = table.split_at_mut(1 << k);
                    for (h, &l) in hi[..1 << k].iter_mut().zip(lo.iter()) {
                        *h = l * s_k;
                    }
                }
                table
            })
            .collect();

        let width = positions.len() * num_ntts;
        parallel::map_reduce(
            1 << (log_rows - low),
            || vec![F64::ZERO; width],
            |hi| {
                let rows = &msg[(hi << low) * num_ntts..][..num_ntts << low];
                let mut out = vec![F64::ZERO; width];
                let mut sums = vec![0u128; num_ntts];
                for ((s, table), out) in factors.iter().zip(&tables).zip(out.chunks_exact_mut(num_ntts)) {
                    dot_columns(table, rows, &mut sums);
                    // The high factor: `s_k(p)` over the bits `k` set in `hi`, each at index `low + k`.
                    let scale = (s[low..].iter().enumerate())
                        .filter(|&(k, _)| (hi >> k) & 1 == 1)
                        .fold(F64::ONE, |acc, (_, &s_k)| acc * s_k);
                    for (o, &sum) in out.iter_mut().zip(&sums) {
                        *o = F64(reduce(sum)) * scale;
                    }
                }
                out
            },
            |mut acc, part| {
                for (a, &b) in acc.iter_mut().zip(&part) {
                    *a += b;
                }
                acc
            },
        )
    }

    /// Reed-Solomon encode a row-major message of `num_ntts` lanes over `E`, handing `on_rows` every codeword row.
    ///
    /// - It is the row-only encode over the message's `3 * num_ntts` K lanes.
    /// - So each row goes over as K words, three per E lane, and none is kept.
    ///
    /// # Panics
    ///
    /// Panics unless `num_ntts` is a power of two, and wherever the encode over `K` panics.
    pub(crate) fn encode_rows_ext(&self, msg: &[F192], num_ntts: usize, log_inv_rate: usize, on_rows: &RowSink<'_>) {
        assert!(num_ntts.is_power_of_two());
        self.encode_rows_with(ext_words(msg), 3 * num_ntts, log_inv_rate, on_rows);
    }

    /// The codeword rows at `positions` of the encode of `msg` over `E`: one row of `num_ntts` elements per position.
    pub(crate) fn rows_at_ext(&self, msg: &[F192], num_ntts: usize, positions: &[usize]) -> Vec<F192> {
        let rows = self.rows_at(ext_words(msg), 3 * num_ntts, positions);
        (rows.as_chunks::<3>().0.iter())
            .map(|&[c0, c1, c2]| F192::new(c0.0, c1.0, c2.0))
            .collect()
    }

    /// Run layers `start..d` of a `2^d`-row transform in as few sweeps of the buffer as possible.
    ///
    /// A large transform is bound by memory bandwidth, so its cost is its number of sweeps.
    ///
    /// # Plan
    ///
    /// ```text
    ///     layers:  start ............ deep_start ............ d
    ///              |---- gathered passes ----|---- deep pass ----|
    ///
    ///     gathered pass:  one task per row group of 2^g rows, 2^(d - layer - g) apart
    ///                     gathered into L2 scratch, all g layers run there, written back
    ///     deep pass:      one task per run of contiguous sub-blocks, their layers run in place
    /// ```
    ///
    /// - The deep pass takes the layers one L2-sized sub-block holds, or one L3-sized one where that saves a sweep.
    /// - From `2^12` rows on, it also starts late enough to cut enough sub-blocks for every worker.
    /// - Gathered passes, each at most one L2 group of layers, run the layers before it.
    /// - So on one worker, with `n` words a row, up to `(L2 words / n)^2` rows take at most two sweeps.
    ///
    /// # With a message
    ///
    /// - The layer-`start` blocks are not in the buffer yet: each is a copy of the message.
    /// - The first pass reads its rows from the message instead.
    ///
    /// # Why block 0 goes last
    ///
    /// - The message may be the buffer's own block 0.
    /// - So a gathered task visits blocks in descending order, and overwrites block 0 last.
    /// - Tasks own disjoint row residues, so no task reads rows another task writes.
    ///
    /// # Finished rows
    ///
    /// - Where the deep pass splits into several tasks, each hands its final rows to `on_rows` while they are in L2.
    /// - Otherwise the rows go over in parallel blocks once every layer is done.
    fn transform(
        &self,
        data: &mut [F64],
        num_ntts: usize,
        start: usize,
        msg: Option<SendPtr<F64>>,
        on_rows: Option<&RowSink<'_>>,
    ) {
        // The buffer is 2^log_d rows of `num_ntts` words.
        assert!(num_ntts > 0);
        assert_eq!(data.len() % num_ntts, 0);
        let log_d = log2_strict_usize(data.len() / num_ntts);
        assert!(log_d <= self.log_domain_size());
        assert!(start <= log_d);

        /// Below this domain the transform is too small to split across the pool.
        const PARALLEL_FLOOR_LOG_D: usize = 12;
        /// Fewest rows a deep sub-block takes when splitting for parallelism.
        const MIN_SUB_LOG: usize = 8;

        // How many rows, as a log, each cache budget holds.
        //
        //     56 lanes:  2^16 / 56 -> 2^10 rows in L2,  2^18 / 56 -> 2^12 rows in L3
        let fit = |words: usize| (words / num_ntts).max(1).ilog2() as usize;
        let (fit2, fit3) = (fit(L2_WORDS), fit(L3_WORDS));

        // From `2^12` rows on, cut `2^LOG_SUBS_PER_WORKER` deep sub-blocks per worker, each of at least `2^8` rows.
        let par_log = if log_d >= PARALLEL_FLOOR_LOG_D {
            (log2_strict_usize(parallel::num_threads().next_power_of_two()) + LOG_SUBS_PER_WORKER)
                .min(log_d - MIN_SUB_LOG)
        } else {
            0
        };

        // Where the deep pass starts.
        //
        // A deep pass of L3 sub-blocks spills L2, which only pays when it saves a whole sweep.
        //
        //     21 layers, fit2 = 10, fit3 = 12:
        //       L2 deep pass:  2 gathered sweeps (10 + 1 layers), then 10 deep
        //       L3 deep pass:  1 gathered sweep  (9 layers),      then 12 deep  <- one sweep fewer
        //
        //     20 layers: 1 gathered sweep either way, so the deep pass stays in L2
        let gathered_sweeps = |deep: usize| (log_d - start).saturating_sub(deep).div_ceil(fit2);
        let deep = if gathered_sweeps(fit3) < gathered_sweeps(fit2) {
            fit3
        } else {
            fit2
        };
        let deep_start = log_d.saturating_sub(deep).max(par_log).max(start);

        // A buffer this large is evicted before the next pass reads it back.
        let stream = data.len() >= STREAM_MIN_WORDS;

        // Phase 1: gathered passes, each at most one L2 group of layers.
        //
        // Only the first one reads the message.
        let mut msg = msg;
        let mut layer = start;
        while layer < deep_start {
            let g = (deep_start - layer).min(fit2);
            self.gathered_pass(data, log_d, num_ntts, layer, g, 0, msg.take(), stream);
            layer += g;
        }

        // Phase 2: a deep-only plan builds its replicas up front, since its tasks transform in place.
        if let Some(m) = msg {
            replicate(data, m, data.len() >> start);
        }

        // A deep task takes whole sub-blocks, enough of them for `2^MIN_TASK_LOG` rows where there are that many.
        let log_sub = log_d - deep_start;
        let log_group = MIN_TASK_LOG.saturating_sub(log_sub).min(deep_start);

        // A lone deep task runs on this thread, so its rows go over in parallel afterwards instead.
        let fuse = log_group < deep_start && deep_start < log_d;
        let deep_rows = on_rows.filter(|_| fuse);

        // Phase 3: the deep pass, one task per run of contiguous sub-blocks, each run in place.
        if deep_start < log_d {
            let sub_len = num_ntts << log_sub;
            parallel::chunks_mut(data, sub_len << log_group, |task_idx, task| {
                let first_sub = task_idx << log_group;
                for (i, sub) in task.chunks_exact_mut(sub_len).enumerate() {
                    self.run_layers(sub, log_d, num_ntts, deep_start, log_d, deep_start, first_sub + i);
                }
                if let Some(f) = deep_rows {
                    f(first_sub << log_sub, task);
                }
            });
        }

        if let Some(f) = on_rows.filter(|_| !fuse) {
            // Four blocks per worker.
            let log_tasks = (4 * parallel::num_threads()).next_power_of_two().ilog2() as usize;
            let log_rows = log_d - log_tasks.min(log_d);
            parallel::chunks_mut(data, num_ntts << log_rows, |i, rows| f(i << log_rows, rows));
        }
    }

    /// Run layers `layer..layer + g` in one sweep of the buffer, one row group at a time.
    ///
    /// # Row groups
    ///
    /// - A group takes rows `r + i * step`, for `i < 2^g`, of one layer-`layer` block.
    /// - Here `step = 2^(d - layer - g)` and the residue `r < step`.
    /// - Those are exactly the rows the next `g` layers pair with each other.
    ///
    /// ```text
    ///     g = 2, a 16-row block, step = 4, residue r = 1:
    ///
    ///     rows:     0  1  2  3 |  4  5  6  7 |  8  9 10 11 | 12 13 14 15
    ///                  ^              ^              ^              ^
    ///     scratch:  [ row 1, row 5, row 9, row 13 ]   ->  a 4-row transform of its own
    /// ```
    ///
    /// # Why the twiddles still match
    ///
    /// - At layer `L`, a row's block index is `row >> (d - L)`.
    /// - The residue is below `step`, so that shift drops it.
    /// - The scratch transform therefore takes the same twiddles as the full one.
    ///
    /// # With a message
    ///
    /// - Every block's rows come from the message.
    /// - One task takes one residue across all blocks, block 0 last.
    ///
    /// # Part of the domain
    ///
    /// - The buffer holds whole layer-`layer` blocks of the domain, from block `first_block` on.
    /// - That block index picks the twiddles.
    #[allow(clippy::too_many_arguments)]
    fn gathered_pass(
        &self,
        data: &mut [F64],
        log_d: usize,
        num_ntts: usize,
        layer: usize,
        g: usize,
        first_block: usize,
        msg: Option<SendPtr<F64>>,
        stream: bool,
    ) {
        // A group is 2^g rows, `step` rows apart.
        let log_step = log_d - layer - g;
        let (rows, step) = (1usize << g, 1usize << log_step);
        let blocks = data.len() / (num_ntts << (log_d - layer));
        // With a message, a task is one residue across every block.
        // Without one, a task is one (block, residue) pair.
        let n_tasks = if msg.is_some() { step } else { step * blocks };
        let base = SendPtr(data.as_mut_ptr());
        parallel::for_each_chunk(n_tasks, |lo, hi| {
            // One L2-resident scratch of 2^g rows serves every group of the task.
            with_scratch(rows * num_ntts, |scratch| {
                // One fence at the end of the task covers all its streaming stores.
                let stream = stream.then(Stream::new);
                let mut group = |block: usize, r: usize| {
                    // Row `i` of the group, as a word offset inside its block.
                    let row = |i: usize| (r + (i << log_step)) * num_ntts;
                    let block_off = (block << (log_d - layer)) * num_ntts;
                    // Gather: the scattered rows become one contiguous 2^g-row buffer.
                    for (i, dst) in scratch.chunks_exact_mut(num_ntts).enumerate() {
                        // SAFETY:
                        // - The message and the codeword both cover every row addressed here.
                        // - Tasks own disjoint residues, so no other task writes these rows.
                        // - Block 0 is written last, after every read of the message in it.
                        let src = unsafe {
                            match msg {
                                Some(m) => std::slice::from_raw_parts(m.add(row(i)), num_ntts),
                                None => base.slice(block_off + row(i), num_ntts),
                            }
                        };
                        dst.copy_from_slice(src);
                    }
                    // Transform: a (layer + g)-layer domain whose sub-block index is the global block.
                    self.run_layers(
                        scratch,
                        layer + g,
                        num_ntts,
                        layer,
                        layer + g,
                        layer,
                        first_block + block,
                    );
                    // Scatter: every row returns to its place.
                    for (i, src) in scratch.chunks_exact(num_ntts).enumerate() {
                        // SAFETY: this group alone owns these rows of the codeword.
                        let dst = unsafe { base.slice(block_off + row(i), num_ntts) };
                        match &stream {
                            Some(s) => s.copy(dst, src),
                            None => dst.copy_from_slice(src),
                        }
                    }
                };
                for t in lo..hi {
                    if msg.is_some() {
                        // Block 0 may be the message itself, so it is transformed last.
                        for block in (0..blocks).rev() {
                            group(block, t);
                        }
                    } else {
                        // Task index = block * step + residue.
                        group(t >> log_step, t & (step - 1));
                    }
                }
            });
        });
    }

    /// Run layers `first_layer..end_layer` in place over one sub-block of a `2^log_d`-row domain.
    ///
    /// - The domain splits into `2^outer_log` equal sub-blocks, and `buf` is sub-block `sub_idx`.
    /// - That index fixes each block's index in the whole domain, and so its twiddle.
    /// - Three layers fuse into one radix-8 sweep where blocks are wide enough, then two, then one.
    #[allow(clippy::too_many_arguments)]
    fn run_layers(
        &self,
        buf: &mut [F64],
        log_d: usize,
        num_ntts: usize,
        first_layer: usize,
        end_layer: usize,
        outer_log: usize,
        sub_idx: usize,
    ) {
        let mut layer = first_layer;
        while layer < end_layer {
            // This layer's blocks inside the buffer: how many, and their size in rows and words.
            let num_blocks_in_buf = 1usize << (layer - outer_log);
            let block_size = 1usize << (log_d - layer);
            let block_elems = block_size * num_ntts;
            // A block's index in the whole domain, which picks its twiddle.
            let global = |block_in_buf: usize| sub_idx * num_blocks_in_buf + block_in_buf;

            // A twiddle is F_2-linear in its block index, and this layer's blocks are an aligned run.
            //
            //     block i - 1 -> block i flips bits 0..=tz(i), so the twiddle moves by the subset sum of those rows
            // Layer `layer + shift`'s table row, from the entry that bit 0 of this layer's block index selects.
            let rows = |shift: usize| &self.evals[self.log_domain_size() - layer - 1 - shift][1 + shift..];
            if layer + 2 < end_layer && block_size >= 8 {
                // Three layers to go and blocks of at least 8 rows: one radix-8 sweep.
                let eighth = block_size >> 3;
                let (r0, r1, r2) = (rows(0), rows(1), rows(2));
                let mut t = self.twiddles_radix8(layer, global(0));
                for block_in_buf in 0..num_blocks_in_buf {
                    if block_in_buf > 0 {
                        let (d0, d1, d2) = (step(r0, block_in_buf), step(r1, block_in_buf), step(r2, block_in_buf));
                        t[0] += d0;
                        t[1] += d1;
                        t[2] += d1;
                        for t in &mut t[3..] {
                            *t += d2;
                        }
                    }
                    let start = block_in_buf * block_elems;
                    butterfly_interleaved_fused_3layer(&mut buf[start..start + block_elems], &t, eighth, num_ntts);
                }
                layer += 3;
            } else if layer + 1 < end_layer && block_size >= 4 {
                // Two layers to go: one radix-4 sweep.
                let quarter = block_size >> 2;
                let (r0, r1) = (rows(0), rows(1));
                let global_block = global(0);
                let mut t_outer = self.twiddle(layer, global_block);
                let mut t_inner_a = self.twiddle(layer + 1, 2 * global_block);
                // The odd half's block index differs from the even half's in bit 0 alone.
                let odd = self.evals[self.log_domain_size() - layer - 2][1];
                for block_in_buf in 0..num_blocks_in_buf {
                    if block_in_buf > 0 {
                        t_outer += step(r0, block_in_buf);
                        t_inner_a += step(r1, block_in_buf);
                    }
                    let start = block_in_buf * block_elems;
                    butterfly_interleaved_fused_2layer(
                        &mut buf[start..start + block_elems],
                        t_outer,
                        t_inner_a,
                        t_inner_a + odd,
                        quarter,
                        num_ntts,
                    );
                }
                layer += 2;
            } else {
                // One layer: a plain butterfly sweep.
                let block_size_half = block_size >> 1;
                let r0 = rows(0);
                let mut twiddle = self.twiddle(layer, global(0));
                for block_in_buf in 0..num_blocks_in_buf {
                    if block_in_buf > 0 {
                        twiddle += step(r0, block_in_buf);
                    }
                    let start = block_in_buf * block_elems;
                    butterfly_interleaved_block(
                        &mut buf[start..start + block_elems],
                        twiddle,
                        block_size_half,
                        num_ntts,
                    );
                }
                layer += 1;
            }
        }
    }

    /// Undo the forward transform of one lane from layer 0, in place: evaluations back to novel-basis coefficients.
    ///
    /// The layers run in reverse, each butterfly inverted, one at a time on this thread.
    ///
    /// # Panics
    ///
    /// Panics unless `data` has a power-of-two length, the domain's size or less.
    pub fn inverse_transform(&self, data: &mut [F64]) {
        let log_d = log2_strict_usize(data.len());
        assert!(log_d <= self.log_domain_size());
        for layer in (0..log_d).rev() {
            let num_blocks = 1usize << layer;
            let block_size_half = 1usize << (log_d - layer - 1);
            for block in 0..num_blocks {
                let twiddle = self.twiddle(layer, block);
                let block_start = block << (log_d - layer);
                for idx0 in block_start..(block_start + block_size_half) {
                    let idx1 = idx0 | block_size_half;
                    let u = data[idx0];
                    let new_v = data[idx1] + u;
                    data[idx1] = new_v;
                    data[idx0] = u + new_v * twiddle;
                }
            }
        }
    }
}

/// Visit every row group of a fused multi-layer block.
///
/// ```text
///     the block is N slabs of equal height
///
///     slab 0:     row 0   row 1   ...   row r   ...
///     slab 1:     row 0   row 1   ...   row r   ...
///     ...
///     slab N-1:   row 0   row 1   ...   row r   ...
///
///     group r  =  row r of every slab
/// ```
///
/// # Why the rows are disjoint
///
/// - Distinct groups take distinct rows inside each slab.
/// - The slabs do not overlap.
/// - So the groups are pairwise disjoint, and one base pointer can stand in for N nested splits.
fn fused_rows<const N: usize>(
    block: &mut [F64],
    stride_rows: usize,
    num_ntts: usize,
    do_one: impl Fn(&mut [&mut [F64]; N]),
) {
    // Words from one slab to the next.
    let stride = stride_rows * num_ntts;
    debug_assert_eq!(block.len(), N * stride);
    let base = block.as_mut_ptr();
    for r in 0..stride_rows {
        // Row `r` of each slab starts this many words into it.
        let off = r * num_ntts;
        // SAFETY:
        // - The groups are disjoint, as argued above.
        // - The row ends inside its slab, since the row index is below the slab height.
        let mut rows: [&mut [F64]; N] =
            std::array::from_fn(|i| unsafe { std::slice::from_raw_parts_mut(base.add(i * stride + off), num_ntts) });
        do_one(&mut rows);
    }
}

/// Layers L, L+1 and L+2 fused into one sweep over a layer-L block.
///
/// ```text
///     a group is 8 rows, e = (block rows) / 8 apart:  r, r + e, ..., r + 7e
///
///     layer L     pairs rows 4e apart
///     layer L+1   pairs rows 2e apart
///     layer L+2   pairs rows  e apart
/// ```
///
/// - The eight rows stay in L1 across all twelve butterflies.
/// - The seven twiddles are breadth-first: one for layer L, two for L+1, four for L+2.
fn butterfly_interleaved_fused_3layer(block: &mut [F64], t: &[F64; 7], eighth: usize, num_ntts: usize) {
    fused_rows::<8>(block, eighth, num_ntts, |rows| radix8_butterflies(rows, t));
}

/// The twelve butterflies of one radix-8 row group, with its seven twiddles breadth-first.
#[inline(always)]
fn radix8_butterflies(rows: &mut [&mut [F64]; 8], t: &[F64; 7]) {
    let [r0, r1, r2, r3, r4, r5, r6, r7] = rows;
    // Layer L: rows 4 apart, one twiddle for the whole block.
    butterfly_lanes(r0, r4, t[0]);
    butterfly_lanes(r1, r5, t[0]);
    butterfly_lanes(r2, r6, t[0]);
    butterfly_lanes(r3, r7, t[0]);
    // Layer L+1: rows 2 apart, one twiddle per half.
    butterfly_lanes(r0, r2, t[1]);
    butterfly_lanes(r1, r3, t[1]);
    butterfly_lanes(r4, r6, t[2]);
    butterfly_lanes(r5, r7, t[2]);
    // Layer L+2: adjacent rows, one twiddle per quarter.
    butterfly_lanes(r0, r1, t[3]);
    butterfly_lanes(r2, r3, t[4]);
    butterfly_lanes(r4, r5, t[5]);
    butterfly_lanes(r6, r7, t[6]);
}

/// Column sums of rows weighted by a table, as unreduced 128-bit carry-less products.
///
/// ```text
///     sums[w] = sum_j table[j] * rows[j][w]
/// ```
///
/// The rows are `sums.len()` words each, one row per table entry.
fn dot_columns(table: &[F64], rows: &[F64], sums: &mut [u128]) {
    let width = sums.len();
    debug_assert_eq!(rows.len(), table.len() * width);
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    let done = {
        let vectors = width / 8;
        for c in 0..vectors {
            // SAFETY: the target features are enabled at compile time, and words `8c..8c + 8` lie inside every row.
            let column = unsafe { dot_column_avx512(table, rows.as_ptr().add(8 * c), width) };
            sums[8 * c..][..8].copy_from_slice(&column);
        }
        8 * vectors
    };
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    let done = {
        let vectors = width / 8;
        for c in 0..vectors {
            // SAFETY: the target feature is enabled at compile time, and words `8c..8c + 8` lie inside every row.
            let column = unsafe { dot_column_neon(table, rows.as_ptr().add(8 * c), width) };
            sums[8 * c..][..8].copy_from_slice(&column);
        }
        8 * vectors
    };
    #[cfg(not(any(
        all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"),
        all(target_arch = "aarch64", target_feature = "aes")
    )))]
    let done = 0;
    for (w, sum) in sums.iter_mut().enumerate().skip(done) {
        *sum = (table.iter().zip(rows[w..].iter().step_by(width))).fold(0, |acc, (t, x)| acc ^ mul_wide(t.0, x.0));
    }
}

/// The unreduced column sums over eight words of every row, the first at `column`, rows `width` words apart.
///
/// One carry-less multiply takes the even words and another the odd words, one product per 128-bit lane.
///
/// # Safety
///
/// - Requires VPCLMULQDQ and AVX-512F.
/// - `column` must address eight readable words in each of `table.len()` rows.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
unsafe fn dot_column_avx512(table: &[F64], column: *const F64, width: usize) -> [u128; 8] {
    // SAFETY:
    // - The caller supplies eight readable words in every row.
    // - This function's target features cover every intrinsic below.
    unsafe {
        // Sums of the even words' products, then of the odd words', one 128-bit sum per 128-bit lane.
        let (mut even, mut odd) = (_mm512_setzero_si512(), _mm512_setzero_si512());
        for (j, t) in table.iter().enumerate() {
            let x = _mm512_loadu_si512(column.add(j * width).cast());
            let t = _mm512_set1_epi64(t.0 as i64);
            even = _mm512_xor_si512(even, _mm512_clmulepi64_epi128::<0x00>(t, x));
            odd = _mm512_xor_si512(odd, _mm512_clmulepi64_epi128::<0x10>(t, x));
        }
        let (mut e, mut o) = ([0u128; 4], [0u128; 4]);
        _mm512_storeu_si512(e.as_mut_ptr().cast(), even);
        _mm512_storeu_si512(o.as_mut_ptr().cast(), odd);
        std::array::from_fn(|w| if w % 2 == 0 { e[w / 2] } else { o[w / 2] })
    }
}

/// Unreduced column sums over eight words of every row, the first at `column`, rows `width` words apart.
///
/// - Each 128-bit load holds two words.
/// - `PMULL` multiplies the low one by the row's table entry, `PMULL2` the high one.
/// - Two rows go per step, so one three-way XOR folds both of a word's products into its sum.
///
/// # Safety
///
/// - Requires the `aes` target feature.
/// - `column` must address eight readable words in each of `table.len()` rows.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline]
#[target_feature(enable = "aes")]
unsafe fn dot_column_neon(table: &[F64], column: *const F64, width: usize) -> [u128; 8] {
    use primitives::field::neon::xor3_u64;
    // SAFETY:
    // - The caller supplies eight readable words in every row.
    // - This function's target feature covers every intrinsic below.
    unsafe {
        // Row j's eight words as four vectors, each word times the row's table entry t_j.
        //
        //     x[v] = [w_2v, w_2v+1]   ->   (t_j * w_2v, t_j * w_2v+1)
        let products = |j: usize| {
            let row = column.add(j * width).cast::<u64>();
            let t = vdupq_n_u64(table[j].0);
            std::array::from_fn::<_, 4, _>(|v| {
                let x = vld1q_u64(row.add(2 * v));
                let lo = vmull_p64(vgetq_lane_u64::<0>(t), vgetq_lane_u64::<0>(x));
                let hi = vmull_high_p64(vreinterpretq_p64_u64(t), vreinterpretq_p64_u64(x));
                (vreinterpretq_u64_p128(lo), vreinterpretq_u64_p128(hi))
            })
        };
        // One 128-bit sum per word of the column.
        let mut sums = [vdupq_n_u64(0); 8];
        // Rows two at a time: each sum takes both rows' products in one three-way XOR.
        let pairs = table.len() / 2;
        for j in 0..pairs {
            let (a, b) = (products(2 * j), products(2 * j + 1));
            for v in 0..4 {
                sums[2 * v] = xor3_u64(sums[2 * v], a[v].0, b[v].0);
                sums[2 * v + 1] = xor3_u64(sums[2 * v + 1], a[v].1, b[v].1);
            }
        }
        // An odd last row goes alone.
        if table.len() % 2 == 1 {
            let a = products(table.len() - 1);
            for v in 0..4 {
                sums[2 * v] = veorq_u64(sums[2 * v], a[v].0);
                sums[2 * v + 1] = veorq_u64(sums[2 * v + 1], a[v].1);
            }
        }
        sums.map(|s| vreinterpretq_p128_u64(s))
    }
}

/// Transpose a lane-major message into the row-major order the encoder reads.
///
/// # Layout
///
/// ```text
///     input, lane-major:   [ block 0 | block 1 | ... | block n-1 ]   each 2^rows_log words
///     output, row-major:   row x = [ block n-1 word x, ..., block 1 word x, block 0 word x ]
/// ```
///
/// - Codeword lane `t` takes message block `n - 1 - t`.
/// - Any lane count works: a commitment encodes only the lanes that carry data.
///
/// # Why descending
///
/// - A Merkle leaf image lists the blocks from the highest index down, the absent ones zero.
/// - So the absent all-zero blocks lead every leaf image.
/// - Their hash prefix is then one chaining value that every leaf shares, and the proof can leave them out.
/// - Each lane is an independent codeword, so the order costs nothing.
///
/// # Performance
///
/// - Rows are handled one tile at a time.
/// - Each lane adds a contiguous burst of words to an L1-resident tile.
/// - The finished tile goes out as one contiguous run.
/// - That keeps an `n`-way gather at a `2^log_rows` stride near memory bandwidth.
///
/// # Panics
///
/// Panics unless `1 <= n_lanes <= 4096`, the tile's width.
/// Also panics unless `msg` and `out` both hold `n_lanes` blocks of `2^log_rows` words.
pub(crate) fn transpose_lane_major(out: &mut [F64], msg: &[F64], n_lanes: usize, log_rows: usize) {
    let rows = 1usize << log_rows;
    assert!(n_lanes > 0, "a commitment needs at least one lane");
    assert_eq!(msg.len(), n_lanes * rows, "message is n_lanes contiguous lane blocks");
    assert_eq!(out.len(), msg.len(), "the transpose is the same words, reordered");

    /// Words per cache-resident row tile.
    const TILE_WORDS: usize = 4096;
    assert!(n_lanes <= TILE_WORDS, "a codeword row must fit the transpose tile");
    // The largest power-of-two row count whose tile fits.
    // Both it and `rows` are powers of two, so the tiles cover every row.
    //
    // Why: this transpose alone initializes the codeword's message region.
    // A row left out would keep stale bytes, and the proof would fail to verify rather than crash.
    let tile_rows = (1usize << (TILE_WORDS / n_lanes).ilog2()).min(rows);
    assert_eq!(rows % tile_rows, 0, "row tiles must cover every row");

    // Nothing reads the output back before a buffer this large is evicted.
    let stream = out.len() >= STREAM_MIN_WORDS;
    parallel::chunks_mut(out, tile_rows * n_lanes, |t, out_tile| {
        with_scratch(out_tile.len(), |tile| {
            // First message row this tile covers.
            let r0 = t * tile_rows;
            // Fill the tile column by column: lane `lane` takes every `n_lanes`-th word.
            for lane in 0..n_lanes {
                let block = n_lanes - 1 - lane;
                let src = &msg[block * rows + r0..][..tile_rows];
                for (slot, &word) in tile[lane..].iter_mut().step_by(n_lanes).zip(src) {
                    *slot = word;
                }
            }
            // Write the finished tile out as one contiguous run.
            if stream {
                Stream::new().copy(out_tile, tile);
            } else {
                out_tile.copy_from_slice(tile);
            }
        });
    });
}

/// Words one L2-resident unit of work may span: a gathered row group or a deep sub-block.
///
/// # Why this value
///
/// - 2^16 words is 512 KiB.
/// - Two SMT threads share a core's L2 of 1 MiB, so each budgets for half.
///
/// # On Apple silicon
///
/// - A deep layer costs about the same whether its sub-block fits a cache or not: the transform is compute bound.
/// - A gathered layer costs more than a deep one, its rows scattered over more streams than the prefetcher follows.
/// - So the budget is sized to push layers into the deep pass, not to fit a cache.
/// - It exceeds the L3 budget, so the in-place transform's deep pass never takes that one.
#[cfg(not(all(target_arch = "aarch64", target_os = "macos")))]
const L2_WORDS: usize = 1 << 16;
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
const L2_WORDS: usize = 1 << 21;

/// Deep sub-blocks cut per worker, as a log.
///
/// - Apple silicon mixes performance and efficiency cores.
/// - With one sub-block each, the performance cores would wait on the efficiency cores' sub-blocks.
/// - Elsewhere every core is alike, and one each suffices.
#[cfg(not(all(target_arch = "aarch64", target_os = "macos")))]
const LOG_SUBS_PER_WORKER: usize = 0;
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
const LOG_SUBS_PER_WORKER: usize = 2;

/// Fewest rows a deep task covers, as a log.
///
/// - A high-rate encode of a short message leaves sub-blocks of a few rows.
/// - With one task each, the Merkle tree would get blocks smaller than a hash batch, and hash them one leaf at a time.
/// - So a task takes enough contiguous sub-blocks for whole batches, which also spreads its fixed cost.
const MIN_TASK_LOG: usize = 6;

/// Words a deep sub-block may span when that saves a whole sweep.
///
/// # Why this value
///
/// - 2^18 words is 2 MiB, one thread's share of L3.
/// - Such a sub-block spills from L2 into L3.
/// - That costs extra L3 traffic, but saves a whole sweep of DRAM.
const L3_WORDS: usize = 1 << 18;

/// Words a row-only encode builds per round when a replica outgrows L3.
///
/// - A round takes as many whole replicas as fit, and at least one.
/// - Each round ends in barriers, and its first gathered pass reads the whole message.
/// - Several replicas a round share both, which measured faster on aarch64.
/// - Elsewhere the budget is zero, so a round is one replica.
#[cfg(target_arch = "aarch64")]
const REPLICA_ROUND_WORDS: usize = 1 << 22;
#[cfg(not(target_arch = "aarch64"))]
const REPLICA_ROUND_WORDS: usize = 0;

/// Deep sub-blocks a row-only encode cuts each round into, per worker, when a replica outgrows L3.
const ROUND_SUBS_PER_WORKER: usize = 8;

/// Buffers of at least this many words get streaming stores for data a pass does not read back.
///
/// # Why this value
///
/// - 2^23 words is 64 MiB, more than L3 keeps until the next pass.
/// - A streaming store then skips the read an ordinary store makes before it writes.
/// - A smaller buffer stays in L3 for the next pass, which a streaming store would give up.
const STREAM_MIN_WORDS: usize = 1 << 23;

/// Lend this thread's scratch buffer, grown to `len` words.
///
/// - It is cache-line aligned, so a full-width load never splits a line.
/// - It lives as long as the thread, so no pass allocates in its hot loop.
/// - It holds whatever its last user left, so a caller writes every word before reading it.
/// - It is not reentrant: a nested call panics on the borrow.
fn with_scratch<R>(len: usize, f: impl FnOnce(&mut [F64]) -> R) -> R {
    // One cache line of words.
    #[derive(Clone, Copy)]
    #[repr(C, align(64))]
    struct Line([F64; 8]);
    thread_local! {
        static SCRATCH: RefCell<Vec<Line>> = const { RefCell::new(Vec::new()) };
    }
    SCRATCH.with_borrow_mut(|lines| {
        // Grow only; a later, smaller request reuses the same lines.
        if lines.len() * 8 < len {
            lines.resize(len.div_ceil(8), Line([F64::ZERO; 8]));
        }
        // SAFETY:
        // - A line is exactly eight contiguous words, with no padding.
        // - The buffer holds at least the requested words, all initialized.
        f(unsafe { std::slice::from_raw_parts_mut(lines.as_mut_ptr().cast::<F64>(), len) })
    })
}

/// Fill every replica of the buffer with a copy of the message.
///
/// - This is the unfused form of a gathered first pass.
/// - The message may be the buffer's own first replica, which is then left as it is.
fn replicate(data: &mut [F64], msg: SendPtr<F64>, msg_len: usize) {
    // Copy granularity: small enough to spread a short message over every worker.
    const CHUNK: usize = 1 << 14;
    let replicas = data.len() / msg_len;
    let in_place = std::ptr::eq(msg.0, data.as_mut_ptr());
    let chunks = msg_len.div_ceil(CHUNK);
    let dst = SendPtr(data.as_mut_ptr());
    // Replica index innermost, so one worker copies a chunk into several replicas while it is cached.
    parallel::for_each(chunks * replicas, |t| {
        let (c, replica) = (t / replicas, t % replicas);
        // The message already occupies replica 0.
        if in_place && replica == 0 {
            return;
        }
        let start = c * CHUNK;
        let len = CHUNK.min(msg_len - start);
        // SAFETY:
        // - Only this task writes this range.
        // - The range skips replica 0, so it never overlaps a message stored there.
        unsafe {
            let src = std::slice::from_raw_parts(msg.add(start), len);
            dst.slice(replica * msg_len + start, len).copy_from_slice(src);
        }
    });
}

/// Layers L and L+1 fused into one sweep over a layer-L block, four rows at a time.
fn butterfly_interleaved_fused_2layer(
    block: &mut [F64],
    t_outer: F64,
    t_inner_a: F64,
    t_inner_b: F64,
    quarter: usize,
    num_ntts: usize,
) {
    fused_rows::<4>(block, quarter, num_ntts, |rows| {
        let [row_a, row_b, row_c, row_d] = rows;
        // Layer L: rows 2 apart, one twiddle for the block.
        butterfly_lanes(row_a, row_c, t_outer);
        butterfly_lanes(row_b, row_d, t_outer);
        // Layer L+1: adjacent rows, one twiddle per half.
        butterfly_lanes(row_a, row_b, t_inner_a);
        butterfly_lanes(row_c, row_d, t_inner_b);
    });
}

/// One layer over a block: each top-half row paired with the row half a block below it, under one twiddle.
#[inline]
fn butterfly_interleaved_block(block: &mut [F64], twiddle: F64, block_size_half: usize, num_ntts: usize) {
    let half_offset = block_size_half * num_ntts;
    let (top, bot) = block.split_at_mut(half_offset);
    for r in 0..block_size_half {
        let off = r * num_ntts;
        butterfly_lanes(&mut top[off..off + num_ntts], &mut bot[off..off + num_ntts], twiddle);
    }
}

/// The forward butterfly on every lane of a row pair, with a shared twiddle: `u' = u + v * t`, then `v' = v + u'`.
#[inline]
fn butterfly_lanes(top: &mut [F64], bot: &mut [F64], twiddle: F64) {
    lane_butterflies::<false>(top, bot, twiddle);
}

/// The transposed butterfly on every lane of a row pair: `s = u + v`, then `u' = s` and `v' = v + s * t`.
///
/// It is the inverse of the forward butterfly with top and bottom exchanged, on both input and output.
#[inline]
pub(crate) fn transposed_butterfly_lanes(top: &mut [F64], bot: &mut [F64], twiddle: F64) {
    lane_butterflies::<true>(top, bot, twiddle);
}

/// One lane's butterfly, forward or transposed.
#[inline(always)]
fn butterfly_one<const TRANSPOSED: bool>(u: &mut F64, v: &mut F64, t: F64) {
    if TRANSPOSED {
        let s = *u + *v;
        *u = s;
        *v += s * t;
    } else {
        *u += *v * t;
        *v += *u;
    }
}

/// The butterflies of every lane of a row pair, forward or transposed.
///
/// - A zero twiddle needs no product, so the butterfly is one addition.
/// - Otherwise a SIMD kernel takes whole vectors of lanes, and the scalar butterfly the rest.
/// - On NEON a call takes eight lanes as four independent reductions, so their PMULL chains overlap.
/// - There a two-lane kernel takes an even tail, and the scalar butterfly an odd last lane.
#[inline]
fn lane_butterflies<const TRANSPOSED: bool>(top: &mut [F64], bot: &mut [F64], twiddle: F64) {
    debug_assert_eq!(top.len(), bot.len());
    if twiddle == F64::ZERO {
        if TRANSPOSED {
            for (u, v) in top.iter_mut().zip(bot) {
                *u += *v;
            }
        } else {
            for (u, v) in top.iter().zip(bot) {
                *v += *u;
            }
        }
        return;
    }
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    let done = {
        let vectors = top.len() / 8;
        // SAFETY: the features are enabled at compile time, and call `i` touches words `8i..8i + 8` of both rows.
        unsafe {
            for i in 0..vectors {
                butterfly_lanes_avx512::<TRANSPOSED>(
                    top.as_mut_ptr().add(8 * i),
                    bot.as_mut_ptr().add(8 * i),
                    twiddle.0,
                );
            }
        }
        8 * vectors
    };
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "vpclmulqdq",
        target_feature = "avx2",
        not(target_feature = "avx512f")
    ))]
    let done = {
        let vectors = top.len() / 4;
        // SAFETY: the features are enabled at compile time, and call `i` touches words `4i..4i + 4` of both rows.
        unsafe {
            for i in 0..vectors {
                butterfly_lanes_avx2::<TRANSPOSED>(top.as_mut_ptr().add(4 * i), bot.as_mut_ptr().add(4 * i), twiddle.0);
            }
        }
        4 * vectors
    };
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    let done = {
        let vectors = top.len() / 8;
        let mut lane = 8 * vectors;
        // SAFETY:
        // - The `aes` target feature is enabled at compile time.
        // - The eight-lane calls touch words `8i..8i + 8`, and the pair calls `lane..lane + 2`, all inside both rows.
        unsafe {
            for i in 0..vectors {
                butterfly_lanes_neon_8::<TRANSPOSED>(
                    top.as_mut_ptr().add(8 * i),
                    bot.as_mut_ptr().add(8 * i),
                    twiddle.0,
                );
            }
            while lane + 2 <= top.len() {
                butterfly_lane_pair_neon::<TRANSPOSED>(
                    top.as_mut_ptr().add(lane),
                    bot.as_mut_ptr().add(lane),
                    twiddle.0,
                );
                lane += 2;
            }
        }
        lane
    };
    #[cfg(not(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2")
    )))]
    let done = 0;
    for (u, v) in top[done..].iter_mut().zip(&mut bot[done..]) {
        butterfly_one::<TRANSPOSED>(u, v, twiddle);
    }
}

/// Four butterflies with a shared twiddle, for a machine with VPCLMULQDQ but no AVX-512.
///
/// ```text
///     reduce:     p = lo + hi * x^64,  x^64 = x^4 + x^3 + x + 1
///                 p mod f = lo ^ g(hi ^ spill),  g(y) = y ^ y<<1 ^ y<<3 ^ y<<4
///                 spill = n ^ n>>1 ^ n>>3 with n = hi>>60, the bits g pushes past x^63
/// ```
///
/// - The reduction takes no further carry-less multiply, the scarce unit.
/// - The spill is one byte-shuffle lookup of the top nibble.
/// - The left shifts of g are doublings, which issue on more ports than shifts.
///
/// # Safety
///
/// - Requires VPCLMULQDQ and AVX2.
/// - Each pointer must address four readable and writable words.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "vpclmulqdq",
    target_feature = "avx2",
    not(target_feature = "avx512f")
))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx2")]
unsafe fn butterfly_lanes_avx2<const TRANSPOSED: bool>(top: *mut F64, bot: *mut F64, twiddle: u64) {
    // SAFETY:
    // - The caller supplies two valid four-word rows.
    // - This function's target features cover every intrinsic below.
    unsafe {
        let u = _mm256_loadu_si256(top.cast());
        let v = _mm256_loadu_si256(bot.cast());
        let tw = _mm256_set1_epi64x(twiddle as i64);

        // The row multiplied by the twiddle, and the row the product is added to.
        let (m, acc) = if TRANSPOSED {
            (_mm256_xor_si256(u, v), v)
        } else {
            (v, u)
        };

        // Products m * t, one 128-bit product per 128-bit lane, then back to lane order.
        let even = _mm256_clmulepi64_epi128::<0x00>(m, tw);
        let odd = _mm256_clmulepi64_epi128::<0x11>(m, tw);
        let lo = _mm256_unpacklo_epi64(even, odd);
        let hi = _mm256_unpackhi_epi64(even, odd);

        // The spill of every top nibble.
        const SPILL: [u8; 16] = {
            let mut table = [0u8; 16];
            let mut n = 0;
            while n < 16 {
                table[n] = (n ^ (n >> 1) ^ (n >> 3)) as u8;
                n += 1;
            }
            table
        };
        let table = _mm256_broadcastsi128_si256(_mm_loadu_si128(SPILL.as_ptr().cast()));
        let spill = _mm256_shuffle_epi8(table, _mm256_srli_epi64::<60>(hi));
        // Both hi and spill are multiplied by the same constant, so fold them first.
        let x = _mm256_xor_si256(hi, spill);
        let x2 = _mm256_add_epi64(x, x);
        let x8 = {
            let x4 = _mm256_add_epi64(x2, x2);
            _mm256_add_epi64(x4, x4)
        };
        let x16 = _mm256_add_epi64(x8, x8);
        let gx = _mm256_xor_si256(_mm256_xor_si256(x, x2), _mm256_xor_si256(x8, x16));
        let product = _mm256_xor_si256(lo, gx);

        let sum = _mm256_xor_si256(acc, product);
        let (new_u, new_v) = if TRANSPOSED {
            (m, sum)
        } else {
            (sum, _mm256_xor_si256(v, sum))
        };
        _mm256_storeu_si256(top.cast(), new_u);
        _mm256_storeu_si256(bot.cast(), new_v);
    }
}

/// Eight butterflies with a shared twiddle, as four independent NEON two-lane reductions.
///
/// - Every row vector loads before any product, so the core has four independent PMULL chains to overlap.
/// - One call spreads the loop control and the twiddle and reduction constants over eight lanes.
///
/// # Safety
///
/// - Requires the `aes` target feature.
/// - Each pointer must address eight readable and writable words.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline]
#[target_feature(enable = "aes")]
unsafe fn butterfly_lanes_neon_8<const TRANSPOSED: bool>(top: *mut F64, bot: *mut F64, twiddle: u64) {
    // SAFETY:
    // - The caller supplies two valid eight-word rows, and F64 is repr(transparent) over u64.
    // - This function's target feature covers every intrinsic below.
    unsafe {
        let v0 = vld1q_u64(bot.cast());
        let v1 = vld1q_u64(bot.cast::<u64>().add(2));
        let v2 = vld1q_u64(bot.cast::<u64>().add(4));
        let v3 = vld1q_u64(bot.cast::<u64>().add(6));
        let u0 = vld1q_u64(top.cast());
        let u1 = vld1q_u64(top.cast::<u64>().add(2));
        let u2 = vld1q_u64(top.cast::<u64>().add(4));
        let u3 = vld1q_u64(top.cast::<u64>().add(6));
        let tw = vdupq_n_u64(twiddle);
        // The rows multiplied by the twiddle, and the rows the products are added to.
        let ((m0, a0), (m1, a1), (m2, a2), (m3, a3)) = if TRANSPOSED {
            (
                (veorq_u64(u0, v0), v0),
                (veorq_u64(u1, v1), v1),
                (veorq_u64(u2, v2), v2),
                (veorq_u64(u3, v3), v3),
            )
        } else {
            ((v0, u0), (v1, u1), (v2, u2), (v3, u3))
        };

        let p00: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(m0), twiddle));
        let p01: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(m0),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));
        let p10: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(m1), twiddle));
        let p11: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(m1),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));
        let p20: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(m2), twiddle));
        let p21: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(m2),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));
        let p30: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(m3), twiddle));
        let p31: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(m3),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));

        let sum0 = veorq_u64(a0, reduce_pair_pmull4(p00, p01));
        let sum1 = veorq_u64(a1, reduce_pair_pmull4(p10, p11));
        let sum2 = veorq_u64(a2, reduce_pair_pmull4(p20, p21));
        let sum3 = veorq_u64(a3, reduce_pair_pmull4(p30, p31));
        // Forward: u' = u + v * t, then v' = v + u'. Transposed: u' = u + v, then v' = v + u' * t.
        let ((new_u0, new_v0), (new_u1, new_v1), (new_u2, new_v2), (new_u3, new_v3)) = if TRANSPOSED {
            ((m0, sum0), (m1, sum1), (m2, sum2), (m3, sum3))
        } else {
            (
                (sum0, veorq_u64(v0, sum0)),
                (sum1, veorq_u64(v1, sum1)),
                (sum2, veorq_u64(v2, sum2)),
                (sum3, veorq_u64(v3, sum3)),
            )
        };

        vst1q_u64(top.cast(), new_u0);
        vst1q_u64(top.cast::<u64>().add(2), new_u1);
        vst1q_u64(top.cast::<u64>().add(4), new_u2);
        vst1q_u64(top.cast::<u64>().add(6), new_u3);
        vst1q_u64(bot.cast(), new_v0);
        vst1q_u64(bot.cast::<u64>().add(2), new_v1);
        vst1q_u64(bot.cast::<u64>().add(4), new_v2);
        vst1q_u64(bot.cast::<u64>().add(6), new_v3);
    }
}

/// Eight butterflies with a shared twiddle, one per 64-bit lane of an AVX-512 register.
///
/// # Algorithm
///
/// ```text
///     products:   even lanes 0,2,4,6 -> CLMUL 0x00      odd lanes 1,3,5,7 -> CLMUL 0x11
///                 each 128-bit lane then holds one whole 128-bit product
///
///     unpack:     lo = [ lo(p_0), lo(p_1), ..., lo(p_7) ]     hi = [ hi(p_0), ..., hi(p_7) ]
///
///     reduce:     p = lo + hi * x^64,  x^64 = x^4 + x^3 + x + 1
///                 p mod f = lo ^ g(hi ^ spill),  g(y) = y ^ y<<1 ^ y<<3 ^ y<<4
///                 spill = hi>>63 ^ hi>>61 ^ hi>>60, the bits g pushes past x^63
/// ```
///
/// - The unpacks stay inside 128-bit lanes, so no shuffle crosses lanes.
/// - The reduction takes shifts and three-way XORs, `vpternlogq 0x96`, instead of two more carry-less multiplies.
/// - The carry-less multiplier is the scarce unit on Zen 5, so those two would dominate the kernel.
///
/// # Safety
///
/// - Requires VPCLMULQDQ and AVX-512F.
/// - Each pointer must address eight readable and writable words.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx2")]
unsafe fn butterfly_lanes_avx512<const TRANSPOSED: bool>(top: *mut F64, bot: *mut F64, twiddle: u64) {
    // SAFETY:
    // - The caller supplies two valid eight-word rows.
    // - This function's target features cover every intrinsic below.
    unsafe {
        // Load both rows and broadcast the twiddle to every lane.
        let u = _mm512_loadu_si512(top.cast());
        let v = _mm512_loadu_si512(bot.cast());
        let tw = _mm512_set1_epi64(twiddle as i64);
        // The row multiplied by the twiddle, and the row the product is added to.
        let (m, acc) = if TRANSPOSED {
            (_mm512_xor_si512(u, v), v)
        } else {
            (v, u)
        };

        // Products m * t: even lanes, then odd lanes, one 128-bit product per 128-bit lane.
        let even = _mm512_clmulepi64_epi128::<0x00>(m, tw);
        let odd = _mm512_clmulepi64_epi128::<0x11>(m, tw);
        // Back to lane order: qword i of lo / hi is the low / high half of lane i's product.
        let lo = _mm512_unpacklo_epi64(even, odd);
        let hi = _mm512_unpackhi_epi64(even, odd);

        // Reduce modulo x^64 + x^4 + x^3 + x + 1 with shifts and three-way XORs.
        const XOR3: i32 = 0x96;
        // The bits of hi * (x^4 + x^3 + x + 1) that land past x^63.
        let spill = _mm512_ternarylogic_epi64::<XOR3>(
            _mm512_srli_epi64::<63>(hi),
            _mm512_srli_epi64::<61>(hi),
            _mm512_srli_epi64::<60>(hi),
        );
        // Both hi and spill are multiplied by the same constant, so fold them first.
        let x = _mm512_xor_si512(hi, spill);
        // g(x) = x ^ x<<1 ^ x<<3 ^ x<<4, split across two three-way XORs.
        let fx = _mm512_ternarylogic_epi64::<XOR3>(x, _mm512_slli_epi64::<1>(x), _mm512_slli_epi64::<3>(x));
        // acc + m * t, with the product's lo and g(x) folded in one step.
        let sum = _mm512_ternarylogic_epi64::<XOR3>(acc, lo, _mm512_xor_si512(fx, _mm512_slli_epi64::<4>(x)));
        // Forward: u' = u + v * t, then v' = v + u'. Transposed: u' = u + v, then v' = v + u' * t.
        let (new_u, new_v) = if TRANSPOSED {
            (m, sum)
        } else {
            (sum, _mm512_xor_si512(v, sum))
        };
        _mm512_storeu_si512(top.cast(), new_u);
        _mm512_storeu_si512(bot.cast(), new_v);
    }
}

/// Two butterflies with a shared twiddle, kept in NEON registers end to end.
///
/// - PMULL and PMULL2 multiply the loaded row's two words, with no lane extraction.
/// - The two products reduce through a two-lane fold made of carry-less multiplies alone.
///
/// # Safety
///
/// - Requires the `aes` target feature.
/// - Each pointer must address two readable and writable words.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline]
#[target_feature(enable = "aes")]
unsafe fn butterfly_lane_pair_neon<const TRANSPOSED: bool>(top: *mut F64, bot: *mut F64, twiddle: u64) {
    // SAFETY:
    // - The caller supplies two valid two-word rows, and F64 is repr(transparent) over u64.
    // - This function's target feature covers every intrinsic below.
    unsafe {
        let u = vld1q_u64(top as *const u64);
        let v = vld1q_u64(bot as *const u64);
        let m = if TRANSPOSED { veorq_u64(u, v) } else { v };
        // Products by the twiddle: PMULL on the low word, PMULL2 on the high one.
        // The broadcast twiddle is loop-invariant, so it is hoisted once the kernel is inlined.
        let tw = vdupq_n_u64(twiddle);
        let p0: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(m), twiddle));
        let p1: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(m),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));
        let prod = reduce_pair_pmull4(p0, p1);
        let (new_u, new_v) = if TRANSPOSED {
            (m, veorq_u64(v, prod))
        } else {
            let new_u = veorq_u64(u, prod);
            (new_u, veorq_u64(v, new_u))
        };
        vst1q_u64(top as *mut u64, new_u);
        vst1q_u64(bot as *mut u64, new_v);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_util::Rng;
    use std::sync::Mutex;

    /// Test oracle: fill every replica with a copy of a message held elsewhere.
    fn replicate_rows(data: &mut [F64], msg: &[F64]) {
        for replica in data.chunks_mut(msg.len()) {
            replica.copy_from_slice(msg);
        }
    }

    /// Scalar reference: one butterfly at a time over `num_ntts` interleaved lanes.
    fn forward_scalar_from_layer(ntt: &AdditiveNttF64, data: &mut [F64], num_ntts: usize, start_layer: usize) {
        let n_total = data.len();
        let log_d = log2_strict_usize(n_total / num_ntts);

        for layer in start_layer..log_d {
            let num_blocks = 1usize << layer;
            let block_size = 1usize << (log_d - layer);
            let block_size_half = block_size >> 1;
            let block_elems = block_size * num_ntts;
            for block in 0..num_blocks {
                let twiddle = ntt.twiddle(layer, block);
                let block_start = block * block_elems;
                for row in 0..block_size_half {
                    let off_top = block_start + row * num_ntts;
                    let off_bot = off_top + block_size_half * num_ntts;
                    for lane in 0..num_ntts {
                        let v = data[off_bot + lane];
                        let new_u = data[off_top + lane] + v * twiddle;
                        data[off_top + lane] = new_u;
                        data[off_bot + lane] = v + new_u;
                    }
                }
            }
        }
    }

    /// The driver matches the scalar reference, and the inverse transform undoes it.
    #[test]
    fn inverse_roundtrip_and_variants_agree() {
        let ntt = AdditiveNttF64::standard(12);
        let mut rng = Rng::new(1);
        for log_d in [1usize, 3, 6, 10] {
            let n = 1usize << log_d;
            let orig: Vec<F64> = (0..n).map(|_| F64(rng.next_u64())).collect();

            let mut a = orig.clone();
            forward_scalar_from_layer(&ntt, &mut a, 1, 0);
            let mut c = orig.clone();
            ntt.transform(&mut c, 1, 0, None, None);
            assert_eq!(a, c, "parallel == scalar at log_d={log_d}");

            ntt.inverse_transform(&mut a);
            assert_eq!(a, orig, "inverse roundtrip at log_d={log_d}");
        }
    }

    #[test]
    fn interleaved_parallel_matches_scalar() {
        // Invariant: the parallel transform equals the scalar reference, word for word.
        //
        // Each shape forces one plan of the driver, under the budgets used off Apple silicon:
        //
        //     (log_d, lanes, start)   plan
        //     (7, 3, 0)               deep pass only, a single sub-block
        //     (12, 8, 0 or 1)         one gathered pass, then deep sub-blocks
        //     (14, 64, 0 or 1)        one gathered pass, then deep sub-blocks
        //     (10, 2048, 0)           wide rows shrink the cache budgets: one gathered pass
        //     (12, 2048, 1)           two gathered passes, with streaming stores
        //
        // A non-zero start is the commit path, which enters at the rate layer.
        let mut rng = Rng::new(0xC0FFEE);
        for (log_d, lanes, start_layer) in [
            (7usize, 3usize, 0usize),
            (12, 8, 0),
            (12, 8, 1),
            (14, 64, 0),
            (14, 64, 1),
            (10, 2048, 0),
            (12, 2048, 1),
        ] {
            let ntt = AdditiveNttF64::standard(log_d);
            let original: Vec<F64> = (0..lanes << log_d).map(|_| F64(rng.next_u64())).collect();

            // Reference: one butterfly at a time.
            let mut want = original.clone();
            forward_scalar_from_layer(&ntt, &mut want, lanes, start_layer);
            // Under test: the pass-planning driver.
            let mut got = original;
            ntt.transform(&mut got, lanes, start_layer, None, None);

            assert_eq!(got, want, "log_d={log_d}, lanes={lanes}, start_layer={start_layer}");
        }
    }

    #[test]
    fn fused_encode_matches_replicate_then_transform() {
        // Invariant: encoding in place equals replicating the message, then transforming.
        //
        // The in-place encode never materializes the replicas up front.
        // Its message is the buffer's own first replica, which the plan must overwrite last.
        //
        // The plans are those of the budgets used off Apple silicon.
        //
        //     (log_d, lanes, rate)   plan
        //     (9, 8, 1)              replicate first, then deep pass only
        //     (12, 64, 2)            one gathered pass reading the first replica
        //     (14, 8, 1)             one gathered pass reading the first replica
        //     (14, 64, 2)            one gathered pass reading the first replica
        //     (12, 2048, 1)          two gathered passes, with streaming stores
        //     (4, 8, 4)              rate = log_d: no layer left, rows handed over at the end
        //
        // The handed-over rows must tile the codeword once, each block already final.
        let mut rng = Rng::new(0xE0C0DE);
        for (log_d, lanes, log_inv_rate) in [
            (9usize, 8usize, 1usize),
            (12, 64, 2),
            (14, 8, 1),
            (14, 64, 2),
            (12, 2048, 1),
            (4, 8, 4),
        ] {
            let ntt = AdditiveNttF64::standard(log_d);
            let msg_len = (lanes << log_d) >> log_inv_rate;
            let msg: Vec<F64> = (0..msg_len).map(|_| F64(rng.next_u64())).collect();

            // Reference: 2^rate explicit copies, then the scalar transform from the rate layer.
            let mut want = vec![F64::ZERO; msg_len << log_inv_rate];
            replicate_rows(&mut want, &msg);
            forward_scalar_from_layer(&ntt, &mut want, lanes, log_inv_rate);

            // Under test: only the first replica holds the message, the rest is zero.
            let mut got = vec![F64::ZERO; msg_len << log_inv_rate];
            got[..msg_len].copy_from_slice(&msg);
            let blocks = Mutex::new(Vec::new());
            ntt.encode_interleaved_in_place_with(&mut got, lanes, log_inv_rate, &|row, rows| {
                blocks.lock().unwrap().push((row, rows.to_vec()));
            });
            assert_eq!(got, want, "log_d={log_d}, lanes={lanes}, rate={log_inv_rate}");

            let mut blocks = blocks.into_inner().unwrap();
            blocks.sort_by_key(|b| b.0);
            let mut next = 0;
            for (row, rows) in blocks {
                assert_eq!(row, next, "blocks tile the rows, log_d={log_d}");
                assert_eq!(
                    rows[..],
                    want[row * lanes..][..rows.len()],
                    "a handed-over block is final"
                );
                next += rows.len() / lanes;
            }
            assert_eq!(next, 1 << log_d, "every row handed over, log_d={log_d}");
        }
    }

    /// Every codeword lane is the single-lane codeword of its own contiguous message block.
    ///
    /// That makes a commitment over `n_lanes` lanes equal the power-of-two one with a zero tail.
    /// So the shapes include lane counts that are not powers of two.
    #[test]
    fn lane_major_msg_encode_matches_per_lane_reference() {
        let mut rng = Rng::new(0x1A2E);
        for (log_rows, log_inv_rate, n_lanes) in [
            (2usize, 1usize, 3usize),
            (3, 1, 1),
            (5, 2, 7),
            (9, 1, 5),
            (12, 2, 37),
            (14, 1, 64),
        ] {
            let log_d = log_rows + log_inv_rate;
            let ntt = AdditiveNttF64::standard(log_d);
            let rows = 1usize << log_rows;
            let msg: Vec<F64> = (0..rows * n_lanes).map(|_| F64(rng.next_u64())).collect();

            let mut got = vec![F64::ZERO; msg.len() << log_inv_rate];
            transpose_lane_major(&mut got[..msg.len()], &msg, n_lanes, log_rows);
            ntt.encode_interleaved_in_place(&mut got, n_lanes, log_inv_rate);

            let block_len = 1usize << log_d;
            for lane in 0..n_lanes {
                // Lane `lane` encodes message block `n_lanes - 1 - lane`.
                let block = n_lanes - 1 - lane;
                let mut want = vec![F64::ZERO; block_len];
                replicate_rows(&mut want, &msg[block * rows..(block + 1) * rows]);
                ntt.transform(&mut want, 1, log_inv_rate, None, None);
                for pos in 0..block_len {
                    assert_eq!(
                        got[pos * n_lanes + lane],
                        want[pos],
                        "lane {lane} pos {pos} at log_rows={log_rows}, rate={log_inv_rate}, n_lanes={n_lanes}"
                    );
                }
            }
        }
    }

    #[test]
    fn a_deep_pass_in_l3_matches_per_lane_ntts() {
        // Invariant: the plan that gives the deep pass the L3 budget computes the same transform.
        //
        // Fixture state: 8192 lanes, so L2 holds 2^3 rows and L3 2^5 rows.
        //
        //     7 layers, L2 deep pass:  2 gathered sweeps (3 + 1 layers), then 3 deep
        //     7 layers, L3 deep pass:  1 gathered sweep  (2 layers),     then 5 deep  <- taken
        let (log_d, lanes) = (7, 8192);
        let ntt = AdditiveNttF64::standard(log_d);
        let mut rng = Rng::new(0x13);
        let soa: Vec<F64> = (0..lanes << log_d).map(|_| F64(rng.next_u64())).collect();

        // The whole interleaved buffer through the planner.
        let mut got = soa.clone();
        ntt.transform(&mut got, lanes, 0, None, None);

        // Each lane on its own through the scalar transform.
        for lane in 0..lanes {
            let mut want: Vec<F64> = (0..1 << log_d).map(|pos| soa[pos * lanes + lane]).collect();
            forward_scalar_from_layer(&ntt, &mut want, 1, 0);
            for (pos, &w) in want.iter().enumerate() {
                assert_eq!(got[pos * lanes + lane], w, "lane {lane} pos {pos}");
            }
        }
    }

    #[test]
    fn interleaved_lanes_are_independent_ntts() {
        let ntt = AdditiveNttF64::standard(10);
        let mut rng = Rng::new(2);
        let log_d = 7;
        let n = 1usize << log_d;
        for lanes in [1usize, 2, 4, 8, 64] {
            // One interleaved buffer, and a copy of each lane on its own.
            let mut soa = vec![F64::ZERO; n * lanes];
            let mut per_lane: Vec<Vec<F64>> = vec![vec![F64::ZERO; n]; lanes];
            for pos in 0..n {
                for lane in 0..lanes {
                    let v = F64(rng.next_u64());
                    soa[pos * lanes + lane] = v;
                    per_lane[lane][pos] = v;
                }
            }
            ntt.transform(&mut soa, lanes, 0, None, None);
            for (lane, lane_data) in per_lane.iter_mut().enumerate() {
                forward_scalar_from_layer(&ntt, lane_data, 1, 0);
                for pos in 0..n {
                    assert_eq!(soa[pos * lanes + lane], lane_data[pos]);
                }
            }
        }
    }

    /// Reference E-valued transform: one butterfly at a time, with the E-by-K product.
    fn forward_scalar(ntt: &AdditiveNttF64, data: &mut [F192], num_ntts: usize, start_layer: usize) {
        let log_d = log2_strict_usize(data.len() / num_ntts);
        for layer in start_layer..log_d {
            // At this layer, each block pairs its top half with its bottom half.
            let half = 1usize << (log_d - layer - 1);
            for block in 0..1usize << layer {
                // One twiddle per block.
                let twiddle = ntt.twiddle(layer, block);
                for row in block * 2 * half..block * 2 * half + half {
                    for lane in 0..num_ntts {
                        // Butterfly: u' = u + v * t, then v' = v + u'.
                        let (top, bot) = (row * num_ntts + lane, (row + half) * num_ntts + lane);
                        let new_u = data[top] + data[bot].mul_base(twiddle);
                        data[bot] += new_u;
                        data[top] = new_u;
                    }
                }
            }
        }
    }

    #[test]
    fn encode_and_rows_match_replicate_then_scalar_transform() {
        // Invariant: the encode hands over every row of the replicated, E-valued transform exactly once.
        // And a row evaluated from the message is that same row.
        //
        // The reference multiplies true E elements by K twiddles.
        // So a match also proves the three-coefficient view is exact.
        //
        // Each shape forces one plan, under the budgets used off Apple silicon:
        //
        //     (log_d, lanes, rate)   K words a row   plan
        //     (3, 1, 1)              3               whole replicas built in scratch
        //     (8, 4, 2)              12              whole replicas built in scratch
        //     (12, 16, 1)            48              whole replicas built in scratch
        //     (14, 16, 4)            48              whole replicas built in scratch
        //     (15, 16, 2)            48              rounds of replicas: a gathered pass, then deep sub-blocks
        //     (17, 16, 4)            48              sixteen replicas: one a round on x86, eight on aarch64
        //     (16, 2, 1)             6               whole replicas built in scratch, two tasks
        //     (12, 1024, 1)          3072            one replica a round: two gathered passes, then deep sub-blocks
        //     (4, 2, 4)              6               rate = log_d: no layer left, copies only
        let mut rng = Rng::new(0xE192);
        for (log_d, lanes, rate) in [
            (3usize, 1usize, 1usize),
            (8, 4, 2),
            (12, 16, 1),
            (14, 16, 4),
            (15, 16, 2),
            (17, 16, 4),
            (16, 2, 1),
            (12, 1024, 1),
            (4, 2, 4),
        ] {
            let ntt = AdditiveNttF64::standard(log_d);
            let msg = rng.ext_vec((lanes << log_d) >> rate);
            // Reference: 2^rate explicit copies, then the E-valued transform from the rate layer.
            let mut want: Vec<F192> = msg.iter().copied().cycle().take(msg.len() << rate).collect();
            forward_scalar(&ntt, &mut want, lanes, rate);
            let want_words = ext_words(&want);

            // Under test: the rows the encode hands over, each written once into a zeroed codeword.
            let row_words = 3 * lanes;
            let got = Mutex::new((vec![F64::ZERO; want_words.len()], vec![0u32; 1 << log_d]));
            ntt.encode_rows_ext(&msg, lanes, rate, &|row, rows| {
                let (codeword, seen) = &mut *got.lock().unwrap();
                codeword[row * row_words..][..rows.len()].copy_from_slice(rows);
                for count in &mut seen[row..row + rows.len() / row_words] {
                    *count += 1;
                }
            });
            let (codeword, seen) = got.into_inner().unwrap();
            assert!(
                seen.iter().all(|&count| count == 1),
                "log_d={log_d}, lanes={lanes}, rate={rate}"
            );
            assert_eq!(codeword, want_words, "log_d={log_d}, lanes={lanes}, rate={rate}");

            // Rows at spread positions, the first and last included, from the message alone.
            let positions: Vec<usize> = (0..1 << log_d)
                .step_by(((1 << log_d) / 37).max(1))
                .chain([(1 << log_d) - 1, 0])
                .collect();
            let rows = ntt.rows_at_ext(&msg, lanes, &positions);
            for (&p, row) in positions.iter().zip(rows.chunks_exact(lanes)) {
                assert_eq!(
                    row,
                    &want[p * lanes..][..lanes],
                    "position {p}, log_d={log_d}, lanes={lanes}"
                );
            }
        }
    }
}
