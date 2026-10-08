//! Additive NTT over GF(2^64) in the Lin-Chung-Han novel polynomial basis.
//!
//! It is the Reed-Solomon encoder of every WHIR commitment over K = F_{2^64}.
//!
//! - Layers run neighbors-last: layer 0 pairs rows half the domain apart.
//! - Many independent transforms share one buffer, interleaved row by row.
//! - The E-valued encodes of deeper WHIR levels reuse it, one F64 lane per F192 coefficient.
//! - Large transforms are bound by memory bandwidth, so the driver minimizes sweeps of the buffer.

use primitives::{Field, PackedValue, PrimeCharacteristicRing};

use parallel::SendPtr;
use primitives::F64;
use primitives::log2_strict_usize;
use primitives::stream::Stream;
use std::cell::RefCell;

/// Table of the normalized subspace polynomials at the basis.
///
/// - Row `i` holds `s_i(b_j)` for every basis element `b_j` with `j >= i`.
/// - Each row is scaled so that its first entry is one.
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
        let inv = row[0].invert_or_zero();
        for v in row.iter_mut() {
            *v *= inv;
        }
    }
    evals
}

/// `Σ_j bit_j(idx) · basis[j]`.
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

/// Receives a finished block of codeword rows, as `(first_row, rows)`.
pub(crate) type RowSink<'a> = dyn Fn(usize, &[F64]) + Sync + 'a;

/// Additive NTT over F_{2^64} with the standard polynomial-basis subspace
/// `{1, x, x², …}`: the F_2-subspace is `{0, 1, …, 2^ℓ−1}` under the natural
/// integer encoding, exactly as in the extension-field version (whose domain already
/// lived inside this very subfield).
#[derive(Clone, Debug)]
pub struct AdditiveNttF64 {
    evals: Vec<Vec<F64>>,
}

impl AdditiveNttF64 {
    fn new(basis: &[F64]) -> Self {
        Self {
            evals: generate_evals_from_subspace(basis),
        }
    }

    /// Standard NTT with basis `{1, x, …, x^(dim-1)}`. Requires `dim ≤ 63` so
    /// the evaluation domain (and the twiddles) stay inside F_{2^64} without
    /// wrap; far beyond any codeword size in use.
    pub fn standard(dim: usize) -> Self {
        assert!(dim <= 63, "standard NTT requires dim ≤ 63");
        let basis: Vec<F64> = (0..dim).map(|i| F64::new(1u64 << i)).collect();
        Self::new(&basis)
    }

    pub(crate) const fn log_domain_size(&self) -> usize {
        self.evals.len()
    }

    /// Twiddle of one block at one layer.
    ///
    /// - It is `s_i(sum_j bit_j(block) * b_(i+1+j))`, with `i = L - layer - 1` on a `2^L`-point domain.
    /// - The normalized `s_i` is F_2-linear, so this is a subset sum of row `i` of the table.
    pub(crate) fn twiddle(&self, layer: usize, block: usize) -> F64 {
        let v = &self.evals[self.log_domain_size() - layer - 1];
        span_get(&v[1..], block)
    }

    /// The seven twiddles a radix-8 group needs, breadth-first: layer `layer`,
    /// then `layer + 1` (one per half), then `layer + 2` (one per quarter).
    ///
    /// `span_get` is F_2-linear in the block index, so the six deeper twiddles are
    /// the block's own contribution plus a fixed correction per sub-block index:
    /// one scan of the three basis rows replaces seven.
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

    /// RS-encode a message already stored in the codeword's first replica.
    ///
    /// # Overview
    ///
    /// - The message fills the first `1 / 2^r` of the buffer, `r` the log inverse rate.
    /// - It is row-major: word `row * n + lane` for `n` interleaved lanes.
    /// - The buffer ends as `2^r` copies of it, each transformed from layer `r` on.
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
    pub fn encode_interleaved_in_place(&self, data: &mut [F64], num_ntts: usize, log_inv_rate: usize) {
        // The message is the buffer's own first replica.
        let msg = SendPtr(data.as_mut_ptr());
        self.transform(data, num_ntts, log_inv_rate, Some(msg), None);
    }

    /// Encode in place, handing `on_rows` every finished block of rows.
    ///
    /// - It is called as `on_rows(first_row, rows)`, from pool tasks.
    /// - Each row is handed over exactly once.
    /// - Blocks are aligned, and all of one power-of-two size.
    /// - A block is handed over while its rows are still in cache.
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

    /// RS-encode a message held in a buffer of its own, handing `on_rows` every row of the codeword and keeping none.
    ///
    /// - Replica `c` of the codeword is the message transformed from layer `r` on, under the twiddles of block `c`.
    /// - The rows go over in blocks as for the in-place encode, each once.
    /// - Nothing is written back to memory: a caller that needs a row again evaluates it with [`Self::rows_at`].
    ///
    /// # Plan
    ///
    /// ```text
    ///     replica fits L3 sub-block:  one task per run of replicas, each built in scratch from the message
    ///     larger replica:             one or more replicas a round, in one buffer reused by every round
    ///                                 gathered passes from the message, then deep sub-blocks in place
    /// ```
    ///
    /// # Panics
    ///
    /// Panics unless the message is a power-of-two number of rows.
    pub(crate) fn encode_rows_with(&self, msg: &[F64], num_ntts: usize, log_inv_rate: usize, on_rows: &RowSink<'_>) {
        assert!(num_ntts > 0);
        assert_eq!(msg.len() % num_ntts, 0);
        let log_rows = log2_strict_usize(msg.len() / num_ntts);
        let start = log_inv_rate;
        let log_d = log_rows + start;
        assert!(log_d <= self.log_domain_size());
        let fit = |words: usize| (words / num_ntts).max(1).ilog2() as usize;

        if log_rows <= fit(L3_WORDS) {
            // A task takes whole replicas, enough of them for `2^MIN_TASK_LOG` rows.
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
        // Its gathered pass reads each message row once for all of them.
        let log_batch = ((REPLICA_ROUND_WORDS / msg.len()).max(1).ilog2() as usize).min(start);
        // Deep sub-blocks fit L2, and a round cuts into several per worker, since each one ends in a barrier.
        // The layers above them run as gathered passes.
        let fit2 = fit(L2_WORDS);
        let log_tasks = (ROUND_SUBS_PER_WORKER * parallel::num_threads())
            .next_power_of_two()
            .ilog2() as usize;
        let log_sub = fit2
            .min((log_rows + log_batch).saturating_sub(log_tasks))
            .clamp(1, log_rows);
        let deep_start = log_d - log_sub;
        let mut round = Box::new_uninit_slice(msg.len() << log_batch);
        // SAFETY: every round writes each word, by its first gathered pass or a copy, before any pass reads it.
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
            // Sub-blocks as large as a replica leave no gathered layer: the round starts as copies of the message.
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

    /// The rows at `positions` of the codeword [`Self::encode_rows_with`] encodes `msg` into, from the message alone.
    ///
    /// - Each lane is a polynomial in the novel basis, its coefficients the lane's words in row order.
    /// - Basis polynomial `i` at a point is the product of the normalized subspace polynomials of the bits set in `i`.
    /// - Position `p` is the point whose bits are those of `p`, so each row is one evaluation per lane.
    ///
    /// # Algorithm
    ///
    /// An index splits into its low bits and the rest, `i = i_hi · 2^L + i_lo`:
    ///
    /// ```text
    ///     row(p) = Σ_hi  (Π_{k >= L, bit k of i} s_k(p))  ·  Σ_lo low_p[i_lo] · msg[i]
    ///                    \_______ one K scalar _______/
    /// ```
    ///
    /// - Each position's low table is built once, `2^L` words of K.
    /// - A task reads `2^L` message rows once for every position, its sums unreduced until each row is scaled.
    pub(crate) fn rows_at(&self, msg: &[F64], num_ntts: usize, positions: &[usize]) -> Vec<F64> {
        /// Low index bits tabulated per position: at most 2^10 words, 8 KiB of K a position.
        const LOW_BITS: usize = 10;
        /// Fewest low bits, so that a task reads whole runs of rows.
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
        //     low_p[0] = 1,   low_p[j + 2^k] = low_p[j] · s_k(p)   for j < 2^k
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
                let mut sums = vec![F64::ZERO; num_ntts];
                for ((s, table), out) in factors.iter().zip(&tables).zip(out.chunks_exact_mut(num_ntts)) {
                    dot_columns(table, rows, &mut sums);
                    let scale = (s[low..].iter().enumerate())
                        .filter(|&(k, _)| (hi >> k) & 1 == 1)
                        .fold(F64::ONE, |acc, (_, &s_k)| acc * s_k);
                    for (o, &sum) in out.iter_mut().zip(&sums) {
                        *o = sum * scale;
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
    ///     deep pass:      one task per contiguous sub-block, its layers run in place
    /// ```
    ///
    /// - When every layer fits one L3-sized sub-block, the deep pass is the whole transform: one sweep.
    /// - Otherwise gathered passes run until the rest fits one L2-sized sub-block.
    /// - With `n` words a row, a block of up to `(L2 words / n)^2` rows then costs two sweeps.
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
    /// - Each deep task's sub-blocks are final, and hand their rows to `on_rows` while they are in L2.
    /// - Without a split deep pass, the rows go over in parallel blocks at the end.
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

        // From 2^12 rows on, cut at least 2^LOG_SUBS_PER_WORKER deep sub-blocks per worker.
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

        // A deep task takes whole sub-blocks, enough of them for `2^MIN_TASK_LOG` rows.
        let log_sub = log_d - deep_start;
        let log_group = MIN_TASK_LOG.saturating_sub(log_sub).min(deep_start);

        // A lone task runs on this thread, so its rows go over in parallel afterwards.
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

    /// Run a range of layers in place over one sub-block of the domain.
    ///
    /// - The domain has `2^d` rows and splits into `2^o` equal sub-blocks.
    /// - The buffer is one of them; its index fixes the global block index, and so the twiddle, of each block.
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

            if layer + 2 < end_layer && block_size >= 8 {
                // Three layers to go and blocks of at least 8 rows: one radix-8 sweep.
                let eighth = block_size >> 3;
                for block_in_buf in 0..num_blocks_in_buf {
                    let t = self.twiddles_radix8(layer, global(block_in_buf));
                    let start = block_in_buf * block_elems;
                    butterfly_interleaved_fused_3layer(&mut buf[start..start + block_elems], &t, eighth, num_ntts);
                }
                layer += 3;
            } else if layer + 1 < end_layer && block_size >= 4 {
                // Two layers to go: one radix-4 sweep.
                let quarter = block_size >> 2;
                for block_in_buf in 0..num_blocks_in_buf {
                    let global_block = global(block_in_buf);
                    let t_outer = self.twiddle(layer, global_block);
                    let t_inner_a = self.twiddle(layer + 1, 2 * global_block);
                    let t_inner_b = self.twiddle(layer + 1, 2 * global_block + 1);
                    let start = block_in_buf * block_elems;
                    butterfly_interleaved_fused_2layer(
                        &mut buf[start..start + block_elems],
                        t_outer,
                        t_inner_a,
                        t_inner_b,
                        quarter,
                        num_ntts,
                    );
                }
                layer += 2;
            } else {
                // One layer: a plain butterfly sweep.
                let block_size_half = block_size >> 1;
                for block_in_buf in 0..num_blocks_in_buf {
                    let twiddle = self.twiddle(layer, global(block_in_buf));
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

    /// Recover novel-basis coefficients from evaluations with a scalar inverse NTT.
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

/// Column sums through upstream field multiplication.
fn dot_columns(table: &[F64], rows: &[F64], sums: &mut [F64]) {
    let width = sums.len();
    assert_eq!(rows.len(), table.len() * width);
    for (column, sum) in sums.iter_mut().enumerate() {
        *sum = table.iter().zip(rows[column..].iter().step_by(width))
            .fold(F64::ZERO, |sum, (&weight, &value)| sum + weight * value);
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
/// - A Merkle leaf reads its lanes from the top index down.
/// - So the absent all-zero lanes lead every leaf image.
/// - Their hash prefix is then one chaining value that every leaf shares.
/// - The proof can leave them out.
/// - Each lane is an independent codeword, so the order costs nothing.
///
/// # Performance
///
/// - Rows are handled one tile at a time.
/// - Each lane adds a contiguous burst of words to an L1-resident tile.
/// - The finished tile goes out as one contiguous run.
/// - That keeps an n-way gather at a `2^rows_log` stride near memory bandwidth.
pub(crate) fn transpose_lane_major(out: &mut [F64], msg: &[F64], n_lanes: usize, log_rows: usize) {
    let rows = 1usize << log_rows;
    assert!(n_lanes > 0, "a commitment needs at least one lane");
    assert_eq!(msg.len(), n_lanes * rows, "message is n_lanes contiguous lane blocks");
    assert_eq!(out.len(), msg.len(), "the transpose is the same words, reordered");

    /// Words per cache-resident row tile.
    const TILE_WORDS: usize = 4096;
    assert!(n_lanes <= TILE_WORDS, "a codeword row must fit the transpose tile");
    // Largest power-of-two row count whose tile fits: both it and `rows` are then
    // powers of two, so the tiles cover every row. They have to: this is the sole
    // initializer of an uninitialized codeword's message region, and a truncating
    // tile count would leave the tail reading the previous phase's plausible bytes,
    // whose symptom is a proof that stops verifying rather than a crash.
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
/// - It exceeds [`L3_WORDS`], which then changes no plan.
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
/// - One task each would hand the Merkle tree a few leaves at a time, short of a hash batch, which it hashes one by one.
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
/// - Each round ends in two barriers, and its gathered pass reads the whole message.
/// - Several replicas a round share both, which measured faster on aarch64.
/// - x86 keeps one replica a round, which stays in L3.
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

/// Lend this thread's scratch buffer, grown to the requested length.
///
/// - It is cache-line aligned, so a full-width load never splits a line.
/// - It lives as long as the thread, so no pass allocates in its hot loop.
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

#[inline]
fn butterfly_interleaved_block(block: &mut [F64], twiddle: F64, block_size_half: usize, num_ntts: usize) {
    let half_offset = block_size_half * num_ntts;
    let (top, bot) = block.split_at_mut(half_offset);
    for r in 0..block_size_half {
        let off = r * num_ntts;
        butterfly_lanes(&mut top[off..off + num_ntts], &mut bot[off..off + num_ntts], twiddle);
    }
}

/// Butterfly all `num_ntts` lanes of one (top row, bottom row) pair with a
/// shared twiddle: new_u = u + v*t; new_v = v + new_u.
#[inline]
fn butterfly_lanes(top: &mut [F64], bot: &mut [F64], twiddle: F64) {
    lane_butterflies::<false>(top, bot, twiddle);
}

/// The transposed butterfly on every lane of a row pair: s = u + v; new_u = s; new_v = v + s*t.
///
/// It is the inverse of the forward butterfly with the rows swapped.
#[inline]
pub(crate) fn transposed_butterfly_lanes(top: &mut [F64], bot: &mut [F64], twiddle: F64) {
    lane_butterflies::<true>(top, bot, twiddle);
}

/// Apply one butterfly per lane through the external field backend.
#[inline]
fn lane_butterflies<const TRANSPOSED: bool>(top: &mut [F64], bot: &mut [F64], twiddle: F64) {
    assert_eq!(top.len(), bot.len());
    if twiddle.is_zero() {
        for (u, v) in top.iter_mut().zip(bot) {
            if TRANSPOSED {
                *u += *v;
            } else {
                *v += *u;
            }
        }
        return;
    }
    type Packing = <F64 as Field>::Packing;
    let width = Packing::WIDTH;
    let t = Packing::from(twiddle);
    for start in (0..top.len()).step_by(width) {
        let pack = |row: &[F64]| Packing::from_fn(|i| row.get(start + i).copied().unwrap_or(F64::ZERO));
        let (u, v) = (pack(top), pack(bot));
        let (u, v) = if TRANSPOSED {
            let s = u + v;
            (s, v + s * t)
        } else {
            let s = u + v * t;
            (s, v + s)
        };
        let count = width.min(top.len() - start);
        top[start..start + count].copy_from_slice(&u.as_slice()[..count]);
        bot[start..start + count].copy_from_slice(&v.as_slice()[..count]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::PrimeCharacteristicRing;
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

    /// Check forward∘inverse = id and scalar == parallel.
    #[test]
    fn inverse_roundtrip_and_variants_agree() {
        let ntt = AdditiveNttF64::standard(12);
        let mut rng = Rng::new(1);
        for log_d in [1usize, 3, 6, 10] {
            let n = 1usize << log_d;
            let orig: Vec<F64> = (0..n).map(|_| F64::new(rng.next_u64())).collect();

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
            let original: Vec<F64> = (0..lanes << log_d).map(|_| F64::new(rng.next_u64())).collect();

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
            let msg: Vec<F64> = (0..msg_len).map(|_| F64::new(rng.next_u64())).collect();

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

    /// Every lane of the codeword must be exactly the single-lane RS codeword of
    /// that lane's contiguous message block, which is what makes a commitment over
    /// `n_lanes` lanes equal to the `2^log_batch_size`-lane one with a zero tail.
    /// The shapes cover the transposing fused first pass, its fallback, and lane
    /// counts that are not powers of two (the padding-free commit's whole point).
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
            let msg: Vec<F64> = (0..rows * n_lanes).map(|_| F64::new(rng.next_u64())).collect();

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
        let soa: Vec<F64> = (0..lanes << log_d).map(|_| F64::new(rng.next_u64())).collect();

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
            // SoA buffer + per-lane copies.
            let mut soa = vec![F64::ZERO; n * lanes];
            let mut per_lane: Vec<Vec<F64>> = vec![vec![F64::ZERO; n]; lanes];
            for pos in 0..n {
                for lane in 0..lanes {
                    let v = F64::new(rng.next_u64());
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
}
