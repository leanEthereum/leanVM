//! The grand product via GKR (§sec:gkr): given leaves `v_0…v_{2^μ-1}`, prove the
//! root `P = ∏ v_k` of the product tree, reducing the root to one leaf evaluation
//! `Ṽ_0(ζ)`. Two binary levels are contracted at a time: a radix-four layer has
//! relation `V_i(x)=∏_{a,b∈{0,1}}V_{i-2}(a,b,x)`. Its normalized eq-trick
//! sumcheck has degree four. An odd-depth tree starts with one binary layer.
//! Leaves and every layer are `E`-valued (the bus fingerprints mix `K`-columns
//! into `E` upstream, [`crate::leaf`]).

use crate::PAR_THRESHOLD;
use fiat_shamir::transcript::{Challenger, ProverState, Receiver, Transmitter, VerifierState};
use primitives::field::{F192, F192Unreduced, mul_unreduced4, mul2, mul4};
use primitives::multilinear::{eq_table, interp, poly_eval};
use primitives::stream::Stream;
use zk_alloc::ArenaVec;

/// Why the bus's grand-product GKR rejects.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum GkrError {
    /// The proof stream is malformed.
    #[error(transparent)]
    Transcript(#[from] fiat_shamir::transcript::Error),
    /// A layer's sumcheck does not end at the product of the next layer's claims.
    #[error("the GKR layer {layer} does not reduce to the next")]
    LayerMismatch { layer: usize },
}

/// Rows per parallel window: enough tasks to keep every thread fed, but not so few
/// rows per task that dispatch dominates.
fn window_rows(total: usize) -> usize {
    let tasks = parallel::num_threads() * 16;
    total.div_ceil(tasks).clamp(64, 1 << 10)
}

/// One run of explicit rows of a level: `len` rows from row `first`, stored from row
/// `at` of the level's buffer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Run {
    first: usize,
    len: usize,
    at: usize,
}

impl Run {
    const fn end(&self) -> usize {
        self.first + self.len
    }
}

/// A level of a product tree as rows of four entries, the children of the next
/// radix-four level's nodes: runs of explicit rows stored end to end, every other row
/// all-one.
///
/// The runs are in order, never touch, and start and end on even rows, so a pair of
/// rows, what a round of the layer folds, is in one run or all-one. An all-one pair adds
/// nothing to a round message (its quartic is the constant one, whose `q(0) + q(1)` is
/// zero) and folds to itself, so the prover's work is the runs': the identity leaves of
/// a table's padding rows (§sec:jagged) are never stored.
#[derive(Default)]
struct Rows {
    values: ArenaVec<F192>,
    runs: Vec<Run>,
}

impl Rows {
    /// Entry `i`.
    fn entry(&self, i: usize) -> F192 {
        let row = i / 4;
        let k = self.runs.partition_point(|r| r.end() <= row);
        match self.runs.get(k) {
            Some(r) if r.first <= row => self.values[4 * (r.at + row - r.first) + i % 4],
            _ => F192::ONE,
        }
    }
}

/// Lay entries `spans` (`(first, len)`, in order and disjoint) out in the runs of rows
/// holding them, each span widened to whole pairs of rows (eight entries) and merged
/// with the one before where they meet, every other entry of the runs one. Returns the
/// runs, their buffer, and each span's place in it.
///
/// # Safety
/// The spans' entries are left uninitialized.
unsafe fn lay_out(spans: &[(usize, usize)]) -> (Vec<Run>, ArenaVec<F192>, Vec<usize>) {
    let mut bounds: Vec<(usize, usize)> = Vec::new();
    for &(first, len) in spans.iter().filter(|s| s.1 > 0) {
        let (start, end) = (first & !7, (first + len).next_multiple_of(8));
        match bounds.last_mut() {
            Some((_, last)) if *last >= start => *last = end,
            _ => bounds.push((start, end)),
        }
    }
    let total = bounds.iter().map(|&(start, end)| end - start).sum();
    // SAFETY: the ones are written below, and the spans are the caller's.
    let mut values = unsafe { ArenaVec::<F192>::uninitialized(total) };
    let mut runs = Vec::with_capacity(bounds.len());
    let mut places = Vec::with_capacity(spans.len());
    let mut spans = spans.iter().peekable();
    let mut at = 0;
    for (start, end) in bounds {
        runs.push(Run {
            first: start / 4,
            len: (end - start) / 4,
            at: at / 4,
        });
        let mut cursor = start;
        while let Some(&&(first, len)) = spans.peek() {
            if len > 0 && first >= end {
                break;
            }
            if len > 0 {
                values[at + cursor - start..at + first - start].fill(F192::ONE);
                cursor = first + len;
            }
            places.push(at + first.saturating_sub(start));
            spans.next();
        }
        values[at + cursor - start..at + end - start].fill(F192::ONE);
        at += end - start;
    }
    places.extend(spans.map(|_| at));
    (runs, values, places)
}

/// One tree's leaves for [`prove_products`]: explicit on the spans the caller writes,
/// one everywhere else, `n` of them in all (the tree's depth is `⌈log2 n⌉`).
pub struct Leaves {
    rows: Rows,
    n: usize,
    /// Each span's place and length in the stored leaves.
    spans: Vec<(usize, usize)>,
}

impl Leaves {
    /// `n` leaves, explicit on `spans` (`(first, len)`, in order and disjoint) and one
    /// elsewhere.
    ///
    /// # Safety
    /// Every leaf of every span must be written ([`Self::spans_mut`]) before the leaves
    /// are read.
    pub unsafe fn new(n: usize, spans: &[(usize, usize)]) -> Self {
        assert!(n > 0, "a tree has a leaf");
        assert!(
            spans.windows(2).all(|s| s[0].0 + s[0].1 <= s[1].0)
                && spans.last().is_none_or(|&(first, len)| first + len <= n),
            "the spans are in order, disjoint, and in the tree"
        );
        // SAFETY: forwarded to the caller.
        let (runs, values, places) = unsafe { lay_out(spans) };
        Self {
            rows: Rows { values, runs },
            n,
            spans: places.into_iter().zip(spans.iter().map(|s| s.1)).collect(),
        }
    }

    /// Each span's leaves, in order, for the caller to write.
    pub fn spans_mut(&mut self) -> Vec<&mut [F192]> {
        let mut out: Vec<&mut [F192]> = Vec::with_capacity(self.spans.len());
        let mut rest: &mut [F192] = &mut self.rows.values;
        let mut base = 0;
        for &(at, len) in &self.spans {
            if len == 0 {
                out.push(&mut []);
                continue;
            }
            let (span, tail) = std::mem::take(&mut rest)[at - base..].split_at_mut(len);
            out.push(span);
            rest = tail;
            base = at + len;
        }
        out
    }
}

/// The levels the radix-four layers read, `0, 2, 4, …` up to the root's (or, at an odd
/// depth, its children's): `levels[i]` is level `2i`.
fn build_levels(leaves: Rows, mu: usize) -> Vec<Rows> {
    let mut levels = vec![leaves];
    for _ in 0..mu / 2 {
        let next = products(levels.last().expect("the leaves"));
        levels.push(next);
    }
    levels
}

/// The next radix-four level: each row's product, one entry of the level above.
fn products(below: &Rows) -> Rows {
    let spans: Vec<(usize, usize)> = below.runs.iter().map(|r| (r.first, r.len)).collect();
    // SAFETY: each run's products are written into its place below.
    let (runs, mut values, places) = unsafe { lay_out(&spans) };
    let total = below.values.len() / 4;
    let size = window_rows(total);
    // `(first row stored, rows, place)` per task.
    let tasks: Vec<(usize, usize, usize)> = (below.runs.iter().zip(&places))
        .flat_map(|(r, &place)| {
            (0..r.len)
                .step_by(size)
                .map(move |o| (r.at + o, size.min(r.len - o), place + o))
        })
        .collect();
    let dst = parallel::SendPtr(values.as_mut_ptr());
    let task = |index: usize| {
        let (row, n, place) = tasks[index];
        // SAFETY: the tasks' places are disjoint and inside `values`.
        let out = unsafe { dst.slice(place, n) };
        for (o, c) in out
            .iter_mut()
            .zip(below.values[4 * row..4 * (row + n)].as_chunks::<4>().0)
        {
            let [left, right] = mul2([c[0], c[2]], [c[1], c[3]]);
            *o = left * right;
        }
    };
    if total >= PAR_THRESHOLD {
        parallel::for_each(tasks.len(), task);
    } else {
        (0..tasks.len()).for_each(task);
    }
    Rows { values, runs }
}

/// `eq(r, x)` as two tables, `eq(r, x) = low[x mod 2^L] · high[x >> L]`.
///
/// The full table would be one E value per row pair of the layer, read every round and shrunk every round.
/// The low table is at most 2^12 entries, 96 KiB, which every task reads from L2.
struct SplitEq {
    /// `eq` of the low `L` variables.
    low: Vec<F192>,
    /// `eq` of the rest.
    high: Vec<F192>,
    /// `L`.
    low_log: usize,
}

impl SplitEq {
    /// Most low variables: 2^12 entries of E is 96 KiB.
    const MAX_LOW_LOG: usize = 12;

    fn new(r: &[F192]) -> Self {
        let low_log = r.len().min(Self::MAX_LOW_LOG);
        Self {
            low: eq_table(&r[..low_log]),
            high: eq_table(&r[low_log..]),
            low_log,
        }
    }

    /// `eq(r, x)`.
    #[cfg(test)]
    fn at(&self, x: usize) -> F192 {
        self.low[x & (self.low.len() - 1)] * self.high[x >> self.low_log]
    }

    /// `sum_x eq(r, x) · terms(x)` over a range of `x`.
    ///
    /// `terms(x, w)` returns its unreduced products already scaled by the low weight `w`.
    /// Each run of `x` sharing a high weight is reduced once and scaled by it once.
    fn weighted_sum(
        &self,
        range: std::ops::Range<usize>,
        mut terms: impl FnMut(usize, F192) -> [F192Unreduced; 4],
    ) -> [F192Unreduced; 4] {
        let mask = self.low.len() - 1;
        let mut total = [F192Unreduced::ZERO; 4];
        let mut x = range.start;
        while x < range.end {
            // The run of `x` in this high block.
            let high = x >> self.low_log;
            let run_end = ((high + 1) << self.low_log).min(range.end);
            let mut run = [F192Unreduced::ZERO; 4];
            for y in x..run_end {
                let t = terms(y, self.low[y & mask]);
                for (acc, t) in run.iter_mut().zip(t) {
                    *acc ^= t;
                }
            }
            let scaled = mul_unreduced4([self.high[high]; 4], run.map(F192Unreduced::reduce));
            for (acc, t) in total.iter_mut().zip(scaled) {
                *acc ^= t;
            }
            x = run_end;
        }
        total
    }
}

#[inline(always)]
fn quartic_summand(lines: [[F192; 2]; 4], equality: F192) -> [F192Unreduced; 4] {
    let [left0, left2, right0, right2] = mul4(
        [lines[0][0], lines[0][1], lines[2][0], lines[2][1]],
        [lines[1][0], lines[1][1], lines[3][0], lines[3][1]],
    );
    let [left_at_one, right_at_one, c0, c4] = mul4(
        [lines[0][0] + lines[0][1], lines[2][0] + lines[2][1], left0, left2],
        [lines[1][0] + lines[1][1], lines[3][0] + lines[3][1], right0, right2],
    );
    let left1 = left_at_one + left0 + left2;
    let right1 = right_at_one + right0 + right2;
    let [middle, at_one, cross_even, cross_high] = mul4(
        [left1, left0 + left1 + left2, left0 + left2, left1 + left2],
        [right1, right0 + right1 + right2, right0 + right2, right1 + right2],
    );
    let c2 = cross_even + c0 + c4 + middle;
    let c3 = cross_high + middle + c4;
    mul_unreduced4([equality; 4], [c0 + at_one, c2, c3, c4])
}

/// Coefficient-wise sum of two round messages.
fn xor4(mut left: [F192Unreduced; 4], right: [F192Unreduced; 4]) -> [F192Unreduced; 4] {
    for (l, r) in left.iter_mut().zip(right) {
        *l ^= r;
    }
    left
}

/// The runs a fold leaves: run `[f, f + n)`'s pairs fold to rows `[f/2, (f+n)/2)`,
/// widened to whole pairs (an all-one row each side at most) and merged where they
/// meet. They never overlap: runs `2` rows apart or more leave runs that at most meet.
fn folded(runs: &[Run]) -> Vec<Run> {
    let mut out: Vec<Run> = Vec::with_capacity(runs.len());
    let mut at = 0;
    for r in runs {
        let (first, end) = ((r.first / 2) & !1, (r.end() / 2).next_multiple_of(2));
        match out.last_mut() {
            Some(last) if last.end() == first => last.len += end - first,
            last => {
                debug_assert!(last.is_none_or(|last| last.end() < first), "folded runs never overlap");
                out.push(Run {
                    first,
                    len: end - first,
                    at,
                });
            }
        }
        at += end - first;
    }
    out
}

/// Two binary product levels contracted into one degree-four layer: the rows of the level
/// below, folded a pair of rows a round.
struct QuaternaryLayerState {
    /// Four child tables interleaved in their original order. This lets the
    /// prover consume a product-tree level without first transposing it.
    rows: Rows,
    /// Where a fold writes, then swapped with `rows.values`.
    next: ArenaVec<F192>,
    /// Rows in all, the all-one ones included.
    logical_rows: usize,
}

impl QuaternaryLayerState {
    fn new(rows: Rows, width: usize) -> Self {
        // A fold leaves at most the rows it reads, so the first one's size bounds every later one's.
        let stored = folded(&rows.runs).iter().map(|r| r.len).sum::<usize>();
        Self {
            rows,
            // SAFETY: a fold writes every row of the runs it leaves before anything reads
            // one, and nothing reads the rest.
            next: unsafe { ArenaVec::uninitialized(4 * stored) },
            logical_rows: width,
        }
    }

    /// `(q(0)+q(1), [X²]q, [X³]q, [X⁴]q)`.
    fn round_message(&self, equality: &SplitEq) -> [F192; 4] {
        let (runs, values) = (&self.rows.runs, &self.rows.values);
        let pairs = values.len() / 8;
        let size = window_rows(pairs);
        // `(run, pair range)` per window.
        let windows: Vec<(Run, usize, usize)> = (runs.iter())
            .flat_map(|&r| {
                (r.first / 2..r.end() / 2)
                    .step_by(size)
                    .map(move |p| (r, p, (p + size).min(r.end() / 2)))
            })
            .collect();
        let window = |index: usize| -> [F192Unreduced; 4] {
            let (r, from, to) = windows[index];
            equality.weighted_sum(from..to, |pair, weight| {
                let lo = 4 * (r.at + 2 * pair - r.first);
                let lines = [0, 1, 2, 3].map(|child| {
                    let at_zero = values[lo + child];
                    [at_zero, at_zero + values[lo + 4 + child]]
                });
                quartic_summand(lines, weight)
            })
        };
        let message = if pairs >= PAR_THRESHOLD {
            parallel::map_reduce(windows.len(), || [F192Unreduced::ZERO; 4], window, xor4)
        } else {
            (0..windows.len()).map(window).fold([F192Unreduced::ZERO; 4], xor4)
        };
        message.map(F192Unreduced::reduce)
    }

    /// Fold the rows at `challenge`, then, given the next round's eq, its message, from
    /// the folded pairs while they are staged. The last round of a layer has no next
    /// round, and its fold is one pair of rows.
    fn fold_and_message(&mut self, challenge: F192, equality: Option<&SplitEq>) -> [F192; 4] {
        /// Folded pairs a task stages.
        const PAIRS: usize = 16;
        let (old, values) = (&self.rows.runs, &self.rows.values);
        let runs = folded(old);
        let stored: usize = runs.iter().map(|r| r.len).sum();
        assert!(4 * stored <= self.next.len(), "a fold leaves at most the rows it reads");
        let dst = parallel::SendPtr(self.next.as_mut_ptr());
        // `(run, pair range)` of the folded rows per task.
        let tasks: Vec<(Run, usize, usize)> = (runs.iter())
            .flat_map(|&r| {
                (r.first / 2..r.end() / 2)
                    .step_by(PAIRS)
                    .map(move |q| (r, q, (q + PAIRS).min(r.end() / 2)))
            })
            .collect();
        let task = |index: usize| {
            let (run, q_from, q_to) = tasks[index];
            let (from, to) = (2 * q_from, 2 * q_to);
            let mut stage = [F192::ZERO; 8 * PAIRS];
            // Row `r` folds old rows `2r` and `2r + 1`: a pair of the old run `k`, or of
            // none, all-one.
            let mut k = old.partition_point(|o| o.end() / 2 <= from);
            let mut row = from;
            while row < to {
                row = match old.get(k) {
                    Some(o) if o.first / 2 <= row => {
                        let stop = to.min(o.end() / 2);
                        for r in row..stop {
                            // One slice, not eight indexes: the bounds checks and the
                            // index-by-24 multiplies fall out.
                            let v = &values[4 * (o.at + 2 * r - o.first)..][..8];
                            let folds = mul4(std::array::from_fn(|c| v[c] + v[4 + c]), [challenge; 4]);
                            for c in 0..4 {
                                stage[4 * (r - from) + c] = v[c] + folds[c];
                            }
                        }
                        if stop == o.end() / 2 {
                            k += 1;
                        }
                        stop
                    }
                    o => {
                        let stop = to.min(o.map_or(to, |o| o.first / 2));
                        stage[4 * (row - from)..4 * (stop - from)].fill(F192::ONE);
                        stop
                    }
                };
            }
            let message = equality.map_or([F192Unreduced::ZERO; 4], |equality| {
                equality.weighted_sum(q_from..q_to, |pair, weight| {
                    let lo = 8 * (pair - q_from);
                    let lines = std::array::from_fn(|c| [stage[lo + c], stage[lo + c] + stage[lo + 4 + c]]);
                    quartic_summand(lines, weight)
                })
            });
            // The next round reads the destination; this round reads only the local stage.
            let stream = Stream::new();
            let len = 4 * (to - from);
            // SAFETY: tasks write disjoint rows of the folded runs, all inside `next`.
            unsafe { stream.copy(dst.slice(4 * (run.at + from - run.first), len), &stage[..len]) };
            message
        };
        let message = if stored >= PAR_THRESHOLD {
            parallel::map_reduce(tasks.len(), || [F192Unreduced::ZERO; 4], task, xor4)
        } else {
            (0..tasks.len()).map(task).fold([F192Unreduced::ZERO; 4], xor4)
        };
        std::mem::swap(&mut self.rows.values, &mut self.next);
        self.rows.values.truncate(4 * stored);
        self.rows.runs = runs;
        self.logical_rows /= 2;
        message.map(F192Unreduced::reduce)
    }

    fn children(&self) -> [F192; 4] {
        debug_assert_eq!(self.logical_rows, 1);
        std::array::from_fn(|child| self.rows.entry(child))
    }
}

/// The result of a batched grand-product proof: the roots and leaf evaluations, all
/// reduced to one shared point. `roots[0] == roots[1]` by construction rather than by
/// a check.
pub struct Products<const N: usize> {
    pub roots: [F192; N],
    pub point: Vec<F192>,
    pub values: [F192; N],
}

/// `Σ_k λ^k·values[k]`, the batch's combination of one coefficient across the trees.
fn combine<const N: usize>(values: [F192; N], lambda: F192) -> F192 {
    values.iter().rev().fold(F192::ZERO, |acc, &v| acc * lambda + v)
}

/// Prove `N` identity-padded grand products as one RLC-batched radix-four GKR, over the
/// depth of the tallest tree.
///
/// The first two trees share a product by construction, as the bus's two sides do
/// (every row they flush is a row the run made, a padding row flushing the identity, so
/// they balance outright). ONE root is sent for both, and no verifier can be handed an
/// unbalanced pair to check.
pub fn prove_products<const N: usize>(leaves: [Leaves; N], ps: &mut ProverState) -> Products<N> {
    const { assert!(N >= 2, "the first two trees are the bus's two sides") };
    let mu = leaves
        .iter()
        .map(|lane| crate::log2_ceil_usize(lane.n))
        .max()
        .expect("at least one tree");
    let mut levels = leaves.map(|lane| build_levels(lane.rows, mu));
    // The root, or at an odd depth its two children's product.
    let roots: [F192; N] = std::array::from_fn(|tree| {
        let top = levels[tree].last().expect("the leaves");
        if mu % 2 == 0 {
            top.entry(0)
        } else {
            top.entry(0) * top.entry(1)
        }
    });
    assert_eq!(roots[0], roots[1], "the bus needs the two products to agree");
    ps.add_scalars(&roots[1..]);
    let mut lambda = ps.sample();
    let mut point = Vec::new();
    let mut values = roots;

    let mut layer = mu;
    while layer > 0 {
        let round_count = mu - layer;
        if layer % 2 == 1 {
            debug_assert_eq!(round_count, 0, "only the root-most layer may be binary");
            let tails: [[F192; 2]; N] = std::array::from_fn(|tree| {
                let below = &levels[tree][(layer - 1) / 2];
                [below.entry(0), below.entry(1)]
            });
            for tail in &tails {
                ps.add_scalars(tail);
            }
            let challenge = ps.sample();
            for (value, [left, right]) in values.iter_mut().zip(tails) {
                *value = interp(left, right, challenge);
            }
            lambda = ps.sample();
            point = vec![challenge];
            layer -= 1;
            continue;
        }

        let width = 1usize << round_count;
        let mut trees: [QuaternaryLayerState; N] = std::array::from_fn(|tree| {
            QuaternaryLayerState::new(std::mem::take(&mut levels[tree][(layer - 2) / 2]), width)
        });
        // Round `j` of this layer weighs its rows by `eq(point[1 + j..], .)`.
        let mut equality = SplitEq::new(if round_count > 0 { &point[1..] } else { &[] });
        let mut round_point = Vec::with_capacity(round_count);
        let mut messages = if round_count > 0 {
            trees.each_ref().map(|tree| tree.round_message(&equality))
        } else {
            [[F192::ZERO; 4]; N]
        };
        for round in 0..round_count {
            let mut coeffs = [0, 1, 2, 3].map(|coefficient| combine(messages.map(|m| m[coefficient]), lambda));
            // The kernel accumulates `q(0) + q(1)`, the wire carries `c1`. This is
            // `Transmitter::add_round_poly(_, true)` bar its dropped `c0`, which the
            // claim fixes and the prover therefore never forms.
            coeffs[0] = coeffs[0] + coeffs[1] + coeffs[2] + coeffs[3];
            ps.add_scalars(&coeffs);
            let challenge = ps.sample();
            round_point.push(challenge);
            if round + 1 < round_count {
                equality = SplitEq::new(&point[2 + round..]);
                messages = trees
                    .each_mut()
                    .map(|tree| tree.fold_and_message(challenge, Some(&equality)));
            } else {
                // No variable is left to weigh a message by: the final round folds alone.
                for tree in &mut trees {
                    tree.fold_and_message(challenge, None);
                }
            }
        }

        for tree in &trees {
            ps.add_scalars(&tree.children());
        }
        let low_challenge = ps.sample();
        let high_challenge = ps.sample();
        for (value, tree) in values.iter_mut().zip(&trees) {
            let tail = tree.children();
            *value = interp(
                interp(tail[0], tail[1], low_challenge),
                interp(tail[2], tail[3], low_challenge),
                high_challenge,
            );
        }
        lambda = ps.sample();
        point = vec![low_challenge, high_challenge];
        point.extend_from_slice(&round_point);
        layer -= 2;
    }

    Products { roots, point, values }
}

/// Verify the RLC-batched radix-four proof of `N` trees of depth `mu`.
pub fn verify_products<const N: usize>(mu: usize, vs: &mut VerifierState) -> Result<Products<N>, GkrError> {
    const { assert!(N >= 2, "the first two trees are the bus's two sides") };
    // One root for both balancing trees, so their equality is structural: there is no
    // unbalanced pair a prover could state, and nothing for the caller to check.
    let mut roots = [F192::ZERO; N];
    for root in &mut roots[1..] {
        *root = vs.next_scalar()?;
    }
    roots[0] = roots[1];
    let mut lambda = vs.sample();
    let mut point = Vec::new();
    let mut values = roots;

    let mut layer = mu;
    while layer > 0 {
        let round_count = mu - layer;
        let mut claim = poly_eval(&values, lambda);
        if layer % 2 == 1 {
            debug_assert_eq!(round_count, 0, "only the root-most layer may be binary");
            let mut tails = [[F192::ZERO; 2]; N];
            for value in tails.iter_mut().flatten() {
                *value = vs.next_scalar()?;
            }
            let products = tails.map(|[left, right]| left * right);
            if claim != poly_eval(&products, lambda) {
                return Err(GkrError::LayerMismatch { layer });
            }
            let challenge = vs.sample();
            for (value, [left, right]) in values.iter_mut().zip(tails) {
                *value = interp(left, right, challenge);
            }
            lambda = vs.sample();
            point = vec![challenge];
            layer -= 1;
            continue;
        }

        let mut round_point = Vec::with_capacity(round_count);
        for &equality_point in point.iter().take(round_count) {
            let h = vs.next_round_poly(5, claim, Some(equality_point))?;
            let challenge = vs.sample();
            round_point.push(challenge);
            claim = poly_eval(&h, challenge);
        }
        let mut tails = [[F192::ZERO; 4]; N];
        for value in tails.iter_mut().flatten() {
            *value = vs.next_scalar()?;
        }
        let products = tails.map(|tail| tail[0] * tail[1] * tail[2] * tail[3]);
        if claim != poly_eval(&products, lambda) {
            return Err(GkrError::LayerMismatch { layer });
        }
        let low_challenge = vs.sample();
        let high_challenge = vs.sample();
        for (value, tail) in values.iter_mut().zip(tails) {
            *value = interp(
                interp(tail[0], tail[1], low_challenge),
                interp(tail[2], tail[3], low_challenge),
                high_challenge,
            );
        }
        lambda = vs.sample();
        point = vec![low_challenge, high_challenge];
        point.extend_from_slice(&round_point);
        layer -= 2;
    }

    Ok(Products { roots, point, values })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mle_eval_e(table: &[F192], point: &[F192]) -> F192 {
        assert_eq!(table.len(), 1 << point.len());
        let mut folded = table.to_vec();
        for &challenge in point {
            let half = folded.len() / 2;
            for row in 0..half {
                folded[row] = interp(folded[2 * row], folded[2 * row + 1], challenge);
            }
            folded.truncate(half);
        }
        folded[0]
    }

    /// Leaves explicit on `spans` (`(first, values)`, in order) and one elsewhere, `n` in all.
    fn leaves(n: usize, spans: &[(usize, &[F192])]) -> Leaves {
        let bounds: Vec<(usize, usize)> = spans.iter().map(|&(first, values)| (first, values.len())).collect();
        // SAFETY: every span is written below.
        let mut leaves = unsafe { Leaves::new(n, &bounds) };
        for (dst, &(_, values)) in leaves.spans_mut().into_iter().zip(spans) {
            dst.copy_from_slice(values);
        }
        leaves
    }

    #[test]
    fn split_eq_is_the_eq_table() {
        // Invariant: the two tables weigh every row as the full eq table, and a weighted sum
        // over a range equals the dense one, whether it crosses a high block or not.
        //
        // Fixture state: 14 variables, so the high table has 4 entries of 2^12 rows each.
        let r: Vec<F192> = (0..14u64).map(|i| F192::new(3 * i + 1, i + 7, 5 * i + 2)).collect();
        let (split, dense) = (SplitEq::new(&r), eq_table(&r));
        for x in [0, 1, 4095, 4096, 4097, 12_345, (1 << 14) - 1] {
            assert_eq!(split.at(x), dense[x], "x={x}");
        }

        // Terms of one coefficient: x itself, as a field element, scaled by the weight.
        let terms = |x: usize, w: F192| {
            let mut t = [F192Unreduced::ZERO; 4];
            t[0] = w.mul_unreduced(F192::new(x as u64, 1, 0));
            t
        };
        for range in [0..10, 4090..4100, 100..9000, 0..1 << 14] {
            let want = range
                .clone()
                .fold(F192::ZERO, |sum, x| sum + dense[x] * F192::new(x as u64, 1, 0));
            assert_eq!(split.weighted_sum(range.clone(), terms)[0].reduce(), want, "{range:?}");
        }
    }

    #[test]
    fn quartic_round_message_matches_direct_evaluation() {
        for width in [2, 4, 8, 16] {
            let below: Vec<F192> = (0..4 * width)
                .map(|i| F192::new((17 * i + width + 1) as u64, (i * i + 3) as u64, (5 * i + 7) as u64))
                .collect();
            let state = QuaternaryLayerState::new(leaves(below.len(), &[(0, &below)]).rows, width);
            // Rows weighed by eq at a point of one variable per pair index bit.
            let r: Vec<F192> = (0..(width / 2).ilog2())
                .map(|i| F192::new(u64::from(31 * i + 5), u64::from(7 * i + 1), u64::from(11 * i + 9)))
                .collect();
            let equality = SplitEq::new(&r);
            let [difference, c2, c3, c4] = state.round_message(&equality);
            let direct = |point: F192| {
                (0..width / 2).fold(F192::ZERO, |sum, row| {
                    let values =
                        [0, 1, 2, 3].map(|child| interp(below[8 * row + child], below[8 * row + 4 + child], point));
                    sum + equality.at(row) * values[0] * values[1] * values[2] * values[3]
                })
            };
            let c0 = direct(F192::ZERO);
            let c1 = difference + c2 + c3 + c4;
            for point in [F192::ZERO, F192::ONE, F192::Y, F192::Y.square()] {
                assert_eq!(
                    c0 + point * (c1 + point * (c2 + point * (c3 + point * c4))),
                    direct(point)
                );
            }
        }
    }

    #[test]
    fn fused_fold_matches_separate_fold_and_message() {
        for width in [4usize, 16, 1 << 14] {
            for len in [1, 4, 5, 7, 8, 9, 31, 32, 33, 4 * width - 5, 4 * width - 1, 4 * width] {
                if len > 4 * width {
                    continue;
                }
                let values: Vec<F192> = (0..len)
                    .map(|i| F192::new((17 * i + 1) as u64, (i * i + 3) as u64, (5 * i + 7) as u64))
                    .collect();
                let mut reference = QuaternaryLayerState::new(leaves(len, &[(0, &values)]).rows, width);
                let mut fused = QuaternaryLayerState::new(leaves(len, &[(0, &values)]).rows, width);
                let point: Vec<F192> = (0..width.ilog2() - 1)
                    .map(|i| F192::new(31 + u64::from(i), 7, 11))
                    .collect();
                // Round `k` weighs by eq of the point less its first `k` variables.
                let mut bound = 0;
                while reference.logical_rows > 2 {
                    let challenge = F192::new(reference.logical_rows as u64, 13, 19);
                    reference.fold_and_message(challenge, None);
                    bound += 1;
                    let equality = SplitEq::new(&point[bound..]);
                    let message = fused.fold_and_message(challenge, Some(&equality));
                    assert_eq!(message, reference.round_message(&equality), "width={width}, len={len}");
                    assert_eq!(&*fused.rows.values, &*reference.rows.values, "width={width}, len={len}");
                }
                reference.fold_and_message(F192::Y, None);
                fused.fold_and_message(F192::Y, None);
                assert_eq!(fused.children(), reference.children());
            }
        }
    }

    #[test]
    fn radix_four_roundtrip_at_even_and_odd_depths() {
        for mu in 0..=10 {
            let mut leaves: [Vec<F192>; 3] = [0, 1, 2].map(|lane| {
                (0..1usize << mu)
                    .map(|row| F192::new((1 + row + lane * 100_003) as u64, row as u64, lane as u64))
                    .collect()
            });
            // The first two trees share their product.
            leaves[1] = leaves[0].iter().rev().copied().collect();
            let expected_roots = leaves
                .each_ref()
                .map(|lane| lane.iter().copied().fold(F192::ONE, |product, value| product * value));
            let mut ps = ProverState::from_label(b"radix-four-gkr-test");
            let proved = prove_products(leaves.each_ref().map(|l| self::leaves(l.len(), &[(0, l)])), &mut ps);
            assert_eq!(proved.roots, expected_roots);
            for (lane, leaf) in leaves.iter().enumerate() {
                assert_eq!(proved.values[lane], mle_eval_e(leaf, &proved.point));
            }

            let proof = ps.into_proof();
            let mut vs = VerifierState::from_label(b"radix-four-gkr-test", &proof);
            let verified = verify_products(mu, &mut vs).expect("GKR verifies");
            assert_eq!(verified.roots, proved.roots);
            assert_eq!(verified.point, proved.point);
            assert_eq!(verified.values, proved.values);
            vs.finish().expect("proof stream is consumed");
        }
    }

    /// Leaves explicit on runs with gaps of every size, the rest one, prove as the same
    /// leaves written out: the transcript, the roots and the leaf values agree.
    #[test]
    fn identity_runs_match_dense_padding() {
        let mut seed = 0x9E37_79B9_7F4A_7C15_u64;
        let mut rand = move |bound: usize| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            (seed % bound as u64) as usize
        };
        // Up to depths whose kernels dispatch in parallel.
        for mu in (3..=12).chain([15, 16]) {
            let n = 1usize << mu;
            let leaf = |i: usize, lane: usize| F192::new((3 + i + lane * 10_007) as u64, i as u64, lane as u64 + 1);
            // Tree 0: spans from 0 or 1 on, separated by gaps from none to an eighth of the tree, some empty.
            let mut spans: Vec<(usize, Vec<F192>)> = Vec::new();
            let mut at = rand(2);
            while at < n {
                let len = [0, 1, 3, 7, 8, 9, 64].map(|l| l.min(n - at))[rand(7)];
                let len = if rand(4) == 0 { len } else { rand(n / 8 + 2).min(n - at) };
                spans.push((at, (at..at + len).map(|i| leaf(i, 0)).collect()));
                at += len + [0, 1, 2, 5, 8, 13, n / 8][rand(7)];
            }
            // Tree 1: tree 0's leaves at its start, so the two share their product; tree 2:
            // a prefix of an odd length.
            let packed: Vec<F192> = spans.iter().flat_map(|(_, v)| v.iter().copied()).collect();
            let prefix: Vec<F192> = (0..n / 2 + 3).map(|i| leaf(i, 2)).collect();
            let dense = |spans: &[(usize, &[F192])]| {
                let mut out = vec![F192::ONE; n];
                for &(first, values) in spans {
                    out[first..first + values.len()].copy_from_slice(values);
                }
                out
            };
            let lanes: [Vec<(usize, &[F192])>; 3] = [
                spans.iter().map(|(first, v)| (*first, &v[..])).collect(),
                vec![(0, &packed[..])],
                vec![(0, &prefix[..])],
            ];
            let dense: [Vec<F192>; 3] = lanes.each_ref().map(|spans| dense(spans));

            let mut sparse_ps = ProverState::from_label(b"sparse-radix-four-gkr-test");
            let proved = prove_products(lanes.each_ref().map(|spans| leaves(n, spans)), &mut sparse_ps);
            for (lane, values) in dense.iter().enumerate() {
                assert_eq!(proved.values[lane], mle_eval_e(values, &proved.point), "mu={mu}");
                assert_eq!(
                    proved.roots[lane],
                    values.iter().fold(F192::ONE, |p, &v| p * v),
                    "mu={mu}"
                );
            }
            let proof = sparse_ps.into_proof();
            let mut dense_ps = ProverState::from_label(b"sparse-radix-four-gkr-test");
            let dense_proved = prove_products(dense.each_ref().map(|l| leaves(n, &[(0, l)])), &mut dense_ps);
            assert_eq!(dense_proved.point, proved.point, "mu={mu}");
            assert_eq!(dense_ps.into_proof().stream, proof.stream, "mu={mu}");
            let mut vs = VerifierState::from_label(b"sparse-radix-four-gkr-test", &proof);
            let verified = verify_products(mu, &mut vs).expect("GKR verifies");
            assert_eq!(verified.values, proved.values);
            vs.finish().expect("proof stream is consumed");
        }
    }
}
