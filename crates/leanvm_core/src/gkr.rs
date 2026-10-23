//! The grand product via GKR (§sec:gkr): given leaves `v_0…v_{2^μ-1}`, prove the
//! root `P = ∏ v_k` of the product tree, reducing the root to one leaf evaluation
//! `Ṽ_0(ζ)`. Two binary levels are contracted at a time: a radix-four layer has
//! relation `V_i(x)=∏_{a,b∈{0,1}}V_{i-2}(a,b,x)`. Its normalized eq-trick
//! sumcheck has degree four. An odd-depth tree starts with one binary layer.
//! Leaves and every layer are `E`-valued (the bus fingerprints mix `K`-columns
//! into `E` upstream, [`crate::leaf`]).
//!
//! On AVX-512 the large rounds run eight pairs of rows at a time in transposed form
//! (`vertical`), and skip the runs of rows known to be the identity.

use std::ops::Range;

use crate::PAR_THRESHOLD;
use crate::transcript::ProverState;
use primitives::field::{F192, F192Unreduced, mul_unreduced4, mul2, mul4};
use primitives::multilinear::{eq_table, interp};
use primitives::stream::Stream;

/// Rows per parallel window: enough tasks to keep every thread fed, but not so few
/// rows per task that dispatch dominates.
fn window_rows(total: usize) -> usize {
    let tasks = parallel::num_threads() * 16;
    total.div_ceil(tasks).clamp(64, 1 << 10)
}

fn add4(a: [F192; 4], b: [F192; 4]) -> [F192; 4] {
    std::array::from_fn(|i| a[i] + b[i])
}

/// `Σ_t f(t)` over `0..tasks`, in parallel when asked.
fn sum_tasks(tasks: usize, parallel: bool, f: impl Fn(usize) -> [F192; 4] + Sync) -> [F192; 4] {
    if parallel {
        parallel::map_reduce(tasks, || [F192::ZERO; 4], f, add4)
    } else {
        (0..tasks).map(f).fold([F192::ZERO; 4], add4)
    }
}

/// `out[i] = ∏ current[4i..4i+4]`, for `out.len() == current.len() / 4`.
pub(crate) fn products_into(current: &[F192], out: &mut [F192]) {
    debug_assert_eq!(out.len(), current.len() / 4);
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
    let done = vertical::products_into(current, out);
    #[cfg(not(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq")))]
    let done = 0;
    for (row, slot) in out.iter_mut().enumerate().skip(done) {
        let [left, right] = mul2(
            [current[4 * row], current[4 * row + 2]],
            [current[4 * row + 1], current[4 * row + 3]],
        );
        *slot = left * right;
    }
}

/// The level above `current`: the product of each four-tuple, an incomplete last one
/// padded with the identity.
fn next_level(current: &[F192]) -> Vec<F192> {
    /// Rows per task, staged before they are published.
    const ROWS: usize = 1 << 9;
    let full_rows = current.len() / 4;
    // SAFETY: the products below write `next[..full_rows]`, and the tail its last slot.
    let mut next: Vec<F192> = unsafe { primitives::uninit_vec(current.len().div_ceil(4)) };
    if full_rows >= PAR_THRESHOLD {
        // The next level and the GKR read the output long after this pass evicts it.
        parallel::chunks_mut(&mut next[..full_rows], ROWS, |task, destination| {
            let mut stage = [F192::ZERO; ROWS];
            let stage = &mut stage[..destination.len()];
            let start = 4 * ROWS * task;
            products_into(&current[start..start + 4 * stage.len()], stage);
            Stream::new().copy(destination, stage);
        });
    } else {
        products_into(&current[..4 * full_rows], &mut next[..full_rows]);
    }
    let tail = &current[4 * full_rows..];
    if !tail.is_empty() {
        let child = |index| tail.get(index).copied().unwrap_or(F192::ONE);
        let [left, right] = mul2([child(0), child(2)], [child(1), child(3)]);
        next[full_rows] = left * right;
    }
    next
}

/// A tree's leaves, with the two levels above them, which the leaf builder forms while
/// the leaves are in cache, and its runs of identity leaves.
pub struct Leaves {
    pub values: Vec<F192>,
    /// `fours[i] = ∏ values[4i..4i+4]`, and `sixteens` likewise over `fours`, an
    /// incomplete last four-tuple padded with the identity.
    pub fours: Vec<F192>,
    pub sixteens: Vec<F192>,
    /// Runs of identity leaves among `values`, sorted, which the GKR rounds above them
    /// need neither read nor write.
    pub ones: Vec<Range<usize>>,
}

impl Leaves {
    pub fn new(values: Vec<F192>) -> Self {
        let fours = next_level(&values);
        let sixteens = next_level(&fours);
        Self {
            values,
            fours,
            sixteens,
            ones: Vec::new(),
        }
    }
}

/// Build only the levels consumed by radix four: `0,2,4,…`, plus a final
/// binary root when the logical depth is odd.
fn build_layers(leaves: Leaves, mu: usize) -> Vec<Vec<F192>> {
    // At mu = 22 the leaf level alone is hundreds of megabytes, and every level
    // dies with the proof.
    let mut layers: Vec<Vec<F192>> = (0..=mu).map(|_| Vec::new()).collect();
    layers[0] = leaves.values;
    let mut level = 0;
    for (given, below) in [(2, leaves.fours), (4, leaves.sixteens)] {
        if given <= mu {
            layers[given] = below;
            level = given;
        }
    }
    while level + 2 <= mu {
        let next = next_level(&layers[level]);
        level += 2;
        layers[level] = next;
    }
    if level < mu {
        layers[mu] = match layers[level].as_slice() {
            [root] => Vec::from_iter([*root]),
            [left, right] => Vec::from_iter([*left * *right]),
            _ => unreachable!("the final binary layer has at most two explicit nodes"),
        };
    }
    layers
}

/// `eq(vars, ·)` as the tensor product of a table over its low `lo_bits` variables
/// and one over the rest. A sum against it weights each term by the low factor and
/// each block of `2^lo_bits` terms by the high one, so the full table is never built,
/// nor marginalized round after round.
struct SplitEq {
    lo: Vec<F192>,
    hi: Vec<F192>,
    lo_bits: usize,
    /// `lo` eight entries at a time, for the vertical kernels.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
    lo8: Vec<primitives::field::x8::F192x8>,
}

impl SplitEq {
    fn new(vars: &[F192]) -> Self {
        let lo_bits = vars.len().div_ceil(2).max(vars.len().min(3));
        let (low, high) = vars.split_at(lo_bits);
        let lo = eq_table(low);
        Self {
            #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
            lo8: lo
                .as_chunks::<8>()
                .0
                .iter()
                .map(primitives::field::x8::F192x8::load)
                .collect(),
            lo,
            hi: eq_table(high),
            lo_bits,
        }
    }

    /// `Σ_{p ∈ range} eq(p)·f(p)`, where `term(p, w)` is `f(p)` already weighted by `w`,
    /// the low factor of `eq(p)`.
    #[inline]
    fn sum(&self, range: Range<usize>, term: impl Fn(usize, F192) -> [F192Unreduced; 4]) -> [F192; 4] {
        let mask = (1usize << self.lo_bits) - 1;
        let mut total = [F192::ZERO; 4];
        let mut start = range.start;
        while start < range.end {
            let block = start >> self.lo_bits;
            let end = range.end.min((block + 1) << self.lo_bits);
            let block_sum = (start..end).fold([F192Unreduced::ZERO; 4], |mut acc, p| {
                let t = term(p, self.lo[p & mask]);
                for i in 0..4 {
                    acc[i] ^= t[i];
                }
                acc
            });
            total = add4(total, mul4([self.hi[block]; 4], block_sum.map(F192Unreduced::reduce)));
            start = end;
        }
        total
    }
}

/// The `eq`-weighted message terms of one pair, from each child's line `[value at 0, slope]`.
/// The weight scales child 0's line, and with it every product: two products rather than four.
#[inline(always)]
fn quartic_summand(lines: [[F192; 2]; 4], equality: F192) -> [F192Unreduced; 4] {
    let [[g0, s0], [g1, s1], [g2, s2], [g3, s3]] = lines;
    let [a0, d0, right0, right2] = mul4([equality, equality, g2, s2], [g0, s0, g3, s3]);
    let [left0, left2, left_at_one, right_at_one] = mul4([a0, d0, a0 + d0, g2 + s2], [g1, s1, g1 + s1, g3 + s3]);
    let left1 = left_at_one + left0 + left2;
    let right1 = right_at_one + right0 + right2;
    let [c0, c4, middle, at_one] = mul_unreduced4(
        [left0, left2, left1, left_at_one],
        [right0, right2, right1, right_at_one],
    );
    let cross_even = (left0 + left2).mul_unreduced(right0 + right2);
    let cross_high = (left1 + left2).mul_unreduced(right1 + right2);
    [c0 ^ at_one, cross_even ^ c0 ^ c4 ^ middle, cross_high ^ middle ^ c4, c4]
}

/// The rows of a level `shift` binary levels up whose children are all in `ones`.
fn coarsen(ones: &[Range<usize>], shift: usize) -> Vec<Range<usize>> {
    ones.iter()
        .map(|r| r.start.div_ceil(1 << shift)..r.end >> shift)
        .filter(|r| !r.is_empty())
        .collect()
}

/// Whether `ones` covers `rows`.
fn covered(ones: &[Range<usize>], rows: Range<usize>) -> bool {
    let i = ones.partition_point(|r| r.start <= rows.start);
    i > 0 && ones[i - 1].end >= rows.end
}

/// `range` split at the edges of `ones` into maximal runs, each tagged with whether
/// `ones` covers it.
fn runs<'a>(range: Range<usize>, ones: &'a [Range<usize>]) -> impl Iterator<Item = (Range<usize>, bool)> + 'a {
    let first = ones.partition_point(|r| r.end <= range.start);
    let mut ones = ones[first..].iter().peekable();
    let mut at = range.start;
    std::iter::from_fn(move || {
        if at >= range.end {
            return None;
        }
        let run = match ones.peek() {
            Some(r) if r.start <= at => {
                let end = r.end.min(range.end);
                ones.next();
                (at..end, true)
            }
            Some(r) => (at..r.start.min(range.end), false),
            None => (at..range.end, false),
        };
        at = run.0.end;
        Some(run)
    })
}

/// Whether the scalar kernels, and the leaf builder's products, skip the rows known to
/// be the identity: they contribute nothing to a round message and fold to the
/// identity. Not yet measured on aarch64, so it keeps computing them.
pub(crate) const SKIP_IDENTITY: bool = cfg!(target_arch = "x86_64");

/// Below this logical height a layer runs the scalar kernels.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
const VERTICAL_ROWS: usize = 1 << 10;

/// Two binary product levels contracted into one degree-four layer.
struct QuaternaryLayerState {
    /// Four child tables interleaved in their original order. This lets the
    /// prover consume a product-tree level without first transposing it.
    values: Vec<F192>,
    /// Logical row count after identity padding. `values` stores an arbitrary
    /// prefix; every omitted row is the constant four-tuple one.
    logical_rows: usize,
    /// Once folded by the vertical kernels, the rows live here instead of in `values`.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
    groups: Vec<vertical::Group>,
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
    spare: Vec<vertical::Group>,
    /// Runs of rows known to be the identity, sorted: the kernels skip them, and
    /// the vertical ones leave their groups unwritten.
    ones: Vec<Range<usize>>,
}

impl QuaternaryLayerState {
    fn new(mut values: Vec<F192>, width: usize) -> Self {
        // Materialize only the incomplete final four-tuple. Every complete
        // all-one row after the arbitrary explicit prefix remains implicit.
        values.resize(4 * values.len().max(1).div_ceil(4), F192::ONE);
        debug_assert_eq!(values.len() % 4, 0);
        debug_assert!(values.len() <= 4 * width);
        Self {
            values,
            logical_rows: width,
            #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
            groups: Vec::new(),
            #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
            spare: Vec::new(),
            ones: Vec::new(),
        }
    }

    /// `(q(0)+q(1), [X²]q, [X³]q, [X⁴]q)`.
    fn round_message(&self, eq: &SplitEq) -> [F192; 4] {
        #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
        if self.logical_rows >= VERTICAL_ROWS {
            return vertical::message(&self.values, &self.ones, eq);
        }
        self.round_message_scalar(eq)
    }

    fn fold(&mut self, challenge: F192) {
        #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
        self.leave_groups();
        self.fold_scalar(challenge);
    }

    /// The vertical kernels' view of the rows, and the buffer the fold writes.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
    fn split(&mut self) -> (vertical::Input<'_>, &mut Vec<vertical::Group>) {
        let data = if self.groups.is_empty() {
            vertical::Data::Rows(&self.values)
        } else {
            vertical::Data::Groups(&self.groups)
        };
        (vertical::Input { data, ones: &self.ones }, &mut self.spare)
    }

    /// Move the rows back into `values` for the scalar kernels.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
    fn leave_groups(&mut self) {
        if !self.groups.is_empty() {
            self.values = vertical::to_rows(&self.groups, &self.ones);
            self.groups = Vec::new();
            self.spare = Vec::new();
        }
    }

    fn round_message_scalar(&self, eq: &SplitEq) -> [F192; 4] {
        let stored_rows = self.values.len() / 4;
        let full_pairs = stored_rows / 2;
        let summand = |pair: usize, weight: F192| -> [F192Unreduced; 4] {
            let (lo, hi) = (8 * pair, 8 * pair + 4);
            let lines = [0, 1, 2, 3].map(|child| {
                let at_zero = self.values[lo + child];
                [at_zero, at_zero + self.values[hi + child]]
            });
            quartic_summand(lines, weight)
        };
        let identity = coarsen(&self.ones, 1);
        let rows = window_rows(full_pairs);
        let window = |index: usize| {
            let base = index * rows;
            runs(base..(base + rows).min(full_pairs), &identity)
                .filter(|(_, ones)| !ones)
                .fold([F192::ZERO; 4], |acc, (run, _)| add4(acc, eq.sum(run, summand)))
        };
        let mut message = sum_tasks(full_pairs.div_ceil(rows), full_pairs >= PAR_THRESHOLD, window);
        if !stored_rows.is_multiple_of(2) {
            let tail = eq.sum(full_pairs..full_pairs + 1, |pair, weight| {
                let lo = 8 * pair;
                let lines = [0, 1, 2, 3].map(|child| {
                    let at_zero = self.values[lo + child];
                    [at_zero, at_zero + F192::ONE]
                });
                quartic_summand(lines, weight)
            });
            message = add4(message, tail);
        }
        message
    }

    fn fold_scalar(&mut self, challenge: F192) {
        let stored_rows = self.values.len() / 4;
        let full_rows = stored_rows / 2;
        let rows = stored_rows.div_ceil(2);
        // SAFETY: the windows below write every slot of `next[..4 * full_rows]` and the
        // tail block the odd row, before anything reads it.
        let mut next: Vec<F192> = unsafe { primitives::uninit_vec(4 * rows) };
        let values = &self.values;
        let identity = coarsen(&self.ones, 1);
        let fold_row = |row: usize| -> [F192; 4] {
            if covered(&identity, row..row + 1) {
                return [F192::ONE; 4];
            }
            // One slice, not eight indexes: the bounds checks and the
            // index-by-24 multiplies fall out.
            let v = &values[8 * row..8 * row + 8];
            let folds = mul4(std::array::from_fn(|child| v[child] + v[4 + child]), [challenge; 4]);
            std::array::from_fn(|child| v[child] + folds[child])
        };
        // The next round is what reads the output, and a layer this size is long
        // evicted by then, so where an ordinary store fetches the line it
        // overwrites the pair is staged and published with streaming stores.
        // Where it does not, the stage buys nothing and costs a real call, the
        // `slot.len()` being one the compiler cannot fold away.
        #[cfg(target_arch = "x86_64")]
        let window = |base: usize, destination: &mut [F192]| {
            let stream = Stream::new();
            for (pair, slot) in destination.chunks_mut(8).enumerate() {
                let mut both = [F192::ZERO; 8];
                both[..4].copy_from_slice(&fold_row(base + 2 * pair));
                if slot.len() == 8 {
                    both[4..].copy_from_slice(&fold_row(base + 2 * pair + 1));
                }
                stream.copy(slot, &both[..slot.len()]);
            }
        };
        #[cfg(not(target_arch = "x86_64"))]
        let window = |base: usize, destination: &mut [F192]| {
            for (pair, slot) in destination.chunks_mut(8).enumerate() {
                slot[..4].copy_from_slice(&fold_row(base + 2 * pair));
                if slot.len() == 8 {
                    slot[4..].copy_from_slice(&fold_row(base + 2 * pair + 1));
                }
            }
        };
        if full_rows >= PAR_THRESHOLD {
            let rows = window_rows(full_rows);
            parallel::chunks_mut(&mut next[..4 * full_rows], 4 * rows, |index, destination| {
                window(index * rows, destination);
            });
        } else {
            window(0, &mut next[..4 * full_rows]);
        }
        if !stored_rows.is_multiple_of(2) {
            let lo = 8 * full_rows;
            let folds = mul4(
                [0, 1, 2, 3].map(|child| self.values[lo + child] + F192::ONE),
                [challenge; 4],
            );
            for child in 0..4 {
                next[4 * full_rows + child] = self.values[lo + child] + folds[child];
            }
        }
        self.values = next;
        self.logical_rows /= 2;
        self.ones = identity;
    }

    fn fold_and_message_scalar(&mut self, challenge: F192, eq: &SplitEq) -> [F192; 4] {
        let stored_rows = self.values.len() / 4;
        let rows = stored_rows.div_ceil(2);
        // SAFETY: the tasks below write every slot of `next[..4 * rows]` before anything reads it.
        let mut next: Vec<F192> = unsafe { primitives::uninit_vec(4 * rows) };
        let values = &self.values;
        // Rows of the folded layer, and pairs of them, known to be the identity.
        let identity = coarsen(&self.ones, 1);
        let identity_pairs = coarsen(&identity, 1);
        let dst = parallel::SendPtr(next.as_mut_ptr());
        const PAIRS: usize = 16;
        let pairs = rows.div_ceil(2);
        let task = |index: usize| {
            let first = index * PAIRS;
            let end = (first + PAIRS).min(pairs);
            let mut stage = [F192::ZERO; 8 * PAIRS];
            let end_row = (2 * end).min(rows);
            for row in 2 * first..end_row {
                let offset = 4 * (row - 2 * first);
                if covered(&identity, row..row + 1) {
                    stage[offset..offset + 4].fill(F192::ONE);
                    continue;
                }
                let lo = 8 * row;
                let left = &values[lo..lo + 4];
                let right = values.get(lo + 4..lo + 8).unwrap_or(&[F192::ONE; 4]);
                let product = mul4(std::array::from_fn(|i| left[i] + right[i]), [challenge; 4]);
                for i in 0..4 {
                    stage[offset + i] = left[i] + product[i];
                }
            }
            let summand = |pair: usize, weight: F192| {
                let lo = 8 * (pair - first);
                let left = &stage[lo..lo + 4];
                let right = if 2 * pair + 1 < rows {
                    &stage[lo + 4..lo + 8]
                } else {
                    &[F192::ONE; 4]
                };
                let lines = std::array::from_fn(|i| [left[i], left[i] + right[i]]);
                quartic_summand(lines, weight)
            };
            let message = runs(first..end, &identity_pairs)
                .filter(|(_, ones)| !ones)
                .fold([F192::ZERO; 4], |acc, (run, _)| add4(acc, eq.sum(run, summand)));
            // The next round reads the destination; this round reads only the local stage.
            let stream = Stream::new();
            let len = 4 * (end_row - 2 * first);
            // SAFETY: tasks own disjoint initialized prefixes of the output, covering every row.
            unsafe { stream.copy(dst.slice(8 * first, len), &stage[..len]) };
            message
        };
        let message = sum_tasks(pairs.div_ceil(PAIRS), rows >= PAR_THRESHOLD, task);
        self.values = next;
        self.logical_rows /= 2;
        self.ones = identity;
        message
    }

    fn children(&self) -> [F192; 4] {
        debug_assert_eq!(self.values.len(), 4);
        debug_assert_eq!(self.logical_rows, 1);
        self.values[..4].try_into().unwrap()
    }
}

/// Fold every tree by `challenge`, returning the next round's messages.
fn fold_and_message(trees: &mut [QuaternaryLayerState; 3], challenge: F192, eq: &SplitEq) -> [[F192; 4]; 3] {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
    {
        if trees[0].logical_rows >= VERTICAL_ROWS {
            let [a, b, c] = trees.each_mut().map(QuaternaryLayerState::split);
            let messages = vertical::fold([a.0, b.0, c.0], challenge, eq, [a.1, b.1, c.1]);
            for tree in trees.iter_mut() {
                std::mem::swap(&mut tree.groups, &mut tree.spare);
                tree.values = Vec::new();
                tree.logical_rows /= 2;
                tree.ones = coarsen(&tree.ones, 1);
            }
            return messages;
        }
        for tree in trees.iter_mut() {
            tree.leave_groups();
        }
    }
    trees.each_mut().map(|tree| tree.fold_and_message_scalar(challenge, eq))
}

/// The AVX-512 kernels: eight pairs of rows at a time, transposed so that every
/// product is lane-wise ([`primitives::field::x8`]). After its first fold a layer
/// keeps its rows transposed, in [`Group`]s, until it is small enough for the scalar
/// kernels.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
mod vertical {
    use super::{SplitEq, add4, coarsen, covered, sum_tasks};
    use primitives::field::F192;
    use primitives::field::x8::{F192x8, Sum8};
    use primitives::stream::Stream;
    use std::ops::Range;

    /// Eight pairs of rows: `g[4h + c]` lane `p` is child `c` of row `2p + h`.
    pub(super) type Group = [F192x8; 8];

    /// Groups per parallel task.
    const TASK: usize = 32;

    /// Group `g` of a row table, the identity past its end.
    #[inline(always)]
    fn load(values: &[F192], g: usize) -> Group {
        match values.get(64 * g..64 * g + 64) {
            Some(run) => F192x8::load_runs(run.try_into().unwrap()),
            None => {
                let mut padded = [F192::ONE; 64];
                let tail = &values[(64 * g).min(values.len())..];
                padded[..tail.len()].copy_from_slice(tail);
                F192x8::load_runs(&padded)
            }
        }
    }

    /// Add eight pairs' `eq`-weighted summands. The weight scales child 0's line, and
    /// with it every product, so it costs two products rather than one per coefficient.
    #[inline(always)]
    fn add_message(g: &Group, eq: F192x8, acc: &mut [Sum8; 4]) {
        let a0 = eq * g[0];
        let d0 = eq * (g[0] + g[4]);
        let left0 = a0 * g[1];
        let left2 = d0 * (g[1] + g[5]);
        let left1 = (a0 + d0) * g[5] + left0 + left2;
        let right0 = g[2] * g[3];
        let right2 = (g[2] + g[6]) * (g[3] + g[7]);
        let right1 = g[6] * g[7] + right0 + right2;
        let c0 = left0.mul_sum(right0);
        let c4 = left2.mul_sum(right2);
        let middle = left1.mul_sum(right1);
        let at_one = (left0 + left1 + left2).mul_sum(right0 + right1 + right2);
        let cross_even = (left0 + left2).mul_sum(right0 + right2);
        let cross_high = (left1 + left2).mul_sum(right1 + right2);
        acc[0] ^= c0 ^ at_one;
        acc[1] ^= cross_even ^ c0 ^ c4 ^ middle;
        acc[2] ^= cross_high ^ middle ^ c4;
        acc[3] ^= c4;
    }

    /// A task's message: group sums under one high `eq` factor, flushed when it changes.
    struct Message<'a> {
        eq: &'a SplitEq,
        block: usize,
        sums: [Sum8; 4],
        total: [F192; 4],
    }

    impl<'a> Message<'a> {
        fn new(eq: &'a SplitEq, first: usize) -> Self {
            Self {
                eq,
                block: first >> (eq.lo_bits - 3),
                sums: [Sum8::ZERO; 4],
                total: [F192::ZERO; 4],
            }
        }

        #[inline(always)]
        fn add(&mut self, g: usize, group: &Group) {
            let shift = self.eq.lo_bits - 3;
            if g >> shift != self.block {
                self.flush();
                self.block = g >> shift;
            }
            add_message(group, self.eq.lo8[g & ((1 << shift) - 1)], &mut self.sums);
        }

        fn flush(&mut self) {
            let sums = std::mem::replace(&mut self.sums, [Sum8::ZERO; 4]).map(Sum8::reduce);
            let scaled = primitives::field::mul4([self.eq.hi[self.block]; 4], sums);
            self.total = add4(self.total, scaled);
        }

        fn finish(mut self) -> [F192; 4] {
            self.flush();
            self.total
        }
    }

    /// The round message of a row table; identity pairs add nothing.
    pub(super) fn message(values: &[F192], ones: &[Range<usize>], eq: &SplitEq) -> [F192; 4] {
        let groups = values.len().div_ceil(64);
        sum_tasks(groups.div_ceil(TASK), groups > TASK, |task| {
            let range = task * TASK..((task + 1) * TASK).min(groups);
            let mut message = Message::new(eq, range.start);
            for g in range {
                if !covered(ones, 16 * g..16 * g + 16) {
                    message.add(g, &load(values, g));
                }
            }
            message.finish()
        })
    }

    /// Fold sixteen pairs, `a`'s then `b`'s, into the eight pairs their sixteen rows make.
    #[inline(always)]
    fn fold_pairs(a: &Group, b: &Group, r: F192x8) -> Group {
        let fold = |g: &Group, c: usize| g[c] + r * (g[c] + g[4 + c]);
        let mut out = [F192x8::splat(F192::ZERO); 8];
        for c in 0..4 {
            (out[c], out[4 + c]) = F192x8::deinterleave(fold(a, c), fold(b, c));
        }
        out
    }

    pub(super) enum Data<'a> {
        Rows(&'a [F192]),
        Groups(&'a [Group]),
    }

    /// A layer's rows as a fold reads them, with the runs known to be the identity.
    pub(super) struct Input<'a> {
        pub(super) data: Data<'a>,
        pub(super) ones: &'a [Range<usize>],
    }

    impl Input<'_> {
        fn len(&self) -> usize {
            match self.data {
                Data::Rows(values) => values.len().div_ceil(64),
                Data::Groups(groups) => groups.len(),
            }
        }

        /// Group `g`, the identity past the end or where `ones` says so.
        #[inline(always)]
        fn get(&self, g: usize) -> Group {
            let ones = [F192x8::splat(F192::ONE); 8];
            if covered(self.ones, 16 * g..16 * g + 16) {
                return ones;
            }
            match self.data {
                Data::Rows(values) => load(values, g),
                Data::Groups(groups) => groups.get(g).copied().unwrap_or(ones),
            }
        }
    }

    /// Fold every tree's rows by `challenge` into its `out`, in one dispatch for the
    /// three, returning the next round's messages.
    pub(super) fn fold(
        inputs: [Input; 3],
        challenge: F192,
        eq: &SplitEq,
        outs: [&mut Vec<Group>; 3],
    ) -> [[F192; 4]; 3] {
        /// Groups below which a dispatch costs more than it saves.
        const PARALLEL: usize = 8 * TASK;
        let n_out = inputs.each_ref().map(|input| input.len().div_ceil(2));
        let mut outs = outs;
        let dst: [parallel::SendPtr<Group>; 3] = std::array::from_fn(|t| {
            let out = &mut *outs[t];
            if out.capacity() < n_out[t] {
                *out = Vec::new();
                // SAFETY: the tasks below write every group before anything reads it.
                *out = unsafe { primitives::uninit_vec(n_out[t]) };
            } else {
                // SAFETY: as above; `Group` is plain data.
                unsafe { out.set_len(n_out[t]) };
            }
            parallel::SendPtr(out.as_mut_ptr())
        });
        let tasks: Vec<(usize, usize)> = (0..3)
            .flat_map(|t| (0..n_out[t]).step_by(TASK).map(move |g| (t, g)))
            .collect();
        let r = F192x8::splat(challenge);
        let ones = inputs.each_ref().map(|input| coarsen(input.ones, 1));
        let task = |i: usize| {
            let (t, first) = tasks[i];
            let stream = Stream::new();
            let mut message = Message::new(eq, first);
            for g in first..(first + TASK).min(n_out[t]) {
                // Identity rows fold to identity rows, which add nothing, and their
                // group is left unwritten.
                if covered(&ones[t], 16 * g..16 * g + 16) {
                    continue;
                }
                let pairs = fold_pairs(&inputs[t].get(2 * g), &inputs[t].get(2 * g + 1), r);
                message.add(g, &pairs);
                // The next round reads it, long after this round's pass evicted it.
                // SAFETY: tasks own disjoint groups of the outputs.
                unsafe { stream.copy(dst[t].slice(g, 1), std::slice::from_ref(&pairs)) };
            }
            let mut messages = [[F192::ZERO; 4]; 3];
            messages[t] = message.finish();
            messages
        };
        let add = |a: [[F192; 4]; 3], b: [[F192; 4]; 3]| std::array::from_fn(|t| add4(a[t], b[t]));
        if n_out.iter().sum::<usize>() > PARALLEL {
            parallel::map_reduce(tasks.len(), || [[F192::ZERO; 4]; 3], task, add)
        } else {
            (0..tasks.len()).map(task).fold([[F192::ZERO; 4]; 3], add)
        }
    }

    pub(super) fn to_rows(groups: &[Group], ones: &[Range<usize>]) -> Vec<F192> {
        let mut values = vec![F192::ZERO; 64 * groups.len()];
        for (g, group) in groups.iter().enumerate() {
            if covered(ones, 16 * g..16 * g + 16) {
                values[64 * g..64 * g + 64].fill(F192::ONE);
                continue;
            }
            for (j, lanes) in group.iter().enumerate() {
                for (p, e) in lanes.to_array().into_iter().enumerate() {
                    values[64 * g + 8 * p + j] = e;
                }
            }
        }
        values
    }

    /// `out[i] = ∏ current[4i..4i+4]` for the leading multiple of sixteen rows; returns how many.
    pub(super) fn products_into(current: &[F192], out: &mut [F192]) -> usize {
        let product = |a: F192x8, b: F192x8, c: F192x8, d: F192x8| (a * b) * (c * d);
        let (chunks, _) = out.as_chunks_mut::<16>();
        for (slot, run) in chunks.iter_mut().zip(current.as_chunks::<64>().0) {
            let g = F192x8::load_runs(run);
            let (lo, hi) = F192x8::interleave(product(g[0], g[1], g[2], g[3]), product(g[4], g[5], g[6], g[7]));
            let (first, second) = slot.split_at_mut(8);
            lo.store(first.try_into().unwrap());
            hi.store(second.try_into().unwrap());
        }
        16 * chunks.len()
    }
}

/// The result of a batched grand-product proof: the three roots and leaf
/// evaluations, all reduced to one shared point. Under [`RootShape::FirstTwoShared`],
/// `roots[0] == roots[1]` by construction rather than by a check.
pub struct ProductTriple {
    pub roots: [F192; 3],
    pub point: Vec<F192>,
    pub values: [F192; 3],
}

/// How many of the three roots ride the stream, which is a property of the statement rather than
/// of the reduction below.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RootShape {
    /// Three unrelated products: every root is sent.
    Distinct,
    /// The first two trees share a product by construction, as the bus's two sides do
    /// (a padding row's leaf is the identity on both, so they balance outright). ONE root
    /// is then sent for both, and no verifier can be handed an unbalanced pair to check.
    FirstTwoShared,
}

/// Prove three identity-padded grand products as one RLC-batched radix-four GKR.
pub fn prove_product_triple(leaves: [Leaves; 3], ps: &mut ProverState, shape: RootShape) -> ProductTriple {
    let mu = crate::log2_ceil_usize(leaves[0].values.len());
    assert!(
        leaves
            .iter()
            .all(|lane| !lane.values.is_empty() && lane.values.len() <= 1 << mu),
        "batched trees must be nonempty prefixes of the first tree's logical tree"
    );
    // In leaves; a layer's rows over level `l` are runs of `2^(l + 2)` leaves.
    let identities = leaves.each_ref().map(|lane| lane.ones.clone());
    let mut layers = leaves.map(|lane| build_layers(lane, mu));
    let roots = [layers[0][mu][0], layers[1][mu][0], layers[2][mu][0]];
    match shape {
        RootShape::Distinct => {
            for root in roots {
                ps.add_scalar(root);
            }
        }
        RootShape::FirstTwoShared => {
            assert_eq!(roots[0], roots[1], "FirstTwoShared needs the two products to agree");
            ps.add_scalar(roots[0]);
            ps.add_scalar(roots[2]);
        }
    }
    let mut point = Vec::new();
    let mut values = roots;

    let mut layer = mu;
    while layer > 0 {
        let lambda = ps.sample();
        let round_count = mu - layer;
        if layer % 2 == 1 {
            debug_assert_eq!(round_count, 0, "only the root-most layer may be binary");
            let tails = [0, 1, 2].map(|tree| {
                let below = &layers[tree][layer - 1];
                match below.as_slice() {
                    [left, right] => [*left, *right],
                    [left] => [*left, F192::ONE],
                    _ => unreachable!("the root's children have at most two explicit nodes"),
                }
            });
            for tail in &tails {
                ps.add_scalars(tail);
            }
            let challenge = ps.sample();
            for (value, [left, right]) in values.iter_mut().zip(tails) {
                *value = interp(left, right, challenge);
            }
            point = vec![challenge];
            layer -= 1;
            continue;
        }

        let width = 1usize << round_count;
        #[allow(unused_mut)]
        let mut trees =
            [0, 1, 2].map(|tree| QuaternaryLayerState::new(std::mem::take(&mut layers[tree][layer - 2]), width));
        if SKIP_IDENTITY {
            for (tree, ones) in trees.iter_mut().zip(&identities) {
                tree.ones = coarsen(ones, layer);
            }
        }
        let mut round_point = Vec::with_capacity(round_count);
        // Round `j` weights its pairs by `eq(point[1 + j..], ·)`.
        let mut messages = if round_count > 0 {
            let eq = SplitEq::new(&point[1..]);
            trees.each_ref().map(|tree| tree.round_message(&eq))
        } else {
            [[F192::ZERO; 4]; 3]
        };
        for round in 0..round_count {
            let mut coeffs = [0, 1, 2, 3].map(|coefficient| {
                messages[0][coefficient] + lambda * (messages[1][coefficient] + lambda * messages[2][coefficient])
            });
            // The kernel accumulates `q(0) + q(1)`, the wire carries `c1`. This is
            // `ProverState::add_round_poly(_, true)` bar its dropped `c0`, which the
            // claim fixes and the prover therefore never forms.
            coeffs[0] = coeffs[0] + coeffs[1] + coeffs[2] + coeffs[3];
            ps.add_scalars(&coeffs);
            let challenge = ps.sample();
            round_point.push(challenge);
            if round + 1 < round_count {
                let eq = SplitEq::new(&point[2 + round..]);
                messages = fold_and_message(&mut trees, challenge, &eq);
            } else {
                // The final round has no next message to weight, and needs the
                // fold alone. Both kernels stay for that reason; `fold` is not dead.
                for tree in &mut trees {
                    tree.fold(challenge);
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
        point = vec![low_challenge, high_challenge];
        point.extend_from_slice(&round_point);
        layer -= 2;
    }

    ProductTriple { roots, point, values }
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

    fn element(i: usize, salt: usize) -> F192 {
        F192::new((17 * i + salt + 1) as u64, (i * i + 3) as u64, (5 * i + 7) as u64)
    }

    #[test]
    fn quartic_round_message_matches_direct_evaluation() {
        for width in [2, 4, 8, 16, 1 << 11] {
            let below: Vec<F192> = (0..4 * width).map(|i| element(i, width)).collect();
            let state = QuaternaryLayerState::new(below, width);
            let point: Vec<F192> = (0..width.ilog2() - 1).map(|i| element(31 * i as usize, 5)).collect();
            let equality = eq_table(&point);
            let [difference, c2, c3, c4] = state.round_message(&SplitEq::new(&point));
            let direct = |point: F192| {
                (0..width / 2).fold(F192::ZERO, |sum, row| {
                    let values = [0, 1, 2, 3]
                        .map(|child| interp(state.values[8 * row + child], state.values[8 * row + 4 + child], point));
                    sum + equality[row] * values[0] * values[1] * values[2] * values[3]
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

    /// The fused and the vertical kernels against the scalar fold and message, every round.
    #[test]
    fn fused_fold_matches_separate_fold_and_message() {
        for width in [4usize, 16, 1 << 11, 1 << 14] {
            let lens = [1, 4, 5, 7, 8, 9, 31, 32, 33, 4 * width - 5, 4 * width - 1, 4 * width];
            for three in lens.windows(3).filter(|l| l.iter().all(|&n| n <= 4 * width)) {
                let tree = |n: usize| QuaternaryLayerState::new((0..n).map(|i| element(i, n)).collect(), width);
                let mut reference = [three[0], three[1], three[2]].map(tree);
                let mut fused = [three[0], three[1], three[2]].map(tree);
                let point: Vec<F192> = (0..width.ilog2() - 1)
                    .map(|i| F192::new(31 + u64::from(i), 7, 11))
                    .collect();
                let eq = SplitEq::new(&point);
                for (f, r) in fused.iter().zip(&reference) {
                    assert_eq!(f.round_message(&eq), r.round_message_scalar(&eq));
                }
                let mut round = 0;
                while reference[0].logical_rows > 2 {
                    round += 1;
                    let challenge = F192::new(reference[0].logical_rows as u64, 13, 19);
                    let eq = SplitEq::new(&point[round..]);
                    let messages = fold_and_message(&mut fused, challenge, &eq);
                    for (r, message) in reference.iter_mut().zip(messages) {
                        r.fold_scalar(challenge);
                        assert_eq!(message, r.round_message_scalar(&eq), "width={width}, lens={three:?}");
                    }
                }
                for (f, r) in fused.iter_mut().zip(&mut reference) {
                    r.fold(F192::Y);
                    f.fold(F192::Y);
                    assert_eq!(f.children(), r.children());
                }
            }
        }
    }

    #[test]
    fn level_products_match_scalar() {
        for len in [4, 5, 63, 64, 65, 4 << 12, (4 << 12) + 3, (4 << 13) - 1] {
            let current: Vec<F192> = (0..len).map(|i| element(i, 3)).collect();
            let want: Vec<F192> = current
                .chunks(4)
                .map(|c| c.iter().fold(F192::ONE, |acc, &v| acc * v))
                .collect();
            assert_eq!(next_level(&current), want, "len={len}");
        }
    }

    #[test]
    fn radix_four_claims_are_true_at_even_and_odd_depths() {
        for mu in 0..=10 {
            let leaves: [Vec<F192>; 3] = [0, 1, 2].map(|lane| {
                (0..1usize << mu)
                    .map(|row| F192::new((1 + row + lane * 100_003) as u64, row as u64, lane as u64))
                    .collect()
            });
            let expected_roots = leaves
                .each_ref()
                .map(|lane| lane.iter().copied().fold(F192::ONE, |product, value| product * value));
            let mut ps = ProverState::from_label(b"radix-four-gkr-test");
            let proved = prove_product_triple(
                leaves.each_ref().map(|l| Leaves::new(l.to_vec())),
                &mut ps,
                RootShape::Distinct,
            );
            assert_eq!(proved.roots, expected_roots);
            for lane in 0..3 {
                assert_eq!(proved.values[lane], mle_eval_e(&leaves[lane], &proved.point));
            }
        }
    }

    #[test]
    fn implicit_identity_suffix_matches_dense_padding() {
        for mu in 3..=10 {
            let lengths = [(1usize << mu) - 3, (1usize << (mu - 1)) + 1, (1usize << (mu - 2)) + 3];
            let leaves: [Vec<F192>; 3] = std::array::from_fn(|lane| {
                (0..lengths[lane])
                    .map(|row| F192::new((3 + row + lane * 10_007) as u64, row as u64, lane as u64))
                    .collect()
            });
            let dense = leaves.each_ref().map(|lane| {
                let mut padded = lane.clone();
                padded.resize(1 << mu, F192::ONE);
                padded
            });
            let mut sparse_ps = ProverState::from_label(b"sparse-radix-four-gkr-test");
            let proved = prove_product_triple(
                leaves.each_ref().map(|l| Leaves::new(l.to_vec())),
                &mut sparse_ps,
                RootShape::Distinct,
            );
            for lane in 0..3 {
                assert_eq!(proved.values[lane], mle_eval_e(&dense[lane], &proved.point));
                assert_eq!(
                    proved.roots[lane],
                    dense[lane]
                        .iter()
                        .copied()
                        .fold(F192::ONE, |product, value| product * value)
                );
            }
            let proof = sparse_ps.into_proof();
            let mut dense_ps = ProverState::from_label(b"sparse-radix-four-gkr-test");
            let dense_proved = prove_product_triple(
                dense.each_ref().map(|l| Leaves::new(l.to_vec())),
                &mut dense_ps,
                RootShape::Distinct,
            );
            assert_eq!(dense_proved.roots, proved.roots);
            assert_eq!(dense_proved.point, proved.point);
            assert_eq!(dense_proved.values, proved.values);
            assert_eq!(dense_ps.into_proof().stream, proof.stream);
        }
    }
}
