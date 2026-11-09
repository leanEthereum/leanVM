//! The grand product via GKR (§sec:gkr): given leaves `v_0…v_{2^μ-1}`, prove the
//! root `P = ∏ v_k` of the product tree, reducing the root to one leaf evaluation
//! `Ṽ_0(ζ)`. Two binary levels are contracted at a time: a radix-four layer has
//! relation `V_i(x)=∏_{a,b∈{0,1}}V_{i-2}(a,b,x)`. Its normalized eq-trick
//! sumcheck has degree four. An odd-depth tree starts with one binary layer.
//! The bus's two trees are `E`-valued (the fingerprints mix `K`-columns into `E`
//! upstream, [`crate::leaf`]). The count tree's leaves are the counts themselves, so
//! its levels stay in `K` until each layer's first fold.
//!
//! On AVX-512 the large rounds run eight pairs of rows at a time in transposed form
//! (`vertical`), and skip the runs of rows known to be the identity.

use std::ops::Range;

use crate::PAR_THRESHOLD;
use crate::transcript::ProverState;
use primitives::field::{F64, F192, F192Unreduced, mul_unreduced4, mul2, mul4};
use primitives::multilinear::{eq_table, interp, interp_k};
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

/// A product tree's node: `E`, or `K` for the count tree.
pub(crate) trait Node:
    Copy + Send + Sync + primitives::Plain + Into<F192> + std::ops::Add<Output = Self> + std::ops::Mul<Output = Self>
{
    const ONE: Self;
    /// `out[i] = ∏ current[4i..4i+4]`, for `out.len() == current.len() / 4`.
    fn products_into(current: &[Self], out: &mut [Self]);
    /// One pair's `eq`-weighted message terms, from each child's line `[value at 0, slope]`.
    fn summand(lines: [[Self; 2]; 4], equality: F192) -> [F192Unreduced; 4];
    /// The row `left + challenge·(left + right)`, into `E`.
    fn fold_row(left: &[Self], right: &[Self], challenge: F192) -> [F192; 4];
}

impl Node for F192 {
    const ONE: Self = F192::ONE;
    fn products_into(current: &[Self], out: &mut [Self]) {
        products_into(current, out);
    }
    #[inline(always)]
    fn summand(lines: [[Self; 2]; 4], equality: F192) -> [F192Unreduced; 4] {
        quartic_summand(lines, equality)
    }
    #[inline(always)]
    fn fold_row(left: &[Self], right: &[Self], challenge: F192) -> [F192; 4] {
        let product = mul4(std::array::from_fn(|i| left[i] + right[i]), [challenge; 4]);
        std::array::from_fn(|i| left[i] + product[i])
    }
}

impl Node for F64 {
    const ONE: Self = F64::ONE;
    fn products_into(current: &[Self], out: &mut [Self]) {
        for (slot, c) in out.iter_mut().zip(current.as_chunks::<4>().0) {
            *slot = (c[0] * c[1]) * (c[2] * c[3]);
        }
    }
    #[inline(always)]
    fn summand(lines: [[Self; 2]; 4], equality: F192) -> [F192Unreduced; 4] {
        quartic_summand_k(lines, equality)
    }
    #[inline(always)]
    fn fold_row(left: &[Self], right: &[Self], challenge: F192) -> [F192; 4] {
        std::array::from_fn(|i| interp_k(left[i], right[i], challenge))
    }
}

/// A level of `n` values, with room for the identity tuple tail the layer state pads it to,
/// so that padding never reallocates and copies the level.
///
/// # Safety
///
/// The caller writes every value of `0..n` before anything reads it.
pub(crate) unsafe fn level<T: Node>(n: usize) -> Vec<T> {
    // SAFETY: forwarded to the caller.
    let mut values = unsafe { primitives::uninit_vec(n.next_multiple_of(4)) };
    values.truncate(n);
    values
}

/// The level above `current`: the product of each four-tuple, an incomplete last one
/// padded with the identity.
fn next_level<T: Node>(current: &[T]) -> Vec<T> {
    /// Rows per task, staged before they are published.
    const ROWS: usize = 1 << 9;
    let full_rows = current.len() / 4;
    // SAFETY: the products below write `next[..full_rows]`, and the tail its last slot.
    let mut next = unsafe { level(current.len().div_ceil(4)) };
    if full_rows >= PAR_THRESHOLD {
        // The next level and the GKR read the output long after this pass evicts it.
        parallel::chunks_mut(&mut next[..full_rows], ROWS, |task, destination| {
            let mut stage = [T::ONE; ROWS];
            let stage = &mut stage[..destination.len()];
            let start = 4 * ROWS * task;
            T::products_into(&current[start..start + 4 * stage.len()], stage);
            Stream::new().copy(destination, stage);
        });
    } else {
        T::products_into(&current[..4 * full_rows], &mut next[..full_rows]);
    }
    let tail = &current[4 * full_rows..];
    if !tail.is_empty() {
        let child = |index| tail.get(index).copied().unwrap_or(T::ONE);
        next[full_rows] = (child(0) * child(1)) * (child(2) * child(3));
    }
    next
}

/// A tree's leaves, with the two levels above them, which the leaf builder forms while
/// the leaves are in cache, and its runs of identity leaves.
#[derive(Clone)]
pub(crate) struct Leaves<T = F192> {
    pub values: Vec<T>,
    /// `fours[i] = ∏ values[4i..4i+4]`, and `sixteens` likewise over `fours`, an
    /// incomplete last four-tuple padded with the identity.
    pub(crate) fours: Vec<T>,
    pub(crate) sixteens: Vec<T>,
    /// Runs of identity leaves among `values`, sorted, which the GKR rounds above them
    /// need neither read nor write.
    pub ones: Vec<Range<usize>>,
}

impl<T: Node> Leaves<T> {
    pub fn new(values: Vec<T>) -> Self {
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
fn build_layers<T: Node>(leaves: Leaves<T>, mu: usize) -> Vec<Vec<T>> {
    // The leaf level alone is large at production sizes, and every level dies
    // with the proof.
    let mut layers: Vec<Vec<T>> = (0..=mu).map(|_| Vec::new()).collect();
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

/// [`quartic_summand`] of `K` lines: every product stays in `K`, and the weight multiplies only
/// the four coefficients.
#[inline(always)]
fn quartic_summand_k(lines: [[F64; 2]; 4], equality: F192) -> [F192Unreduced; 4] {
    let [[g0, s0], [g1, s1], [g2, s2], [g3, s3]] = lines;
    let quadratic = |g: F64, s: F64, h: F64, t: F64| {
        let (zero, two, at_one) = (g * h, s * t, (g + s) * (h + t));
        (zero, at_one + zero + two, two, at_one)
    };
    let (left0, left1, left2, left_at_one) = quadratic(g0, s0, g1, s1);
    let (right0, right1, right2, right_at_one) = quadratic(g2, s2, g3, s3);
    let (c0, c4, middle, at_one) = (
        left0 * right0,
        left2 * right2,
        left1 * right1,
        left_at_one * right_at_one,
    );
    let cross_even = (left0 + left2) * (right0 + right2);
    let cross_high = (left1 + left2) * (right1 + right2);
    let weigh = |c: F64| equality.mul_base_unreduced(c);
    [
        weigh(c0 + at_one),
        weigh(cross_even + c0 + c4 + middle),
        weigh(cross_high + middle + c4),
        weigh(c4),
    ]
}

/// The rows of a level `shift` binary levels up whose children are all in `ones`.
fn coarsen(ones: &[Range<usize>], shift: usize) -> Vec<Range<usize>> {
    ones.iter()
        .map(|r| r.start.div_ceil(1 << shift)..r.end >> shift)
        .filter(|r| !r.is_empty())
        .collect()
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
    /// The count tree's rows before the layer's first fold, in `K`; `values` is empty meanwhile.
    base: Vec<F64>,
}

impl QuaternaryLayerState {
    fn new(values: Vec<F192>, width: usize) -> Self {
        Self::with_rows(pad_rows(values, width), Vec::new(), width)
    }

    /// A `K`-valued layer: its first message and fold take mixed products. A layer of fewer
    /// than two rounds has no fold that feeds a message, so it starts in `E`.
    fn new_k(base: Vec<F64>, width: usize) -> Self {
        if width < 4 {
            return Self::new(base.into_iter().map(F192::from).collect(), width);
        }
        Self::with_rows(Vec::new(), pad_rows(base, width), width)
    }

    fn with_rows(values: Vec<F192>, base: Vec<F64>, width: usize) -> Self {
        Self {
            values,
            logical_rows: width,
            #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
            groups: Vec::new(),
            #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
            spare: Vec::new(),
            ones: Vec::new(),
            base,
        }
    }

    fn is_k(&self) -> bool {
        !self.base.is_empty()
    }

    /// `(q(0)+q(1), [X²]q, [X³]q, [X⁴]q)`.
    fn round_message(&self, eq: &SplitEq) -> [F192; 4] {
        if self.is_k() {
            return round_message_rows(&self.base, &self.ones, eq);
        }
        #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
        if self.logical_rows >= VERTICAL_ROWS {
            return vertical::message(&self.values, &self.ones, eq);
        }
        round_message_rows(&self.values, &self.ones, eq)
    }

    fn fold(&mut self, challenge: F192) {
        debug_assert!(!self.is_k());
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

    fn fold_scalar(&mut self, challenge: F192) {
        let stored_rows = self.values.len() / 4;
        let full_rows = stored_rows / 2;
        let rows = stored_rows.div_ceil(2);
        // SAFETY: the windows below write every slot of `next[..4 * full_rows]` and the
        // tail block the odd row, before anything reads it.
        let mut next: Vec<F192> = unsafe { primitives::uninit_vec(4 * rows) };
        let values = &self.values;
        let identity = coarsen(&self.ones, 1);
        let fold_row = |row: usize, one: bool| -> [F192; 4] {
            if one {
                return [F192::ONE; 4];
            }
            // One slice, not eight indexes: the bounds checks and the
            // index-by-24 multiplies fall out.
            let v = &values[8 * row..8 * row + 8];
            let folds = mul4(std::array::from_fn(|child| v[child] + v[4 + child]), [challenge; 4]);
            std::array::from_fn(|child| v[child] + folds[child])
        };
        // The folded rows `base..base + n`, the identity's runs found in one walk.
        let folded = |base: usize, n: usize| {
            runs(base..base + n, &identity).flat_map(|(run, one)| run.map(move |row| fold_row(row, one)))
        };
        // The next round is what reads the output, and a layer this size is long
        // evicted by then, so where an ordinary store fetches the line it
        // overwrites the pair is staged and published with streaming stores.
        // Where it does not, the stage buys nothing and costs a real call, the
        // `slot.len()` being one the compiler cannot fold away.
        #[cfg(target_arch = "x86_64")]
        let window = |base: usize, destination: &mut [F192]| {
            let stream = Stream::new();
            let mut rows = folded(base, destination.len() / 4);
            for slot in destination.chunks_mut(8) {
                let mut both = [F192::ZERO; 8];
                for (half, row) in both[..slot.len()].chunks_mut(4).zip(&mut rows) {
                    half.copy_from_slice(&row);
                }
                stream.copy(slot, &both[..slot.len()]);
            }
        };
        #[cfg(not(target_arch = "x86_64"))]
        let window = |base: usize, destination: &mut [F192]| {
            let rows = folded(base, destination.len() / 4);
            for (slot, row) in destination.chunks_mut(4).zip(rows) {
                slot.copy_from_slice(&row);
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
        let (next, message) = if self.is_k() {
            fold_and_message_rows(&self.base, &self.ones, challenge, eq)
        } else {
            fold_and_message_rows(&self.values, &self.ones, challenge, eq)
        };
        self.values = next;
        self.base = Vec::new();
        self.logical_rows /= 2;
        self.ones = coarsen(&self.ones, 1);
        message
    }

    fn children(&self) -> [F192; 4] {
        debug_assert_eq!(self.values.len(), 4);
        debug_assert_eq!(self.logical_rows, 1);
        self.values[..4].try_into().unwrap()
    }
}

/// Pad `rows` with the identity to whole four-tuples. Every complete all-one row after
/// the explicit prefix remains implicit.
fn pad_rows<T: Node>(mut rows: Vec<T>, width: usize) -> Vec<T> {
    rows.resize(4 * rows.len().max(1).div_ceil(4), T::ONE);
    debug_assert!(rows.len() <= 4 * width);
    rows
}

/// [`QuaternaryLayerState::round_message`] of stored rows in either field.
fn round_message_rows<T: Node>(values: &[T], ones: &[Range<usize>], eq: &SplitEq) -> [F192; 4] {
    let stored_rows = values.len() / 4;
    let full_pairs = stored_rows / 2;
    let summand = |pair: usize, weight: F192| -> [F192Unreduced; 4] {
        let (lo, hi) = (8 * pair, 8 * pair + 4);
        let lines = [0, 1, 2, 3].map(|child| {
            let at_zero = values[lo + child];
            [at_zero, at_zero + values[hi + child]]
        });
        T::summand(lines, weight)
    };
    let identity = coarsen(ones, 1);
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
                let at_zero = values[lo + child];
                [at_zero, at_zero + T::ONE]
            });
            T::summand(lines, weight)
        });
        message = add4(message, tail);
    }
    message
}

/// Fold stored rows in either field by `challenge` into `E` rows, with the next round's message.
fn fold_and_message_rows<T: Node>(
    values: &[T],
    ones: &[Range<usize>],
    challenge: F192,
    eq: &SplitEq,
) -> (Vec<F192>, [F192; 4]) {
    let stored_rows = values.len() / 4;
    let rows = stored_rows.div_ceil(2);
    // SAFETY: the tasks below write every slot of `next[..4 * rows]` before anything reads it.
    let mut next: Vec<F192> = unsafe { primitives::uninit_vec(4 * rows) };
    // Rows of the folded layer, and pairs of them, known to be the identity.
    let identity = coarsen(ones, 1);
    let identity_pairs = coarsen(&identity, 1);
    let dst = parallel::SendPtr(next.as_mut_ptr());
    const PAIRS: usize = 16;
    let pairs = rows.div_ceil(2);
    let ones_row = [T::ONE; 4];
    let task = |index: usize| {
        let first = index * PAIRS;
        let end = (first + PAIRS).min(pairs);
        let mut stage = [F192::ZERO; 8 * PAIRS];
        let end_row = (2 * end).min(rows);
        for (run, one) in runs(2 * first..end_row, &identity) {
            let staged = &mut stage[4 * (run.start - 2 * first)..4 * (run.end - 2 * first)];
            if one {
                staged.fill(F192::ONE);
                continue;
            }
            for (row, out) in run.zip(staged.as_chunks_mut::<4>().0) {
                let lo = 8 * row;
                let right = values.get(lo + 4..lo + 8).unwrap_or(&ones_row);
                *out = T::fold_row(&values[lo..lo + 4], right, challenge);
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
    (next, message)
}

/// Fold every tree by `challenge`, returning the next round's messages. A `K` count tree
/// takes its first fold on its own.
fn fold_and_message(trees: &mut [QuaternaryLayerState; 3], challenge: F192, eq: &SplitEq) -> [[F192; 4]; 3] {
    let [push, pull, count] = trees;
    if count.is_k() {
        let count = count.fold_and_message_scalar(challenge, eq);
        let [push, pull] = fold_and_message_e([push, pull], challenge, eq);
        return [push, pull, count];
    }
    fold_and_message_e([push, pull, count], challenge, eq)
}

/// [`fold_and_message`] of `E` trees.
fn fold_and_message_e<const N: usize>(
    mut trees: [&mut QuaternaryLayerState; N],
    challenge: F192,
    eq: &SplitEq,
) -> [[F192; 4]; N] {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
    {
        if trees[0].logical_rows >= VERTICAL_ROWS {
            let messages = vertical::fold(trees.each_mut().map(|tree| tree.split()), challenge, eq);
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
    use super::{SplitEq, add4, coarsen, sum_tasks};
    use primitives::field::F192;
    use primitives::field::x8::{F192x8, Sum8};
    use primitives::stream::Stream;
    use std::ops::Range;

    /// Whether `ones` covers `rows`.
    fn covered(ones: &[Range<usize>], rows: Range<usize>) -> bool {
        let i = ones.partition_point(|r| r.start <= rows.start);
        i > 0 && ones[i - 1].end >= rows.end
    }

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

    /// Fold every tree's rows by `challenge` into its output buffer, in one dispatch for
    /// all of them, returning the next round's messages.
    pub(super) fn fold<const N: usize>(
        mut trees: [(Input, &mut Vec<Group>); N],
        challenge: F192,
        eq: &SplitEq,
    ) -> [[F192; 4]; N] {
        /// Groups below which a dispatch costs more than it saves.
        const PARALLEL: usize = 8 * TASK;
        let n_out = trees.each_ref().map(|(input, _)| input.len().div_ceil(2));
        let dst: [parallel::SendPtr<Group>; N] = std::array::from_fn(|t| {
            let out = &mut *trees[t].1;
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
        let inputs = trees.map(|(input, _)| input);
        let tasks: Vec<(usize, usize)> = (0..N)
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
            let mut messages = [[F192::ZERO; 4]; N];
            messages[t] = message.finish();
            messages
        };
        let add = |a: [[F192; 4]; N], b: [[F192; 4]; N]| std::array::from_fn(|t| add4(a[t], b[t]));
        if n_out.iter().sum::<usize>() > PARALLEL {
            parallel::map_reduce(tasks.len(), || [[F192::ZERO; 4]; N], task, add)
        } else {
            (0..tasks.len()).map(task).fold([[F192::ZERO; 4]; N], add)
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

/// The result of a batched grand-product proof: the three leaf evaluations, all reduced to one shared point.
pub struct ProductTriple {
    pub point: Vec<F192>,
    pub values: [F192; 3],
}

/// The binary root layer's two children, a missing right one the identity.
fn root_children<T: Node>(below: &[T]) -> [F192; 2] {
    match *below {
        [left, right] => [left.into(), right.into()],
        [left] => [left.into(), F192::ONE],
        _ => unreachable!("the root's children have at most two explicit nodes"),
    }
}

/// Prove three identity-padded grand products as one RLC-batched radix-four GKR.
/// The first two trees share a product by construction, as the bus's two sides do.
/// One root is sent for both, then the third, so no verifier can be handed an unbalanced pair.
pub(crate) fn prove_product_triple(leaves: [Leaves; 2], count: Leaves<F64>, ps: &mut ProverState) -> ProductTriple {
    let mu = crate::log2_ceil_usize(leaves[0].values.len());
    let lens = [leaves[0].values.len(), leaves[1].values.len(), count.values.len()];
    assert!(
        lens.iter().all(|&n| n > 0 && n <= 1 << mu),
        "batched trees must be nonempty prefixes of the first tree's logical tree"
    );
    // In leaves; a layer's rows over level `l` are runs of `2^(l + 2)` leaves.
    let identities = [leaves[0].ones.clone(), leaves[1].ones.clone(), count.ones.clone()];
    let mut layers = leaves.map(|lane| build_layers(lane, mu));
    let mut count_layers = build_layers(count, mu);
    let roots = [layers[0][mu][0], layers[1][mu][0], count_layers[mu][0].into()];
    assert_eq!(roots[0], roots[1], "the first two products must agree");
    ps.add_scalar(roots[0]);
    ps.add_scalar(roots[2]);
    let mut point = Vec::new();
    let mut values = roots;

    let mut layer = mu;
    while layer > 0 {
        let lambda = ps.sample();
        let round_count = mu - layer;
        if layer % 2 == 1 {
            debug_assert_eq!(round_count, 0, "only the root-most layer may be binary");
            let tails = [
                root_children(&layers[0][layer - 1]),
                root_children(&layers[1][layer - 1]),
                root_children(&count_layers[layer - 1]),
            ];
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
        let mut trees = [
            QuaternaryLayerState::new(std::mem::take(&mut layers[0][layer - 2]), width),
            QuaternaryLayerState::new(std::mem::take(&mut layers[1][layer - 2]), width),
            QuaternaryLayerState::new_k(std::mem::take(&mut count_layers[layer - 2]), width),
        ];
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

    ProductTriple { point, values }
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
                (0..width / 2)
                    .map(|row| {
                        let values = [0, 1, 2, 3].map(|child| {
                            interp(state.values[8 * row + child], state.values[8 * row + 4 + child], point)
                        });
                        equality[row] * values[0] * values[1] * values[2] * values[3]
                    })
                    .sum::<F192>()
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
                // The third fused tree is the count tree, in `K`, against the same values in `E`.
                let count: Vec<F64> = (0..three[2]).map(|i| F64((0x9e37_79b9 * i + 1) as u64)).collect();
                let mut reference = [
                    tree(three[0]),
                    tree(three[1]),
                    QuaternaryLayerState::new(count.iter().map(|&k| k.into()).collect(), width),
                ];
                let mut fused = [
                    tree(three[0]),
                    tree(three[1]),
                    QuaternaryLayerState::new_k(count, width),
                ];
                let point: Vec<F192> = (0..width.ilog2() - 1)
                    .map(|i| F192::new(31 + u64::from(i), 7, 11))
                    .collect();
                let eq = SplitEq::new(&point);
                for (f, r) in fused.iter().zip(&reference) {
                    assert_eq!(f.round_message(&eq), round_message_rows(&r.values, &r.ones, &eq));
                }
                let mut round = 0;
                while reference[0].logical_rows > 2 {
                    round += 1;
                    let challenge = F192::new(reference[0].logical_rows as u64, 13, 19);
                    let eq = SplitEq::new(&point[round..]);
                    let messages = fold_and_message(&mut fused, challenge, &eq);
                    for (r, message) in reference.iter_mut().zip(messages) {
                        r.fold_scalar(challenge);
                        assert_eq!(
                            message,
                            round_message_rows(&r.values, &r.ones, &eq),
                            "width={width}, lens={three:?}"
                        );
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
            let want: Vec<F192> = current.chunks(4).map(|c| c.iter().product()).collect();
            assert_eq!(next_level(&current), want, "len={len}");
        }
    }

    fn product(lane: &[F192]) -> F192 {
        lane.iter().copied().product()
    }

    /// Rescale lane 1's last leaf so its product matches lane 0's, as the bus's two sides do.
    fn balance(leaves: &mut [Vec<F192>; 3]) {
        let last = leaves[1].len() - 1;
        leaves[1][last] = F192::ONE;
        leaves[1][last] = product(&leaves[0]) * product(&leaves[1]).inv();
    }

    /// Lane 2 is the count tree, so its leaves must be `K` values.
    fn prove_lanes(leaves: &[Vec<F192>; 3], ps: &mut ProverState) -> ProductTriple {
        let count = leaves[2]
            .iter()
            .map(|v| v.as_base().expect("a count is in K"))
            .collect();
        prove_product_triple(
            [Leaves::new(leaves[0].clone()), Leaves::new(leaves[1].clone())],
            Leaves::new(count),
            ps,
        )
    }

    /// A count leaf: `K`-valued.
    fn count_leaf(row: usize, salt: usize) -> F192 {
        F192::new((1 + row * 7 + salt) as u64 * 0x9e37_79b9, 0, 0)
    }

    #[test]
    fn radix_four_claims_are_true_at_even_and_odd_depths() {
        for mu in 0..=10 {
            let mut leaves: [Vec<F192>; 3] = [0, 1, 2].map(|lane| {
                (0..1usize << mu)
                    .map(|row| match lane {
                        2 => count_leaf(row, mu),
                        _ => F192::new((1 + row + lane * 100_003) as u64, row as u64, lane as u64),
                    })
                    .collect()
            });
            balance(&mut leaves);
            let mut ps = ProverState::from_label(b"radix-four-gkr-test");
            let proved = prove_lanes(&leaves, &mut ps);
            let stream = ps.into_proof().stream;
            assert_eq!(stream[..2], [product(&leaves[0]), product(&leaves[2])]);
            for lane in 0..3 {
                assert_eq!(proved.values[lane], mle_eval_e(&leaves[lane], &proved.point));
            }
        }
    }

    #[test]
    fn implicit_identity_suffix_matches_dense_padding() {
        for mu in 3..=10 {
            let lengths = [(1usize << mu) - 3, (1usize << (mu - 1)) + 1, (1usize << (mu - 2)) + 3];
            let mut leaves: [Vec<F192>; 3] = std::array::from_fn(|lane| {
                (0..lengths[lane])
                    .map(|row| match lane {
                        2 => count_leaf(row, 3),
                        _ => F192::new((3 + row + lane * 10_007) as u64, row as u64, lane as u64),
                    })
                    .collect()
            });
            balance(&mut leaves);
            let dense = leaves.each_ref().map(|lane| {
                let mut padded = lane.clone();
                padded.resize(1 << mu, F192::ONE);
                padded
            });
            let mut sparse_ps = ProverState::from_label(b"sparse-radix-four-gkr-test");
            let proved = prove_lanes(&leaves, &mut sparse_ps);
            for lane in 0..3 {
                assert_eq!(proved.values[lane], mle_eval_e(&dense[lane], &proved.point));
            }
            let proof = sparse_ps.into_proof();
            assert_eq!(proof.stream[..2], [product(&dense[0]), product(&dense[2])]);
            let mut dense_ps = ProverState::from_label(b"sparse-radix-four-gkr-test");
            let dense_proved = prove_lanes(&dense, &mut dense_ps);
            assert_eq!(dense_proved.point, proved.point);
            assert_eq!(dense_proved.values, proved.values);
            assert_eq!(dense_ps.into_proof().stream, proof.stream);
        }
    }
}
