//! Hotwire's index side: the rounds over the index `j` of cycles, memory cells and instructions, lowest bit
//! first, each of degree 2.
//!
//! The summand is a sum of terms `coef·A(j)·B(j)` and `coef·A(j)` over arrays. An array stores its first entries
//! and has a closed form past them ([`Tail`]): zero for an array the pointers scatter, and the index's power or `eq`
//! and its shift by one for the tables that pair with them. A pair of entries of a term is summed only where both of
//! its arrays can be nonzero, so a table need only be stored as far as its partner reaches.

use super::at;
use super::pointer::{Chunks, NO_INDEX};
use primitives::field::{F64, F128, F128Unreduced, adjacent_products, fold_adjacent};
use std::mem::MaybeUninit;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};

/// Rows ahead that a scatter prefetches its target.
const PREFETCH: usize = 16;

/// Pairs per task of a round.
const TASK_PAIRS: usize = 1 << 12;

/// Rows per task of a scatter, and indices per range of a sorted one.
const SCATTER_TASK: usize = 1 << 12;

/// Rows whose weights a scatter computes together, before it adds them.
const ROW_BLOCK: usize = 128;

/// The owners of a [`Scatter`]'s entries when the workers' adds outside their own ranges are made, each of every
/// `OWNERS`-th stripe of `2^STRIPE_BITS` entries.
const OWNERS: usize = 16;
const STRIPE_BITS: usize = 4;

/// Entries per task of a plain pass over an array: zeroing it, or finding its last nonzero entry.
const BLOCK: usize = 1 << 16;

/// One term of the summand, over arrays named by position.
#[derive(Clone, Copy, Debug)]
pub enum Term {
    Product { coef: F128, a: usize, b: usize },
    Single { coef: F128, a: usize },
}

/// What the index side ends at: the point `r`, every array's value there, and the claim the last round leaves.
pub struct IndexEnd {
    pub point: Vec<F128>,
    pub values: Vec<F128>,
    pub claim: F128,
}

/// What an array holds past its stored entries, at index `j` over the variables still unbound.
#[derive(Clone, Debug)]
pub enum Tail {
    Zero,
    /// `c·ratio^j`.
    Powers {
        c: F128,
        ratio: F64,
    },
    /// `a·eq(point, j) + b·eq(point, j + 1)`, the point lowest variable first.
    Eq(ShiftEq),
}

/// `eq(point, j)` as the product of two small tables, `eq` of the low half of the point's variables at `j`'s low
/// bits and of the high half at its high bits, so an array that is all tail costs no memory and no fold.
#[derive(Clone, Debug)]
struct SplitEq {
    point: Vec<F128>,
    /// The variables `low` covers.
    bits: usize,
    low: Vec<F128>,
    high: Vec<F128>,
}

impl SplitEq {
    fn new(point: Vec<F128>) -> Self {
        let bits = point.len().div_ceil(2);
        let low = primitives::multilinear::eq_table_serial(&point[..bits]);
        let high = primitives::multilinear::eq_table_serial(&point[bits..]);
        Self { point, bits, low, high }
    }

    /// The value at `j`, whose bits past the point's are ignored.
    #[inline(always)]
    fn at(&self, j: usize) -> F128 {
        self.low[j & (self.low.len() - 1)] * self.high[(j >> self.bits) & (self.high.len() - 1)]
    }
}

/// `a·eq(point, j) + b·eq(point, j + 1)`, the second term dropped at the top index: `eq(ζ, ·)` and its shift by one
/// together, which binding the lowest variable keeps in this form. A pair of entries `2i, 2i + 1` shares `eq`'s high
/// table entry with the pair's low-table values `pairs[i]`, but for the term of a run's last pair that reaches the
/// next run's first entry.
#[derive(Clone, Debug)]
pub struct ShiftEq {
    a: F128,
    b: F128,
    eq: SplitEq,
    pairs: Vec<[F128; 2]>,
}

impl ShiftEq {
    pub fn new(a: F128, b: F128, point: Vec<F128>) -> Self {
        let eq = SplitEq::new(point);
        let low = &eq.low;
        let pairs = (0..low.len() / 2)
            .map(|i| {
                let next = low.get(2 * i + 2).map_or(F128::ZERO, |&e| b * e);
                [a * low[2 * i] + b * low[2 * i + 1], a * low[2 * i + 1] + next]
            })
            .collect();
        Self { a, b, eq, pairs }
    }

    #[inline(always)]
    fn at(&self, j: usize) -> F128 {
        let next = if j + 1 < 1 << self.eq.point.len() {
            self.b * self.eq.at(j + 1)
        } else {
            F128::ZERO
        };
        self.a * self.eq.at(j) + next
    }

    /// Bound the lowest variable at `x`: `eq(z, 2j' + 1) = z_0·eq(z', j')` and `eq(z, 2j' + 2) = (1 + z_0)·eq(z', j' + 1)`.
    fn fold(&self, x: F128) -> Self {
        let z = self.eq.point[0];
        Self::new(
            self.a * (F128::ONE + z + x) + self.b * z * (F128::ONE + x),
            self.b * x * (F128::ONE + z),
            self.eq.point[1..].to_vec(),
        )
    }
}

impl Tail {
    #[inline(never)]
    fn at(&self, j: usize) -> F128 {
        match self {
            Self::Zero => F128::ZERO,
            Self::Powers { c, ratio } => c.mul_base(ratio.pow(j as u128)),
            Self::Eq(eq) => eq.at(j),
        }
    }

    /// The tail once the lowest variable is bound at `x`.
    fn fold(&self, x: F128) -> Self {
        match self {
            Self::Zero => Self::Zero,
            Self::Powers { c, ratio } => Self::Powers {
                c: *c * (F128::ONE + x.mul_base(F64::ONE + *ratio)),
                ratio: ratio.square(),
            },
            Self::Eq(eq) => Self::Eq(eq.fold(x)),
        }
    }
}

/// An array of the summand: its stored entries, then its tail.
pub struct Array {
    pub head: Vec<F128>,
    pub tail: Tail,
}

impl From<Vec<F128>> for Array {
    fn from(head: Vec<F128>) -> Self {
        Self { head, tail: Tail::Zero }
    }
}

impl Array {
    /// The indices, of `size`, where it can be nonzero.
    fn len(&self, size: usize) -> usize {
        match self.tail {
            Tail::Zero => self.head.len(),
            _ => size,
        }
    }

    fn get(&self, j: usize) -> F128 {
        self.head.get(j).copied().unwrap_or_else(|| self.tail.at(j))
    }
}

/// The pairs a round sums, given where each array can be nonzero.
fn task_pairs(lens: &[usize], terms: &[Term]) -> usize {
    (terms.iter())
        .map(|&t| match t {
            Term::Product { a, b, .. } => lens[a].min(lens[b]),
            Term::Single { a, .. } => lens[a],
        })
        .max()
        .unwrap_or(0)
        .div_ceil(2)
}

/// A task's entries of an array, from index `offset`.
#[derive(Clone, Copy)]
struct View<'a> {
    head: &'a [F128],
    offset: usize,
    /// The indices from `offset` where the array can be nonzero.
    len: usize,
    tail: &'a Tail,
}

impl View<'_> {
    #[inline(always)]
    fn at(&self, i: usize) -> F128 {
        match self.head.get(i) {
            Some(&v) => v,
            None => self.tail.at(self.offset + i),
        }
    }

    /// The `eq` of an array that is all `eq` tail.
    #[inline(always)]
    fn eq(&self) -> Option<&ShiftEq> {
        match self.tail {
            Tail::Eq(eq) if self.head.is_empty() && eq.eq.bits > 0 => Some(eq),
            _ => None,
        }
    }

    /// The pairs read from the stored entries alone.
    #[inline(always)]
    fn stored_pairs(&self) -> usize {
        match self.tail {
            Tail::Zero => self.head.len().div_ceil(2),
            _ => self.head.len() / 2,
        }
    }
}

/// A product term's sums over the pairs `k` in `pairs` of `other` and an array that is all `eq` tail: the pairs that
/// share `j`'s high bits take `pairs` of the low table alone, one product by the high table's entry per run, and the
/// run's last pair the shifted term that reaches the next run.
#[inline(always)]
fn add_eq_product(acc: &mut [F128Unreduced; 3], shift: &ShiftEq, other: View, pairs: std::ops::Range<usize>) {
    let eq = &shift.eq;
    let mask = (1 << eq.bits) - 1;
    let n = 1usize << eq.point.len();
    let mut k = pairs.start;
    while k < pairs.end {
        // `bits ≥ 1` and `offset` is even, so a pair never crosses a run.
        let j = other.offset + 2 * k;
        let next_run = k + ((mask + 1) - (j & mask)) / 2;
        let run = pairs.end.min(next_run);
        // The run's pairs that `other` stores whole, then the rest.
        let (first, full) = (
            ((other.offset + 2 * k) & mask) / 2,
            run.min((other.head.len() / 2).max(k)),
        );
        let mut sums = [F128Unreduced::ZERO; 3];
        if full > k {
            sums = adjacent_products(
                &shift.pairs.as_flattened()[2 * first..2 * (first + full - k)],
                &other.head[2 * k..2 * full],
            );
        }
        for k in full..run {
            let [p0, p1] = shift.pairs[((other.offset + 2 * k) & mask) / 2];
            let (o0, o1) = (other.at(2 * k), other.at(2 * k + 1));
            sums[0] ^= p0.mul_unreduced(o0);
            sums[1] ^= p1.mul_unreduced(o1);
            sums[2] ^= (p0 + p1).mul_unreduced(o0 + o1);
        }
        let h = eq.high[j >> eq.bits];
        for (a, s) in acc.iter_mut().zip(sums) {
            *a ^= s.reduce().mul_unreduced(h);
        }
        let across = other.offset + 2 * run;
        if run == next_run && across < n && !shift.b.is_zero() {
            let extra = shift.b * eq.low[0] * eq.high[across >> eq.bits];
            let (o0, o1) = (other.at(2 * run - 2), other.at(2 * run - 1));
            acc[1] ^= extra.mul_unreduced(o1);
            acc[2] ^= extra.mul_unreduced(o0 + o1);
        }
        k = run;
    }
}

/// Each term's sums over a task's pairs: `A·B` at `X = 0`, `1` and `∞` for a product (unreduced), `A` at `0` and `1`
/// for a single.
struct Sums {
    products: Vec<[F128Unreduced; 3]>,
    singles: Vec<[F128; 2]>,
}

impl Sums {
    fn new(terms: &[Term]) -> Self {
        let n_products = terms.iter().filter(|t| matches!(t, Term::Product { .. })).count();
        Self {
            products: vec![[F128Unreduced::ZERO; 3]; n_products],
            singles: vec![[F128::ZERO; 2]; terms.len() - n_products],
        }
    }

    /// Add the terms over the pairs `k` in `range` of `arrays`.
    #[inline(always)]
    fn add(&mut self, terms: &[Term], arrays: &[View], range: std::ops::Range<usize>) {
        let (mut p, mut q) = (0, 0);
        for &term in terms {
            match term {
                Term::Product { a, b, .. } => {
                    let (a, b) = (arrays[a], arrays[b]);
                    let end = range.end.min(a.len.div_ceil(2)).min(b.len.div_ceil(2)).max(range.start);
                    let acc = &mut self.products[p];
                    p += 1;
                    if let Some((eq, other)) = (a.eq().map(|e| (e, b))).or_else(|| b.eq().map(|e| (e, a))) {
                        add_eq_product(acc, eq, other, range.start..end);
                        continue;
                    }
                    let stored = end.min(a.stored_pairs()).min(b.stored_pairs()).max(range.start);
                    let (ah, bh) = (a.head, b.head);
                    // The pairs both store whole, then the rest.
                    let full = stored.min(ah.len() / 2).min(bh.len() / 2).max(range.start);
                    if full > range.start {
                        let sums = adjacent_products(&ah[2 * range.start..2 * full], &bh[2 * range.start..2 * full]);
                        for (a, s) in acc.iter_mut().zip(sums) {
                            *a ^= s;
                        }
                    }
                    for k in full..stored {
                        let (a0, a1, b0, b1) = (ah[2 * k], at(ah, 2 * k + 1), bh[2 * k], at(bh, 2 * k + 1));
                        acc[0] ^= a0.mul_unreduced(b0);
                        acc[1] ^= a1.mul_unreduced(b1);
                        acc[2] ^= (a0 + a1).mul_unreduced(b0 + b1);
                    }
                    for k in stored..end {
                        let (a0, a1, b0, b1) = (a.at(2 * k), a.at(2 * k + 1), b.at(2 * k), b.at(2 * k + 1));
                        acc[0] ^= a0.mul_unreduced(b0);
                        acc[1] ^= a1.mul_unreduced(b1);
                        acc[2] ^= (a0 + a1).mul_unreduced(b0 + b1);
                    }
                }
                Term::Single { a, .. } => {
                    let end = range.end.min(arrays[a].len.div_ceil(2)).max(range.start);
                    let acc = &mut self.singles[q];
                    for k in range.start..end {
                        acc[0] += arrays[a].at(2 * k);
                        acc[1] += arrays[a].at(2 * k + 1);
                    }
                    q += 1;
                }
            }
        }
    }

    fn combine(mut self, other: Self) -> Self {
        for (x, y) in self.products.iter_mut().zip(other.products) {
            for (x, y) in x.iter_mut().zip(y) {
                *x ^= y;
            }
        }
        for (x, y) in self.singles.iter_mut().zip(other.singles) {
            x[0] += y[0];
            x[1] += y[1];
        }
        self
    }

    /// The round polynomial's coefficients.
    fn poly(self, terms: &[Term]) -> [F128; 3] {
        let mut poly = [F128::ZERO; 3];
        let (mut products, mut singles) = (self.products.into_iter(), self.singles.into_iter());
        for &term in terms {
            match term {
                Term::Product { coef, .. } => {
                    let [lo, hi, mixed] = products.next().expect("a product's sums").map(F128Unreduced::reduce);
                    poly[0] += coef * lo;
                    poly[1] += coef * (hi + lo + mixed);
                    poly[2] += coef * mixed;
                }
                Term::Single { coef, .. } => {
                    let [lo, hi] = singles.next().expect("a single's sums");
                    poly[0] += coef * lo;
                    poly[1] += coef * (lo + hi);
                }
            }
        }
        poly
    }
}

/// The first round's polynomial, over `size` indices.
fn first_round(arrays: &[Array], terms: &[Term], size: usize) -> [F128; 3] {
    let views: Vec<View> = (arrays.iter())
        .map(|a| View {
            head: &a.head,
            offset: 0,
            len: a.len(size),
            tail: &a.tail,
        })
        .collect();
    let lens: Vec<usize> = views.iter().map(|v| v.len).collect();
    parallel::fold_reduce(
        task_pairs(&lens, terms).div_ceil(TASK_PAIRS),
        || Sums::new(terms),
        |acc, task| acc.add(terms, &views, task * TASK_PAIRS..(task + 1) * TASK_PAIRS),
        Sums::combine,
    )
    .poly(terms)
}

/// Bind the lowest variable of every array, of `size` indices, at `x`, and sum the next round's polynomial, in one
/// pass: a task folds its range of every array and sums the terms over it while it is in cache.
fn fold_round(arrays: &[Array], terms: &[Term], x: F128, size: usize) -> (Vec<Array>, [F128; 3]) {
    let half = size / 2;
    let tails: Vec<Tail> = arrays.iter().map(|a| a.tail.fold(x)).collect();
    let lens: Vec<usize> = arrays.iter().map(|a| a.head.len().div_ceil(2)).collect();
    let mut out: Vec<Vec<MaybeUninit<F128>>> = lens.iter().map(|&n| primitives::uninit_vec(n)).collect();
    let ptrs: Vec<parallel::SendPtr<MaybeUninit<F128>>> =
        out.iter_mut().map(|o| parallel::SendPtr(o.as_mut_ptr())).collect();
    let summed: Vec<usize> = (lens.iter().zip(&tails))
        .map(|(&n, tail)| if matches!(tail, Tail::Zero) { n } else { half })
        .collect();
    let pairs = (lens.iter().map(|n| n.div_ceil(2)).max().unwrap_or(0)).max(task_pairs(&summed, terms));
    let sums = parallel::fold_reduce(
        pairs.div_ceil(TASK_PAIRS),
        || Sums::new(terms),
        |acc, task| {
            let range = task * TASK_PAIRS..(task + 1) * TASK_PAIRS;
            let offset = 2 * range.start;
            let views: Vec<View> = (arrays.iter().zip(&tails))
                .zip(ptrs.iter().zip(&lens))
                .map(|((a, tail), (ptr, &n))| {
                    let (lo, hi) = (offset.min(n), (2 * range.end).min(n));
                    // SAFETY: entries `lo..hi` of this array are this task's alone.
                    let dst = unsafe { std::slice::from_raw_parts_mut(ptr.0.add(lo), hi - lo) };
                    // The outputs of whole stored pairs, then the last one's, which can take its second from the tail.
                    let full = (a.head.len() / 2).clamp(lo, hi);
                    let (whole, rest) = dst.split_at_mut(full - lo);
                    if full > lo {
                        fold_adjacent(whole, &a.head[2 * lo..2 * full], x);
                    }
                    for (j, o) in rest.iter_mut().enumerate() {
                        let i = 2 * (full + j);
                        let (a0, a1) = (
                            a.head[i],
                            a.head.get(i + 1).copied().unwrap_or_else(|| a.tail.at(i + 1)),
                        );
                        o.write(a0 + x * (a0 + a1));
                    }
                    // SAFETY: the loop above wrote every entry.
                    let dst = unsafe { dst.assume_init_mut() };
                    let len = match tail {
                        Tail::Zero => dst.len(),
                        _ => half.saturating_sub(offset),
                    };
                    View {
                        head: dst,
                        offset,
                        len,
                        tail,
                    }
                })
                .collect();
            // The views start at the task's first pair.
            acc.add(terms, &views, 0..TASK_PAIRS);
        },
        Sums::combine,
    );
    let arrays = out
        .into_iter()
        // SAFETY: task `t` wrote entries `2t·TASK_PAIRS..2(t + 1)·TASK_PAIRS` of each array, and the tasks reach every
        // entry: `pairs ≥ ⌈n/2⌉` for each array's `n` entries.
        .map(|head| unsafe { primitives::assume_init_vec(head) })
        .zip(tails)
        .map(|(head, tail)| Array { head, tail })
        .collect();
    (arrays, sums.poly(terms))
}

/// The index side over `n_vars` variables. `round` takes each round polynomial's coefficients and returns the
/// challenge.
pub fn prove(
    n_vars: usize,
    mut arrays: Vec<Array>,
    terms: &[Term],
    round: &mut dyn FnMut(&[F128]) -> F128,
) -> IndexEnd {
    assert!(
        arrays.iter().all(|a| a.head.len() <= 1 << n_vars),
        "an array past 2^{n_vars}"
    );
    let mut size = 1usize << n_vars;
    let mut point = Vec::with_capacity(n_vars);
    let mut claim = None;
    let mut poly = first_round(&arrays, terms, size);
    for _ in 0..n_vars {
        debug_assert!(claim.is_none_or(|c: F128| c == poly[1] + poly[2]));
        let x = round(&poly);
        claim = Some(primitives::multilinear::poly_eval(&poly, x));
        (arrays, poly) = fold_round(&arrays, terms, x, size);
        size /= 2;
        point.push(x);
    }
    let values: Vec<F128> = arrays.iter().map(|a| a.get(0)).collect();
    let last = terms
        .iter()
        .map(|&term| match term {
            Term::Product { coef, a, b } => coef * values[a] * values[b],
            Term::Single { coef, a } => coef * values[a],
        })
        .sum();
    debug_assert!(claim.is_none_or(|c| c == last));
    IndexEnd {
        point,
        values,
        claim: last,
    }
}

/// An array the pointers of many columns add into at once: two `u64` limbs per entry, added by XOR, laid out
/// as [`F128`] is so the array becomes one without a copy. An index past its length sets `overflow` and adds
/// nothing, so a caller that sized it for the honest indices can redo it at full size.
pub struct Scatter {
    limbs: Vec<AtomicU64>,
    overflow: AtomicBool,
    /// Whether the pool has one worker, so no two adds run at once and an add needs no read-modify-write.
    alone: bool,
}

impl Scatter {
    pub fn new(len: usize) -> Self {
        // SAFETY: every limb is written.
        let limbs = unsafe {
            primitives::filled_vec(2 * len, |limbs| {
                parallel::chunks_mut(limbs, 2 * BLOCK, |_, chunk| {
                    for limb in chunk {
                        limb.write(AtomicU64::new(0));
                    }
                });
            })
        };
        Self {
            limbs,
            overflow: AtomicBool::new(false),
            alone: parallel::num_threads() == 1,
        }
    }

    /// Prefetch entry `j` for writing: the scatters' indices land all over the arrays, and a row's target is known
    /// [`PREFETCH`] rows ahead.
    #[inline(always)]
    fn prefetch(&self, j: usize) {
        let Some(cell) = self.limbs.get(2 * j) else {
            return;
        };
        let at = std::ptr::from_ref(cell);
        // SAFETY: a prefetch never faults and writes nothing.
        #[cfg(target_arch = "aarch64")]
        unsafe {
            std::arch::asm!("prfm pstl1keep, [{0}]", in(reg) at, options(nostack, preserves_flags, readonly));
        }
        // SAFETY: as above.
        #[cfg(target_arch = "x86_64")]
        unsafe {
            std::arch::x86_64::_mm_prefetch::<{ std::arch::x86_64::_MM_HINT_T0 }>(at.cast());
        }
        #[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
        let _ = at;
    }

    /// Whether an index fell past the array.
    pub fn overflowed(&self) -> bool {
        self.overflow.load(Ordering::Relaxed)
    }

    #[inline(always)]
    fn add(&self, j: usize, value: F128) {
        self.add_at(j, value, self.alone);
    }

    /// [`Self::add`] at an entry no other worker adds to meanwhile: no atomic read-modify-write.
    #[inline(always)]
    fn add_owned(&self, j: usize, value: F128) {
        self.add_at(j, value, true);
    }

    /// Add `value` at entry `j`, by a plain read and write if `owned`, else atomically.
    #[inline(always)]
    fn add_at(&self, j: usize, value: F128, owned: bool) {
        let Some(cell) = self.limbs.get(2 * j..2 * j + 2) else {
            self.overflow.store(true, Ordering::Relaxed);
            return;
        };
        for (c, limb) in cell.iter().zip(value.to_limbs()) {
            if owned {
                c.store(c.load(Ordering::Relaxed) ^ limb, Ordering::Relaxed);
            } else if limb != 0 {
                c.fetch_xor(limb, Ordering::Relaxed);
            }
        }
    }

    /// [`Scatter::add_repeated_words`] of several tables' words into several arrays in one pass: row `u` of table `t` adds
    /// its weight for target `a` at its index plus `targets[a].1` in `targets[a].0`, where `weights(t, rows, out)` writes
    /// the weights of `rows` for target `a` in `out[a]`. A task takes a range of indices and,
    /// from each table, the rows from the first whose index reaches the range to the first past it, so for words
    /// sorted by index, such as each table's cycles, a task's adds stay in its own stretch of every array and each
    /// array is swept once rather than once a table. Any order of words still adds each row once.
    pub fn add_sorted_words_to<const K: usize>(
        chunks: &Chunks,
        tables: &[(&[u64], &[u32])],
        targets: [(&Scatter, usize); K],
        weights: impl Fn(usize, std::ops::Range<usize>, [&mut [F128]; K]) + Sync,
    ) {
        for &(words, index) in tables {
            assert_eq!(index.len(), words.len(), "an index per word");
        }
        let len = targets
            .iter()
            .map(|(array, _)| array.limbs.len() / 2)
            .max()
            .unwrap_or(0);
        let ranges = len.div_ceil(SCATTER_TASK).max(1);
        // Each table's first row per range, kept nondecreasing so the ranges split its rows whatever their order.
        let starts: Vec<Vec<usize>> = (tables.iter())
            .map(|&(_, index)| {
                let mut starts: Vec<usize> = (0..ranges)
                    .map(|r| index.partition_point(|&j| (j as usize) < r * SCATTER_TASK))
                    .chain([index.len()])
                    .collect();
                starts[0] = 0;
                for r in 1..=ranges {
                    starts[r] = starts[r].max(starts[r - 1]);
                }
                starts
            })
            .collect();
        // A task owns its range's entries and adds there without atomics; a one-hot word's add outside it (a shifted
        // index past its end, or an unsorted word's) waits until every task is done. A word that is not one-hot, which
        // can have any number of indices, adds at each of them atomically once no task adds without atomics.
        let (foreign, not_one_hot): (Vec<_>, Vec<_>) = parallel::map_collect(ranges, |r| {
            let own = r * SCATTER_TASK..(r + 1) * SCATTER_TASK;
            let (mut foreign, mut not_one_hot) = (Vec::new(), Vec::new());
            let mut block = [[F128::ZERO; ROW_BLOCK]; K];
            for (t, &(words, index)) in tables.iter().enumerate() {
                let rows = starts[t][r]..starts[t][r + 1];
                // Words sorted by index, as the callers pass, read each array in order, so the rows need no prefetch.
                for first in rows.clone().step_by(ROW_BLOCK) {
                    let some = first..rows.end.min(first + ROW_BLOCK);
                    weights(t, some.clone(), block.each_mut().map(|b| &mut b[..some.len()]));
                    for u in some {
                        let j = index[u];
                        if j == NO_INDEX {
                            // A word with a chunk of no bit set has no index.
                            if (0..chunks.d()).all(|i| chunks.bits(words[u], i) != 0) {
                                not_one_hot.push((t, u));
                            }
                            continue;
                        }
                        for (a, (&(array, shift), w)) in targets.iter().zip(&block).enumerate() {
                            let w = w[u - first];
                            if let Some(j) = chunks.shifted(j as usize, shift).filter(|_| !w.is_zero()) {
                                if own.contains(&j) {
                                    array.add_owned(j, w);
                                } else {
                                    foreign.push((a, j, w));
                                }
                            }
                        }
                    }
                }
            }
            (foreign, not_one_hot)
        })
        .into_iter()
        .unzip();
        for (a, j, w) in foreign.into_iter().flatten() {
            targets[a].0.add_owned(j, w);
        }
        let not_one_hot: Vec<(usize, usize)> = not_one_hot.into_iter().flatten().collect();
        if !not_one_hot.is_empty() {
            parallel::for_each(not_one_hot.len(), |k| {
                let (t, u) = not_one_hot[k];
                let mut w = [[F128::ZERO; 1]; K];
                weights(t, u..u + 1, w.each_mut().map(|w| &mut w[..]));
                let w = w.map(|[w]| w);
                chunks.indices(tables[t].0[u], &mut |j| {
                    for (&(array, shift), &w) in targets.iter().zip(&w) {
                        if let Some(j) = chunks.shifted(j, shift).filter(|_| !w.is_zero()) {
                            array.add(j, w);
                        }
                    }
                });
            });
        }
    }

    /// Add each row's weight at the index of its word plus `shift`, where `weights(rows, out)` writes the weights of
    /// `rows` in `out`, dropping an index whose shift leaves its window
    /// ([`Chunks::shifted`]), with `index` the words' indices ([`Chunks::decode_all`]). A word whose chunks are not all
    /// one-hot adds at every index of it ([`Chunks::indices`]), which is what the row side's `Φ_s` of that word sums
    /// to.
    ///
    /// For words that repeat, such as instructions: with several workers, each sums the adds to an
    /// index that rows hit again soon after, holding back up to `SLOTS` indices (`Combine`).
    pub fn add_repeated_words<const SLOTS: usize>(
        &self,
        chunks: &Chunks,
        words: &[u64],
        index: &[u32],
        shift: usize,
        weights: impl Fn(std::ops::Range<usize>, &mut [F128]) + Sync,
    ) {
        self.add_repeated_accesses::<SLOTS>(chunks, &[(words, index, shift)], |_, rows, out| weights(rows, out));
    }

    /// [`Scatter::add_repeated_words`] for several pointers into the same rows in one pass: `accesses[a]` is a pointer's words, their indices and its shift, and each row adds its weight
    /// for access `a` at that access's index, where `weights(a, rows, out)` writes the weights of `rows` in `out`.
    pub fn add_repeated_accesses<const SLOTS: usize>(
        &self,
        chunks: &Chunks,
        accesses: &[(&[u64], &[u32], usize)],
        weights: impl Fn(usize, std::ops::Range<usize>, &mut [F128]) + Sync,
    ) {
        // One worker contends with no one, so it adds each row straight in.
        if self.alone {
            self.add_words_with(chunks, accesses, weights, || Direct(self));
        } else {
            self.add_words_with(chunks, accesses, weights, || Combine::<SLOTS>::new(self));
        }
    }

    /// [`Scatter::add_repeated_accesses`] for accesses whose indices follow the rows, such as memory cells written
    /// once and read soon after: each task of rows owns the indices from about its first row's to the next task's, and
    /// adds there without atomics. Its adds elsewhere wait until every task is done.
    pub fn add_local_accesses(
        &self,
        chunks: &Chunks,
        accesses: &[(&[u64], &[u32], usize)],
        weights: impl Fn(usize, std::ops::Range<usize>, &mut [F128]) + Sync,
    ) {
        if self.alone {
            self.add_words_with(chunks, accesses, weights, || Direct(self));
            return;
        }
        let Some(&(first, ..)) = accesses.first() else {
            return;
        };
        let rows = first.len();
        for &(words, index, _) in accesses {
            assert_eq!(words.len(), rows, "a word per row");
            assert_eq!(index.len(), rows, "an index per word");
        }
        let tasks = rows.div_ceil(SCATTER_TASK);
        // Task `t` owns `bounds[t]..bounds[t + 1]`, kept nondecreasing so the ranges never overlap.
        let mut bounds: Vec<usize> = (0..tasks)
            .map(|t| {
                let rows = t * SCATTER_TASK..rows.min((t + 1) * SCATTER_TASK);
                let mut sample: Vec<usize> = (rows.take(4))
                    .flat_map(|u| accesses.iter().map(move |&(_, index, shift)| (index[u], shift)))
                    .filter(|&(j, _)| j != NO_INDEX)
                    .map(|(j, shift)| j as usize + shift)
                    .collect();
                sample.sort_unstable();
                sample.get(sample.len().saturating_sub(1) / 2).copied().unwrap_or(0)
            })
            .chain([usize::MAX])
            .collect();
        bounds[0] = 0;
        for t in 1..=tasks {
            bounds[t] = bounds[t].max(bounds[t - 1]);
        }
        // Each task's adds outside its range, by their owner.
        let foreign: Vec<Vec<Vec<(u32, F128)>>> = parallel::map_collect(tasks, |t| {
            let own = bounds[t]..bounds[t + 1];
            let mut foreign = vec![Vec::new(); OWNERS];
            let task = t * SCATTER_TASK..rows.min((t + 1) * SCATTER_TASK);
            self.add_rows(chunks, accesses, &weights, task, |j, w| {
                if own.contains(&j) {
                    self.add_owned(j, w);
                } else {
                    let key = u32::try_from(j).expect("an index below 2^32");
                    foreign[(j >> STRIPE_BITS) % OWNERS].push((key, w));
                }
            });
            foreign
        });
        parallel::for_each(OWNERS, |o| {
            for f in &foreign {
                let f = &f[o];
                for (k, &(j, w)) in f.iter().enumerate() {
                    if let Some(&(ahead, _)) = f.get(k + PREFETCH) {
                        self.prefetch(ahead as usize);
                    }
                    self.add_owned(j as usize, w);
                }
            }
        });
    }

    fn add_words_with<A: Adder>(
        &self,
        chunks: &Chunks,
        accesses: &[(&[u64], &[u32], usize)],
        weights: impl Fn(usize, std::ops::Range<usize>, &mut [F128]) + Sync,
        adder: impl Fn() -> A + Sync,
    ) {
        let Some(&(first, ..)) = accesses.first() else {
            return;
        };
        let rows = first.len();
        for &(words, index, _) in accesses {
            assert_eq!(words.len(), rows, "a word per row");
            assert_eq!(index.len(), rows, "an index per word");
        }
        parallel::for_each_chunk(rows.div_ceil(SCATTER_TASK), |start, end| {
            let mut adder = adder();
            let rows = start * SCATTER_TASK..rows.min(end * SCATTER_TASK);
            self.add_rows(chunks, accesses, &weights, rows, |j, w| adder.add(j, w));
            adder.flush();
        });
    }

    /// Weigh `rows` a block at a time and pass each nonzero add, its index and weight, to `add`.
    #[inline(always)]
    fn add_rows(
        &self,
        chunks: &Chunks,
        accesses: &[(&[u64], &[u32], usize)],
        weights: &impl Fn(usize, std::ops::Range<usize>, &mut [F128]),
        rows: std::ops::Range<usize>,
        mut add: impl FnMut(usize, F128),
    ) {
        let mut block = vec![[F128::ZERO; ROW_BLOCK]; accesses.len()];
        for first in rows.clone().step_by(ROW_BLOCK) {
            let some = first..rows.end.min(first + ROW_BLOCK);
            for (a, w) in block.iter_mut().enumerate() {
                weights(a, some.clone(), &mut w[..some.len()]);
            }
            for u in some {
                for (a, &(words, index, shift)) in accesses.iter().enumerate() {
                    if let Some(&j) = index.get(u + PREFETCH)
                        && j != NO_INDEX
                    {
                        self.prefetch(j as usize + shift);
                    }
                    let w = block[a][u - first];
                    if w.is_zero() {
                        continue;
                    }
                    let mut add = |j: usize| {
                        if let Some(j) = chunks.shifted(j, shift) {
                            add(j, w);
                        }
                    };
                    match index[u] {
                        NO_INDEX => chunks.indices(words[u], &mut add),
                        j => add(j as usize),
                    }
                }
            }
        }
    }

    /// The entries, without the trailing zeros.
    pub fn into_vec(self) -> Vec<F128> {
        let mut limbs = std::mem::ManuallyDrop::new(self.limbs);
        let (len, cap) = (limbs.len() / 2, limbs.capacity());
        assert_eq!(cap % 2, 0);
        const _: () =
            assert!(align_of::<AtomicU64>() == align_of::<F128>() && 2 * size_of::<AtomicU64>() == size_of::<F128>());
        // SAFETY: `F128` is `repr(C)` over two `u64` limbs in this order, and `AtomicU64` has `u64`'s in-memory
        // representation; the allocation's size and alignment match `cap / 2` of `F128` (asserted above).
        let mut out: Vec<F128> = unsafe { Vec::from_raw_parts(limbs.as_mut_ptr().cast(), len, cap / 2) };
        // The last nonzero entry, each task searching one block from its end.
        let block = BLOCK;
        let last = parallel::map_reduce(
            len.div_ceil(block),
            || 0,
            |b| {
                let start = b * block;
                let tail = &out[start..len.min(start + block)];
                tail.iter().rposition(|v| !v.is_zero()).map_or(0, |j| start + j + 1)
            },
            usize::max,
        );
        out.truncate(last);
        out
    }
}

/// Where a worker of [`Scatter::add_words_with`] sends its adds.
trait Adder {
    fn add(&mut self, j: usize, value: F128);
    fn flush(self);
}

/// Each add straight into the [`Scatter`].
struct Direct<'a>(&'a Scatter);

impl Adder for Direct<'_> {
    #[inline(always)]
    fn add(&mut self, j: usize, value: F128) {
        self.0.add(j, value);
    }

    fn flush(self) {}
}

/// The adds of one worker into a [`Scatter`], with the latest index at each of `N` slots (by its low bits) held
/// back and summed: an index that rows hit again soon after, such as a loop's instruction, takes one atomic add per run of hits instead of one per row, and the workers no longer contend
/// for its cache line.
struct Combine<'a, const N: usize> {
    scatter: &'a Scatter,
    keys: Box<[u32; N]>,
    values: Box<[F128; N]>,
}

impl<'a, const N: usize> Combine<'a, N> {
    fn new(scatter: &'a Scatter) -> Self {
        Self {
            scatter,
            keys: vec![u32::MAX; N].into_boxed_slice().try_into().unwrap(),
            values: vec![F128::ZERO; N].into_boxed_slice().try_into().unwrap(),
        }
    }
}

impl<const N: usize> Adder for Combine<'_, N> {
    #[inline(always)]
    fn add(&mut self, j: usize, value: F128) {
        let slot = j % N;
        let key = u32::try_from(j).expect("an index below 2^32");
        if self.keys[slot] == key {
            self.values[slot] += value;
            return;
        }
        if self.keys[slot] != u32::MAX {
            self.scatter.add(self.keys[slot] as usize, self.values[slot]);
        }
        self.keys[slot] = key;
        self.values[slot] = value;
    }

    /// Add what is held back.
    fn flush(self) {
        for (&key, &value) in self.keys.iter().zip(self.values.iter()) {
            if key != u32::MAX {
                self.scatter.add(key as usize, value);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::pointer::{ChunkEq, Shifts, eval_chunk};
    use super::*;
    use primitives::field::F64;
    use primitives::multilinear::{eq_table, poly_eval};
    use primitives::test_rng::Rng;

    fn mle(a: &[F128], point: &[F128]) -> F128 {
        eq_table(point).iter().zip(a).map(|(&e, &v)| e * v).sum()
    }

    #[test]
    fn a_scatter_flags_an_index_past_its_length() {
        let chunks = Chunks::new(9);
        let words: Vec<u64> = [3, 7, 2].iter().map(|&s| chunks.encode(s)).collect();
        let fits = Scatter::new(8);
        let index = chunks.decode_all(&words);
        fits.add_repeated_words::<1>(&chunks, &words, &index, 0, |_, out| out.fill(F128::ONE));
        assert!(!fits.overflowed());
        let short = Scatter::new(7);
        short.add_repeated_words::<1>(&chunks, &words, &index, 0, |_, out| out.fill(F128::ONE));
        assert!(short.overflowed());
        assert_eq!(short.into_vec(), [0, 0, 1, 1].map(|b| F128::new(b, 0)));
    }

    #[test]
    fn index_side_matches_the_naive_sum_and_end() {
        let mut rng = Rng::new(0x1d5);
        let n = 9;
        let lens = [512usize, 300, 1, 0, 37, 512, 2, 257];
        let arrays: Vec<Vec<F128>> = lens.iter().map(|&l| rng.ext_vec(l)).collect();
        let terms = [
            Term::Product {
                coef: rng.ext(),
                a: 0,
                b: 1,
            },
            Term::Product {
                coef: rng.ext(),
                a: 2,
                b: 1,
            },
            Term::Product {
                coef: rng.ext(),
                a: 3,
                b: 0,
            },
            Term::Product {
                coef: rng.ext(),
                a: 4,
                b: 5,
            },
            Term::Product {
                coef: rng.ext(),
                a: 6,
                b: 7,
            },
            Term::Product {
                coef: rng.ext(),
                a: 7,
                b: 7,
            },
            Term::Single { coef: rng.ext(), a: 2 },
            Term::Single { coef: rng.ext(), a: 7 },
        ];
        let value = |values: &dyn Fn(usize) -> F128| -> F128 {
            terms
                .iter()
                .map(|&t| match t {
                    Term::Product { coef, a, b } => coef * values(a) * values(b),
                    Term::Single { coef, a } => coef * values(a),
                })
                .sum()
        };
        let mut claim: F128 = (0..1 << n).map(|j| value(&|a| at(&arrays[a], j))).sum();
        let end = prove(
            n,
            arrays.iter().cloned().map(Array::from).collect(),
            &terms,
            &mut |poly| {
                assert_eq!(poly.len(), 3);
                assert_eq!(claim, poly[1] + poly[2], "a round's sum");
                let x = rng.ext();
                claim = poly_eval(poly, x);
                x
            },
        );
        assert_eq!(claim, end.claim);
        for (a, &v) in arrays.iter().zip(&end.values) {
            assert_eq!(mle(a, &end.point), v);
        }
        assert_eq!(end.claim, value(&|a| end.values[a]));
    }

    /// Scattering several tables' words by index range adds what scattering each table's words alone adds, whether
    /// the words are sorted, shuffled or not one-hot.
    #[test]
    fn sorted_scatter_adds_each_row_once() {
        let mut rng = Rng::new(0x50d);
        let chunks = Chunks::new(14);
        let top = 1usize << chunks.width;
        let tables: Vec<Vec<u64>> = (0..3)
            .map(|t| {
                let mut sigmas: Vec<usize> = (0..5000 + 1000 * t).map(|_| rng.next_u64() as usize % top).collect();
                if t != 1 {
                    sigmas.sort_unstable();
                }
                (sigmas.iter().enumerate())
                    .map(|(u, &s)| {
                        let word = chunks.encode(s);
                        if t == 2 && u % 97 == 0 {
                            word | rng.next_u64() & rng.next_u64()
                        } else {
                            word
                        }
                    })
                    .collect()
            })
            .collect();
        let indices: Vec<Vec<u32>> = tables.iter().map(|w| chunks.decode_all(w)).collect();
        let weights: Vec<Vec<[F128; 2]>> = (tables.iter())
            .map(|w| w.iter().map(|_| [rng.ext(), rng.ext()]).collect())
            .collect();
        for len in [top, 3000] {
            let (a, b) = (Scatter::new(len), Scatter::new(len));
            let words: Vec<(&[u64], &[u32])> = tables.iter().zip(&indices).map(|(w, i)| (&w[..], &i[..])).collect();
            Scatter::add_sorted_words_to(&chunks, &words, [(&a, 1), (&b, 0)], |t, rows, out| {
                for (i, out) in out.into_iter().enumerate() {
                    for (o, w) in out.iter_mut().zip(&weights[t][rows.clone()]) {
                        *o = w[i];
                    }
                }
            });
            let (c, d) = (Scatter::new(len), Scatter::new(len));
            for (t, (w, i)) in tables.iter().zip(&indices).enumerate() {
                let weights = &weights;
                let column = |k: usize| {
                    move |rows: std::ops::Range<usize>, out: &mut [F128]| {
                        for (o, w) in out.iter_mut().zip(&weights[t][rows]) {
                            *o = w[k];
                        }
                    }
                };
                c.add_repeated_words::<1>(&chunks, w, i, 1, column(0));
                d.add_repeated_words::<1>(&chunks, w, i, 0, column(1));
            }
            assert_eq!(a.overflowed(), c.overflowed());
            assert_eq!(a.into_vec(), c.into_vec(), "length {len}");
            assert_eq!(b.into_vec(), d.into_vec(), "length {len}");
        }
    }

    /// Scattering accesses whose indices mostly follow the rows, by each task's own range, adds what the repeated
    /// scatter adds, whatever the indices: rising, random, past the array or not one-hot.
    #[test]
    fn a_local_scatter_adds_each_row_once() {
        let mut rng = Rng::new(0x10c);
        let chunks = Chunks::new(16);
        let top = 1usize << chunks.width;
        let rows = 20_000;
        let words: Vec<Vec<u64>> = (0..3)
            .map(|a| {
                (0..rows)
                    .map(|u| {
                        let sigma = match (a, u % 7) {
                            (_, 0) => rng.next_u64() as usize % top,
                            (2, _) => rng.next_u64() as usize % 40,
                            _ => (3 * u + rng.next_u64() as usize % 50) % top,
                        };
                        let word = chunks.encode(sigma);
                        if u % 101 == 0 {
                            word | rng.next_u64() & rng.next_u64()
                        } else {
                            word
                        }
                    })
                    .collect()
            })
            .collect();
        let index: Vec<Vec<u32>> = words.iter().map(|w| chunks.decode_all(w)).collect();
        let weights: Vec<Vec<F128>> = (0..3).map(|_| (0..rows).map(|_| rng.ext()).collect()).collect();
        let accesses: Vec<(&[u64], &[u32], usize)> =
            (0..3).map(|a| (&words[a][..], &index[a][..], [0, 1, 5][a])).collect();
        let weigh = |a: usize, rows: std::ops::Range<usize>, out: &mut [F128]| out.copy_from_slice(&weights[a][rows]);
        for len in [top, 50_000] {
            let (local, repeated) = (Scatter::new(len), Scatter::new(len));
            local.add_local_accesses(&chunks, &accesses, weigh);
            repeated.add_repeated_accesses::<4>(&chunks, &accesses, weigh);
            assert_eq!(local.overflowed(), repeated.overflowed());
            assert_eq!(local.into_vec(), repeated.into_vec(), "length {len}");
        }
    }

    /// A scattered array at a point is the sum of its rows' `Φ_s` there, for any words: a read past its window drops
    /// on both sides.
    #[test]
    fn scatter_is_the_row_side_pointer() {
        let mut rng = Rng::new(0x5ca);
        for width in [3usize, 7, 10, 13] {
            let chunks = Chunks::new(width);
            let top = 1usize << width;
            let words: Vec<u64> = (0..300)
                .map(|u| {
                    let sigma = if u % 10 == 0 {
                        top - 1
                    } else {
                        rng.next_u64() as usize % top
                    };
                    let word = chunks.encode(sigma);
                    match u % 9 {
                        0 => word ^ 1 << (rng.next_u32() % 64),
                        1 => word | rng.next_u64() & rng.next_u64(),
                        _ => word,
                    }
                })
                .collect();
            let weights: Vec<F128> = (0..words.len())
                .map(|u| if u % 13 == 0 { F128::ZERO } else { rng.ext() })
                .collect();
            let r = rng.ext_vec(width);
            let eq = ChunkEq::at(&chunks, &r);
            let shifts = Shifts::new(&eq, 12);
            let index = chunks.decode_all(&words);
            for shift in [0, 1, 5, 12] {
                let scatter = Scatter::new(top);
                scatter.add_repeated_words::<1>(&chunks, &words, &index, shift, |rows, out| {
                    out.copy_from_slice(&weights[rows])
                });
                let array = scatter.into_vec();
                let rows: F128 = words
                    .iter()
                    .zip(&weights)
                    .map(|(&w, &weight)| {
                        let rest: F128 = (1..chunks.d()).map(|i| eq.eval(&chunks, w, i)).product();
                        weight * eval_chunk(&chunks, &shifts.tables[shift], w, 0) * rest
                    })
                    .sum();
                assert_eq!(mle(&array, &r), rows, "width {width}, shift {shift}");
            }
        }
    }

    /// The eq product of a pair range split into pieces at any pair, each piece read through a view from its own even
    /// offset as a task sees it, sums to the product over the whole range, for the shifted and the plain eq: the run
    /// that reaches the next one carries its cross term at every cut.
    #[test]
    fn an_eq_product_split_anywhere_is_the_whole_sum() {
        let mut rng = Rng::new(77);
        for (n, shifted) in [2usize, 3, 6, 10, 11].into_iter().flat_map(|n| [(n, true), (n, false)]) {
            let size = 1usize << n;
            let b = if shifted { rng.ext() } else { F128::ZERO };
            let shift = ShiftEq::new(rng.ext(), b, rng.ext_vec(n));
            let tail = Tail::Eq(shift.clone());
            let other: Vec<F128> = (0..size).map(|_| rng.ext()).collect();
            let mut whole = [F128::ZERO; 3];
            for k in 0..size / 2 {
                let (s0, s1, o0, o1) = (tail.at(2 * k), tail.at(2 * k + 1), other[2 * k], other[2 * k + 1]);
                whole[0] += s0 * o0;
                whole[1] += s1 * o1;
                whole[2] += (s0 + s1) * (o0 + o1);
            }
            for trial in 0..50 {
                let mut cuts: Vec<usize> = (0..trial % 6)
                    .map(|_| rng.next_u64() as usize % (size / 2 + 1))
                    .collect();
                cuts.extend([0, size / 2]);
                cuts.sort_unstable();
                let mut acc = [F128Unreduced::ZERO; 3];
                for piece in cuts.windows(2) {
                    let (lo, hi) = (piece[0], piece[1]);
                    // A view from the array's start or from the piece's first pair.
                    let base = if trial % 2 == 0 { 0 } else { lo };
                    let view = View {
                        head: &other[2 * base..],
                        offset: 2 * base,
                        len: size - 2 * base,
                        tail: &Tail::Zero,
                    };
                    add_eq_product(&mut acc, &shift, view, lo - base..hi - base);
                }
                assert_eq!(acc.map(F128Unreduced::reduce), whole, "n {n}, b {b:?}, cuts {cuts:?}");
            }
        }
    }

    /// At every size from one variable up, an eq tail with `a = 0, b = 1` holds `eq(j + 1)`, and arrays with zero,
    /// shifted eq, plain eq and powers tails, stored up to any length, prove as the arrays they stand for. At 15
    /// variables a round's fold spans several tasks.
    #[test]
    fn tails_prove_as_their_stored_arrays_at_every_size() {
        for n in [1usize, 2, 3, 4, 5, 6, 7, 8, 11, 15] {
            let mut rng = Rng::new(0x7a1 + n as u64);
            let size = 1usize << n;
            let (c, zeta) = (rng.ext(), rng.ext_vec(n));
            let tails = [
                Tail::Zero,
                Tail::Eq(ShiftEq::new(c, rng.ext(), zeta.clone())),
                Tail::Eq(ShiftEq::new(F128::ZERO, F128::ONE, zeta.clone())),
                Tail::Eq(ShiftEq::new(c, F128::ZERO, zeta.clone())),
                Tail::Powers {
                    c,
                    ratio: F64::G.pow(5),
                },
            ];
            let eq = eq_table(&zeta);
            for j in 0..size {
                assert_eq!(
                    tails[2].at(j),
                    eq.get(j + 1).copied().unwrap_or(F128::ZERO),
                    "n {n}, j {j}"
                );
            }
            let lens = [
                (0, size),
                (0, size / 2 + 1),
                (0, 3),
                (1, 0),
                (2, 0),
                (1, 5),
                (3, 0),
                (0, size - 1),
                (0, 1),
                (4, 0),
                (4, 3),
            ];
            let heads: Vec<Array> = lens
                .iter()
                .map(|&(t, len)| {
                    let tail = &tails[t];
                    let head: Vec<F128> = (0..len.min(size))
                        .map(|j| if t == 0 || j % 7 == 3 { rng.ext() } else { tail.at(j) })
                        .collect();
                    Array {
                        head,
                        tail: tail.clone(),
                    }
                })
                .collect();
            let full: Vec<Vec<F128>> = (heads.iter())
                .map(|a| match a.tail {
                    Tail::Zero => a.head.clone(),
                    _ => (0..size).map(|j| a.get(j)).collect(),
                })
                .collect();
            let terms = [
                (3, 0),
                (4, 0),
                (1, 4),
                (4, 1),
                (5, 2),
                (4, 7),
                (8, 3),
                (4, 6),
                (3, 8),
                (4, 4),
                (9, 4),
                (10, 1),
            ]
            .map(|(a, b)| Term::Product { coef: rng.ext(), a, b })
            .into_iter()
            .chain([Term::Single { coef: rng.ext(), a: 4 }])
            .collect::<Vec<_>>();
            let run = |arrays: Vec<Array>| {
                let (mut rng, mut polys) = (Rng::new(0x7a2), Vec::new());
                let end = prove(n, arrays, &terms, &mut |poly| {
                    polys.push(poly.to_vec());
                    rng.ext()
                });
                (polys, end.values, end.claim)
            };
            let stored = run(full.into_iter().map(Array::from).collect());
            assert_eq!(run(heads), stored, "n {n}");
        }
    }
}
