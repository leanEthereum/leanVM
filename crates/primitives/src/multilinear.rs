// CREDIT: https://github.com/succinctlabs/flock (`build_eq` and the skip domain's Lagrange weights), MIT OR Apache-2.0.
//! Multilinear-extension utilities: the equality polynomial, single-variable
//! folding, and MLE evaluation. Truth tables are indexed little-endian (variable
//! `k` is bit `k`). Sumchecks here consume variables from either end, so folding
//! and `eq`-marginalization come in low and high variants. Committed data is
//! `K`-valued (`F64`) while randomness is `E`-valued (`F192`), so the first
//! fold of a committed table also lifts it into `E`.

use std::mem::MaybeUninit;
use std::ops::Range;

use crate::field::gf2_64::{reduce, software::clmul};
use crate::field::{
    F64, F192, F192Unreduced, PHI_8_TABLE_192 as PHI_8_TABLE, Weights8, dot_base, mul_base8, mul_unreduced4, mul4,
};

/// Multilinear interpolation in one variable over `E`: `lo + t·(lo+hi)`, the
/// char-2 form of `(1−t)·lo + t·hi`.
#[inline]
pub fn interp(lo: F192, hi: F192, t: F192) -> F192 {
    lo + t * (lo + hi)
}

/// Mixed interpolation: two `K` endpoints against an `E` parameter, one
/// `mul_base` (`lo + t·(lo+hi)` with `lo, hi ∈ K`).
#[inline]
pub fn interp_k(lo: F64, hi: F64, t: F192) -> F192 {
    F192::from(lo) + t.mul_base(lo + hi)
}

/// `eq(r, x) = ∏_i (1 + r_i + x_i)`. For Boolean `r`, this is the indicator
/// of `x = r`; for arbitrary `r`, it is the multilinear interpolation weight.
pub fn eq_eval(r: &[F192], x: &[F192]) -> F192 {
    debug_assert_eq!(r.len(), x.len());
    r.iter()
        .zip(x)
        .fold(F192::ONE, |acc, (&ri, &xi)| acc * (F192::ONE + ri + xi))
}

/// The `eq(r, ·)` table over `n = r.len()` variables. See [`fill_eq_table_uninit`].
pub fn eq_table(r: &[F192]) -> Vec<F192> {
    eq_table_seeded(r, F192::ONE)
}

/// The table of `seed * eq(r, .)` over `n = r.len()` variables, in LSB-first order.
pub fn eq_table_seeded(r: &[F192], seed: F192) -> Vec<F192> {
    // One entry per point of the cube: 2^n.
    let len = 1usize << r.len();

    // Filled in place in the spare capacity, so no slot is zeroed first.
    let mut eq = Vec::with_capacity(len);
    fill_eq_table_uninit(r, seed, &mut eq.spare_capacity_mut()[..len]);
    // SAFETY: the fill writes all `len` entries.
    unsafe { eq.set_len(len) };
    eq
}

/// Fill `out` with `seed * eq(r, .)`, in LSB-first order. Every entry is written before it is read.
///
/// A small table doubles a level at a time on the calling thread.
///
/// A large one is a tensor product, written in one parallel pass:
///
/// ```text
///     out[h * 2^L + l] = high[h] * low[l],    low = eq(r[..L]),  high = seed * eq(r[L..])
/// ```
///
/// `low` stays in L1, so each entry costs one product and one store, with no level-by-level rereads.
/// A caller inside a dispatch must keep the table below `EQ_PAR_LEN`.
pub fn fill_eq_table_uninit(r: &[F192], seed: F192, out: &mut [MaybeUninit<F192>]) {
    assert_eq!(out.len(), 1usize << r.len(), "out must have length 2^r.len()");
    if out.len() < EQ_PAR_LEN {
        return fill_eq_doubling(r, seed, out);
    }
    let (r_low, r_high) = r.split_at(EQ_LOW_VARS);
    let low = eq_table(r_low);
    let high = eq_table_seeded(r_high, seed);
    let rows = parallel::recommended_chunk_size(high.len());
    parallel::chunks_mut(out, rows * low.len(), |c, chunk| {
        for (row, &w) in chunk.chunks_exact_mut(low.len()).zip(&high[c * rows..]) {
            for (dst, src) in row.as_chunks_mut::<4>().0.iter_mut().zip(low.as_chunks::<4>().0) {
                let p = mul4([w; 4], *src);
                dst.iter_mut().zip(p).for_each(|(d, p)| _ = d.write(p));
            }
        }
    });
}

/// Tables below this size are built on the calling thread.
const EQ_PAR_LEN: usize = 1 << 16;

/// The variables of the L1-resident factor of a large `eq` table.
const EQ_LOW_VARS: usize = 10;

/// The level-by-level `eq` build: each level writes the high half from the low half, then rewrites the low half.
///
/// In characteristic 2 the low child is the high child plus the parent, so each pair costs one product.
fn fill_eq_doubling(r: &[F192], seed: F192, out: &mut [MaybeUninit<F192>]) {
    out[0].write(seed);
    for (i, &rk) in r.iter().enumerate() {
        let half = 1usize << i;
        let (lo, hi) = out[..2 * half].split_at_mut(half);
        // SAFETY: the low half was initialized at earlier levels.
        let lo = unsafe { &mut *(lo as *mut [MaybeUninit<F192>] as *mut [F192]) };
        let (lo4, lo_tail) = lo.as_chunks_mut::<4>();
        let (hi4, hi_tail) = hi.as_chunks_mut::<4>();
        for (l, h) in lo4.iter_mut().zip(hi4) {
            let p = mul4([rk; 4], *l);
            for k in 0..4 {
                h[k].write(p[k]);
                l[k] += p[k];
            }
        }
        for (l, h) in lo_tail.iter_mut().zip(hi_tail) {
            let p = *l * rk;
            h.write(p);
            *l += p;
        }
    }
}

/// Below this a parallel dispatch costs more than the fold it replaces.
const PAR_THRESHOLD: usize = 1 << 12;

/// The mixed fold: bind the lowest variable of a `K`-table to an
/// `E`-challenge, producing the `E`-table the remaining rounds fold. One
/// `mul_base` per output entry.
fn fold_low_k(table: &[F64], chi: F192) -> Vec<F192> {
    debug_assert_eq!(table.len() % 2, 0);
    (0..table.len() / 2)
        .map(|i| interp_k(table[2 * i], table[2 * i + 1], chi))
        .collect()
}

/// Bind the highest variable of a `K`-table and lift the result into `E`.
///
/// Eight entries share one batched mixed product ([`mul_base8`]).
pub fn fold_high_k(table: &[F64], chi: F192) -> Vec<F192> {
    debug_assert_eq!(table.len() % 2, 0);
    let (lo, hi) = table.split_at(table.len() / 2);
    let mut out = Vec::with_capacity(lo.len());
    let (out8, out_tail) = out.spare_capacity_mut()[..lo.len()].as_chunks_mut::<8>();
    let ((lo8, lo_tail), (hi8, hi_tail)) = (lo.as_chunks::<8>(), hi.as_chunks::<8>());
    for ((o, l), h) in out8.iter_mut().zip(lo8).zip(hi8) {
        let p = mul_base8(chi, std::array::from_fn(|i| l[i] + h[i]));
        for i in 0..8 {
            o[i].write(F192::from(l[i]) + p[i]);
        }
    }
    for ((o, &l), &h) in out_tail.iter_mut().zip(lo_tail).zip(hi_tail) {
        o.write(interp_k(l, h, chi));
    }
    // SAFETY: both loops together write every entry.
    unsafe { out.set_len(lo.len()) };
    out
}

/// Bind the highest free variable of `table` to `chi` in place: `table[i] =
/// interp(table[i], table[i + half], chi)`. Binding from the top down leaves the
/// low variables, the ones every table of a batch shares, for last.
pub fn fold_high_inplace(table: &mut Vec<F192>, chi: F192) {
    debug_assert_eq!(table.len() % 2, 0);
    let half = table.len() / 2;
    {
        // Split once rather than index twice: indexing reloads the data pointer
        // and length through the container every iteration, since nothing proves
        // they do not alias the elements, and pays a bounds check for it.
        let (lo, hi) = (**table).split_at_mut(half);
        interp_into(lo, hi, chi);
    }
    table.truncate(half);
}

/// `lo[i] = interp(lo[i], hi[i], chi)`, four products per batch.
fn interp_into(lo: &mut [F192], hi: &[F192], chi: F192) {
    let ((lo4, lo_tail), (hi4, hi_tail)) = (lo.as_chunks_mut::<4>(), hi.as_chunks::<4>());
    for (l, h) in lo4.iter_mut().zip(hi4) {
        let p = mul4([chi; 4], std::array::from_fn(|i| l[i] + h[i]));
        for i in 0..4 {
            l[i] += p[i];
        }
    }
    for (l, h) in lo_tail.iter_mut().zip(hi_tail) {
        *l = interp(*l, *h, chi);
    }
}

/// Marginalize the lowest variable out of an `eq` table (in place). `eq(r_0, 0) +
/// eq(r_0, 1) = 1`, so summing adjacent entries drops `r_0` with no multiplies,
/// versus `2^{n-1}` to rebuild the table.
pub fn shrink_eq_low(table: &mut Vec<F192>) {
    let half = table.len() / 2;
    {
        // Sliced, as in `fold_high_inplace`: reading the pair and writing the
        // sum through one slice drops the per-iteration reload and its bounds
        // check. The write index trails the read, so the in-place walk is sound.
        let t: &mut [F192] = table;
        for i in 0..half {
            let (a, b) = (t[2 * i], t[2 * i + 1]);
            t[i] = a + b;
        }
    }
    table.truncate(half);
}

/// Marginalize the highest variable out of an `eq` table (in place), the
/// [`shrink_eq_low`] counterpart for a top-down sumcheck.
pub fn shrink_eq_high(table: &mut Vec<F192>) {
    let half = table.len() / 2;
    {
        // Sliced, as in `fold_high_inplace`.
        let (lo, hi) = (**table).split_at_mut(half);
        for (l, h) in lo.iter_mut().zip(&*hi) {
            *l += *h;
        }
    }
    table.truncate(half);
}

/// The barycentric weight every node of an aligned `size`-node window of the φ₈ table shares,
/// `1 / ∏_{k≠0} φ₈(k)`. φ₈ is F2-linear on its index, so `nodes[a] + nodes[b] = φ₈(a ^ b)` (the window's
/// offset cancels) and `b ↦ a ^ b` only permutes the window, leaving every node the same product.
/// Computed once for every window size.
pub fn window_denominator(size: usize) -> F192 {
    debug_assert!(size.is_power_of_two() && size <= PHI_8_TABLE.len());
    DENOMINATORS[size.trailing_zeros() as usize]
}

/// [`window_denominator`] for every window size, at compile time. The nodes lie in `F64`, so the
/// product and its inverse (Fermat, `a^(2^64 - 2)`) stay there.
const DENOMINATORS: [F192; 9] = {
    const fn mul(a: u64, b: u64) -> u64 {
        reduce(clmul(a, b))
    }
    let mut out = [F192::ZERO; 9];
    let mut log = 0;
    while log < out.len() {
        let mut product = 1;
        let mut k = 1;
        while k < 1 << log {
            product = mul(product, PHI_8_TABLE[k].c0);
            k += 1;
        }
        let (mut inverse, mut bit) = (1, 1);
        while bit < 64 {
            product = mul(product, product);
            inverse = mul(inverse, product);
            bit += 1;
        }
        out[log] = F192::new(inverse, 0, 0);
        log += 1;
    }
    out
};

/// `scale · Σ_i values[i] · ∏_{k≠i} (p + nodes[k])`, in one pass of three products a node and no
/// inverse; `sum` and `prefix` hold the sum and the product of the differences over the nodes seen so
/// far. For an aligned window of the φ₈ table and `scale = window_denominator(nodes.len())` it is the
/// Lagrange interpolant of `values` at `p`, exact at a node too.
pub fn barycentric_sum(nodes: &[F192], values: &[F192], p: F192, scale: F192) -> F192 {
    debug_assert_eq!(nodes.len(), values.len());
    let (mut sum, mut prefix) = (values[0] * scale, scale);
    for i in 1..nodes.len() {
        prefix *= p + nodes[i - 1];
        sum = sum * (p + nodes[i]) + values[i] * prefix;
    }
    sum
}

/// A polynomial at `point`, by Horner over its coefficients, constant first.
#[inline]
pub fn poly_eval(coeffs: &[F192], point: F192) -> F192 {
    coeffs.iter().rev().fold(F192::ZERO, |acc, &c| acc * point + c)
}

/// Evaluate the MLE of a `K`-valued truth table at an `E`-point (length `log2(len)`).
///
/// The `eq` weights factor into a low and a high table:
///
/// ```text
///     f(point) = sum_h eq(point_high, h) * sum_l eq(point_low, l) * f[h * 2^L + l]
/// ```
///
/// Each row's inner sum is one [`dot_base`] against the packed low table, reduced once.
/// The table is read once and never lifted into `E`.
pub fn mle_eval(table: &[F64], point: &[F192]) -> F192 {
    debug_assert_eq!(table.len(), 1 << point.len());
    if point.len() < 3 {
        return match point.split_first() {
            None => F192::from(table[0]),
            Some((&p0, rest)) => fold_ladder(fold_low_k(table, p0), rest),
        };
    }
    let low_vars = point.len().min(MLE_LOW_VARS);
    let low = packed_eq(&point[..low_vars]);
    let rows = table
        .chunks_exact(1 << low_vars)
        .map(|row| dot_base(&low, row).reduce())
        .collect();
    fold_ladder(rows, &point[low_vars..])
}

/// [`mle_eval`] with the rows spread over the worker pool.
/// A caller already inside a dispatch must use [`mle_eval`] to avoid nesting.
pub fn mle_eval_par(table: &[F64], point: &[F192]) -> F192 {
    debug_assert_eq!(table.len(), 1 << point.len());
    if table.len() < PAR_THRESHOLD {
        return mle_eval(table, point);
    }
    let low_vars = point.len().min(MLE_LOW_VARS);
    let low = packed_eq(&point[..low_vars]);
    let high = eq_table(&point[low_vars..]);
    let eval = |row: usize| high[row] * dot_base(&low, &table[row << low_vars..(row + 1) << low_vars]).reduce();
    parallel::map_reduce(high.len(), || F192::ZERO, eval, |a, b| a + b)
}

/// The variables of the L1-resident low `eq` table of an MLE evaluation.
const MLE_LOW_VARS: usize = 10;

/// `eq(r, .)` packed eight weights at a time for [`dot_base`]. Needs `r.len() >= 3`.
fn packed_eq(r: &[F192]) -> Vec<Weights8> {
    eq_table(r).as_chunks::<8>().0.iter().map(Weights8::new).collect()
}

/// Bind the remaining variables of a half-folded `E`-table, LSB-first.
fn fold_ladder(mut cur: Vec<F192>, point: &[F192]) -> F192 {
    let mut len = cur.len();
    for &p in point {
        len /= 2;
        for i in 0..len {
            cur[i] = interp(cur[2 * i], cur[2 * i + 1], p);
        }
    }
    cur[0]
}

/// The Lagrange weights of the skip domain, the first `2^k_skip` nodes of the φ₈ table, at `z`:
/// `weights[i] = ∏_{k≠i} (z + φ₈(k)) · window_denominator`, by prefix and suffix products of the
/// differences. Linear in the node count, no inverse, and exact at a node.
pub fn skip_lagrange_weights(k_skip: usize, z: F192) -> Vec<F192> {
    let n = 1usize << k_skip;
    let nodes = &PHI_8_TABLE[..n];
    let mut weights = vec![window_denominator(n); n];
    for i in 1..n {
        weights[i] = weights[i - 1] * (z + nodes[i - 1]);
    }
    let mut suffix = z + nodes[n - 1];
    for i in (1..n - 1).rev() {
        weights[i] *= suffix;
        suffix *= z + nodes[i];
    }
    if n > 1 {
        weights[0] *= suffix;
    }
    weights
}

/// The inner product `sum_i a_i * b_i` over `E`.
#[inline]
pub fn inner_product(a: &[F192], b: &[F192]) -> F192 {
    assert_eq!(a.len(), b.len());
    a.iter().zip(b).fold(F192::ZERO, |acc, (&x, &y)| acc + x * y)
}

/// The mixed inner product `sum_i e_i * k_i`, with `k` in `K` and `e` in `E`.
#[inline]
pub fn inner_product_base(k: &[F64], e: &[F192]) -> F192 {
    assert_eq!(k.len(), e.len());
    k.iter().zip(e).fold(F192::ZERO, |acc, (&k, &e)| acc + e.mul_base(k))
}

/// The table `eq(r, .)` as two smaller tables, `eq(r, x) = low[x mod 2^L] * high[x >> L]`.
///
/// - The low table is `eq` over the first `L` variables of `r`, the high table over the rest.
/// - Together they hold `2^L + 2^(n - L)` entries instead of `2^n`.
/// - Products are exact, so every entry equals the full table's.
#[derive(Clone, Debug)]
pub struct SplitEq {
    /// The table over the low `L` variables.
    pub low: Vec<F192>,
    /// The table over the remaining variables.
    pub high: Vec<F192>,
    /// `L`.
    low_log: usize,
}

impl SplitEq {
    /// The split with at most `max_low` low variables.
    pub fn with_low_vars(r: &[F192], max_low: usize) -> Self {
        Self::at_split(r, r.len().min(max_low))
    }

    /// The split with at most `max_high` high variables.
    pub fn with_high_vars(r: &[F192], max_high: usize) -> Self {
        Self::at_split(r, r.len() - r.len().min(max_high))
    }

    fn at_split(r: &[F192], low_log: usize) -> Self {
        Self {
            low: eq_table(&r[..low_log]),
            high: eq_table(&r[low_log..]),
            low_log,
        }
    }

    /// The number of low variables `L`.
    pub const fn low_log(&self) -> usize {
        self.low_log
    }

    /// The number of high variables.
    pub const fn high_log(&self) -> usize {
        self.high.len().trailing_zeros() as usize
    }

    /// `eq(r, x)`.
    #[inline]
    pub fn at(&self, x: usize) -> F192 {
        self.low[x & (self.low.len() - 1)] * self.high[x >> self.low_log]
    }

    /// `sum_x eq(r, x) * terms(x)` over a range of `x`, four coefficients at once.
    ///
    /// - The closure returns the unreduced products at `x`, already scaled by the low weight it is given.
    /// - Each run of `x` sharing a high weight is reduced once and scaled by it once.
    #[inline]
    pub fn weighted_sum(
        &self,
        range: Range<usize>,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parallel_mle_matches_folding() {
        for n in [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 16] {
            let table: Vec<_> = (0..1 << n)
                .map(|i: u64| F64(i.wrapping_mul(0x9E37_79B9_7F4A_7C15)))
                .collect();
            // The plain fold, one variable at a time, is the reference.
            let fold = |point: &[F192]| match point.split_first() {
                None => F192::from(table[0]),
                Some((&p0, rest)) => fold_ladder(fold_low_k(&table, p0), rest),
            };
            let point: Vec<_> = (0..n).map(|i| F192::new(17 + i, 231 + 3 * i, 97 + 7 * i)).collect();
            assert_eq!(mle_eval(&table, &point), fold(&point));
            assert_eq!(mle_eval_par(&table, &point), fold(&point));
            let point: Vec<_> = (0..n).map(|i| F192::from(F64(i % 2))).collect();
            assert_eq!(mle_eval(&table, &point), fold(&point));
            assert_eq!(mle_eval_par(&table, &point), fold(&point));
            // An odd length leaves a scalar tail after the batched folds.
            let chi = point.first().copied().unwrap_or(F192::Y) + F192::Y;
            if n > 0 {
                let half = table.len() / 2;
                let want: Vec<_> = (0..half).map(|i| interp_k(table[i], table[i + half], chi)).collect();
                assert_eq!(&*fold_high_k(&table, chi), &want[..]);
                let lifted: Vec<F192> = table.iter().map(|&k| F192::from(k) * chi).collect();
                let mut got = lifted.clone();
                fold_high_inplace(&mut got, chi);
                let want: Vec<_> = (0..half).map(|i| interp(lifted[i], lifted[i + half], chi)).collect();
                assert_eq!(got, want);
            }
        }
    }

    #[test]
    fn split_eq_is_the_eq_table() {
        // Invariant: the two tables weigh every row as the full eq table, and a weighted sum
        // over a range equals the dense one, whether it crosses a high block or not.
        //
        // Fixture state: 14 variables, split 12 low and 2 high, then 7 low and 7 high.
        let r: Vec<F192> = (0..14u64).map(|i| F192::new(3 * i + 1, i + 7, 5 * i + 2)).collect();
        let dense = eq_table(&r);
        for split in [SplitEq::with_low_vars(&r, 12), SplitEq::with_high_vars(&r, 7)] {
            assert_eq!(split.low_log() + split.high_log(), r.len());
            for x in [0, 1, 127, 128, 4095, 4096, 4097, 12_345, (1 << 14) - 1] {
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

        // A split with fewer variables than its cap puts them all on the capped side.
        let short = SplitEq::with_high_vars(&r[..3], 7);
        assert_eq!((short.low_log(), short.high_log()), (0, 3));
    }
}
