// CREDIT: https://github.com/succinctlabs/flock (`build_eq` and `lagrange_weights_naive`), MIT OR Apache-2.0.
//! Multilinear-extension utilities: the equality polynomial, single-variable
//! folding, and MLE evaluation. Truth tables are indexed little-endian (variable
//! `k` is bit `k`). Sumchecks here consume variables from either end, so folding
//! and `eq`-marginalization come in low and high variants. Committed data is
//! `K`-valued (`F64`) while randomness is `E`-valued (`F192`), so the first
//! fold of a committed table also lifts it into `E`.

use std::ops::DerefMut;

use std::mem::MaybeUninit;

use crate::field::{F64, F192, PHI_8_TABLE_192 as PHI_8_TABLE, Weights8, dot_base, mul_base8, mul4};
use zk_alloc::ArenaVec;

/// The one thing the in-place folds need beyond a mutable slice: the ability to
/// drop a suffix. Implemented for `Vec` and `ArenaVec`, so a fold works on either
/// without duplicating the kernel or naming a container in its signature.
pub trait Shrink<T>: DerefMut<Target = [T]> {
    /// Keep the first `len` elements, dropping the rest.
    fn shrink_to(&mut self, len: usize);
}

impl<T> Shrink<T> for Vec<T> {
    #[inline]
    fn shrink_to(&mut self, len: usize) {
        self.truncate(len);
    }
}

impl<T> Shrink<T> for ArenaVec<T> {
    #[inline]
    fn shrink_to(&mut self, len: usize) {
        self.truncate(len);
    }
}

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
    let len = 1usize << r.len();
    let mut eq = Vec::with_capacity(len);
    fill_eq_table_uninit(r, F192::ONE, &mut eq.spare_capacity_mut()[..len]);
    // SAFETY: the fill writes all `len` entries.
    unsafe { eq.set_len(len) };
    eq
}

/// Arena-backed [`eq_table`], for the prover's large tables. Identical output.
pub fn eq_table_arena(r: &[F192]) -> ArenaVec<F192> {
    let mut eq = zk_alloc::alloc_uninit(1usize << r.len());
    fill_eq_table_uninit(r, F192::ONE, &mut eq);
    // SAFETY: the fill writes every entry.
    unsafe { zk_alloc::assume_init(eq) }
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
    let mut high = zk_alloc::alloc_uninit(1usize << r_high.len());
    fill_eq_table_uninit(r_high, seed, &mut high);
    // SAFETY: the fill above writes every entry.
    let high = unsafe { zk_alloc::assume_init(high) };
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
pub fn fold_high_k(table: &[F64], chi: F192) -> ArenaVec<F192> {
    debug_assert_eq!(table.len() % 2, 0);
    let (lo, hi) = table.split_at(table.len() / 2);
    let mut out = zk_alloc::alloc_uninit(lo.len());
    let (out8, out_tail) = out.as_chunks_mut::<8>();
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
    unsafe { zk_alloc::assume_init(out) }
}

/// Bind the highest free variable of `table` to `chi` in place: `table[i] =
/// interp(table[i], table[i + half], chi)`. Binding from the top down leaves the
/// low variables, the ones every table of a batch shares, for last.
pub fn fold_high_inplace<B: Shrink<F192>>(table: &mut B, chi: F192) {
    debug_assert_eq!(table.len() % 2, 0);
    let half = table.len() / 2;
    {
        // Split once rather than index twice: indexing reloads the data pointer
        // and length through the container every iteration, since nothing proves
        // they do not alias the elements, and pays a bounds check for it.
        let (lo, hi) = (**table).split_at_mut(half);
        interp_into(lo, hi, chi);
    }
    table.shrink_to(half);
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
pub fn shrink_eq_low<B: Shrink<F192>>(table: &mut B) {
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
    table.shrink_to(half);
}

/// Marginalize the highest variable out of an `eq` table (in place), the
/// [`shrink_eq_low`] counterpart for a top-down sumcheck.
pub fn shrink_eq_high<B: Shrink<F192>>(table: &mut B) {
    let half = table.len() / 2;
    {
        // Sliced, as in `fold_high_inplace`.
        let (lo, hi) = (**table).split_at_mut(half);
        for (l, h) in lo.iter_mut().zip(&*hi) {
            *l += *h;
        }
    }
    table.shrink_to(half);
}

/// The one barycentric denominator an aligned `size`-node window of the φ₈ table has: `∏_{k≠0} φ₈(k)`,
/// inverted. φ₈ is F2-linear on its index, so `nodes[a] + nodes[b] = φ₈(a ^ b)` (the window's offset
/// cancels) and `b ↦ a ^ b` only permutes the window, leaving every node the same product.
pub fn window_denominator(size: usize) -> F192 {
    PHI_8_TABLE[1..size]
        .iter()
        .fold(F192::ONE, |acc, &node| acc * node)
        .inv()
}

/// The barycentric weights of `nodes` at `p`: `weights[i] =
/// ∏_{k≠i} (p + nodes[k]) / ∏_{k≠i} (nodes[i] + nodes[k])`. `O(n²)` multiplies
/// and, by `window_denominator`, a single inverse.
///
/// `nodes` must be an aligned window of the φ₈ table, `nodes[a] = nodes[0] + φ₈(a)`, which is what
/// every caller passes: a `2^k` prefix, or one of its cosets.
fn lagrange_weights(nodes: &[F192], p: F192) -> Vec<F192> {
    let n = nodes.len();
    debug_assert!(n.is_power_of_two() && n <= PHI_8_TABLE.len());
    debug_assert!(
        (0..n).all(|a| nodes[a] == nodes[0] + PHI_8_TABLE[a]),
        "not an aligned φ₈ window"
    );
    let denominator = window_denominator(n);
    (0..n)
        .map(|i| {
            let mut num = F192::ONE;
            for k in 0..n {
                if k != i {
                    num *= p + nodes[k];
                }
            }
            num * denominator
        })
        .collect()
}

/// Lagrange evaluation: given distinct `nodes` and a polynomial's `values` there,
/// evaluate the interpolant at `p`. Reads a sumcheck round's univariate (sent as
/// evaluations) at the verifier's challenge.
pub fn lagrange_eval(nodes: &[F192], values: &[F192], p: F192) -> F192 {
    debug_assert_eq!(nodes.len(), values.len());
    lagrange_weights(nodes, p)
        .iter()
        .zip(values)
        .fold(F192::ZERO, |acc, (&w, &v)| acc + v * w)
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
    let high = eq_table_arena(&point[low_vars..]);
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

/// Barycentric weights over the first `2^k_skip` nodes of the GF(2^8) subfield.
/// O(2^{2·k_skip}) field multiplies, a one-time cost.
pub fn lagrange_weights_naive(k_skip: usize, z: F192) -> Vec<F192> {
    let ell = 1usize << k_skip;
    assert!(ell <= 256, "k_skip > 8 would exceed PHI_8_TABLE");
    lagrange_weights(&PHI_8_TABLE[..ell], z)
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
}
