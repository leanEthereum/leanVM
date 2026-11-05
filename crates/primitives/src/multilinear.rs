// CREDIT: https://github.com/succinctlabs/flock (`build_eq`), MIT OR Apache-2.0.
//! Multilinear-extension utilities: the equality polynomial, single-variable
//! folding, and MLE evaluation. Truth tables are indexed little-endian (variable
//! `k` is bit `k`). Sumchecks here consume variables from either end, so folding
//! and `eq`-marginalization come in low and high variants. Committed data is
//! `K`-valued (`F64`) while randomness is `E`-valued (`F192`), so the first
//! fold of a committed table also lifts it into `E`.

use crate::field::{F64, F192, Weights8, dot_base, mul4};

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

/// The `eq(r, ·)` table over `n = r.len()` variables. See [`fill_eq_table`].
pub fn eq_table(r: &[F192]) -> Vec<F192> {
    // SAFETY: the fill writes every element before it reads any.
    unsafe { crate::filled_vec(1usize << r.len(), |eq| fill_eq_table(r, F192::ONE, eq)) }
}

/// The `eq(r, ·)` table, built on the calling thread.
pub fn eq_table_serial(r: &[F192]) -> Vec<F192> {
    // SAFETY: the fill writes every element before it reads any.
    unsafe { crate::filled_vec(1usize << r.len(), |eq| fill_eq_doubling(r, F192::ONE, eq)) }
}

/// Fill `out` with `seed * eq(r, .)`, in LSB-first order. The old contents of `out` are never read.
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
pub fn fill_eq_table(r: &[F192], seed: F192, out: &mut [F192]) {
    assert_eq!(out.len(), 1usize << r.len(), "out must have length 2^r.len()");
    if out.len() < EQ_PAR_LEN {
        return fill_eq_doubling(r, seed, out);
    }
    let (r_low, r_high) = r.split_at(EQ_LOW_VARS);
    let low = eq_table(r_low);
    // SAFETY: the fill writes every element before it reads any.
    let high = unsafe { crate::filled_vec(1usize << r_high.len(), |high| fill_eq_table(r_high, seed, high)) };
    let rows = parallel::recommended_chunk_size(high.len());
    parallel::chunks_mut(out, rows * low.len(), |c, chunk| {
        for (row, &w) in chunk.chunks_exact_mut(low.len()).zip(&high[c * rows..]) {
            for (dst, src) in row.as_chunks_mut::<4>().0.iter_mut().zip(low.as_chunks::<4>().0) {
                let p = mul4([w; 4], *src);
                *dst = p;
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
fn fill_eq_doubling(r: &[F192], seed: F192, out: &mut [F192]) {
    out[0] = seed;
    for (i, &rk) in r.iter().enumerate() {
        let half = 1usize << i;
        let (lo, hi) = out[..2 * half].split_at_mut(half);
        let (lo4, lo_tail) = lo.as_chunks_mut::<4>();
        let (hi4, hi_tail) = hi.as_chunks_mut::<4>();
        for (l, h) in lo4.iter_mut().zip(hi4) {
            let p = mul4([rk; 4], *l);
            *h = p;
            for (l, p) in l.iter_mut().zip(p) {
                *l += p;
            }
        }
        for (l, h) in lo_tail.iter_mut().zip(hi_tail) {
            let p = *l * rk;
            *h = p;
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

/// Marginalize the highest variable out of an `eq` table (in place), for a top-down sumcheck.
/// `eq(r, 0) + eq(r, 1) = 1`, so summing the two halves drops `r` with no multiplies.
pub fn shrink_eq_high(table: &mut Vec<F192>) {
    let half = table.len() / 2;
    {
        // Split once, so the loop pays no reload or bounds check.
        let (lo, hi) = (**table).split_at_mut(half);
        for (l, h) in lo.iter_mut().zip(&*hi) {
            *l += *h;
        }
    }
    table.truncate(half);
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
pub fn packed_eq(r: &[F192]) -> Vec<Weights8> {
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
        }
    }
}
