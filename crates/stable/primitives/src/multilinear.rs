// CREDIT: https://github.com/succinctlabs/flock (`build_eq`), MIT OR Apache-2.0.
//! Multilinear-extension utilities: the equality polynomial, single-variable
//! folding, and MLE evaluation. Truth tables are indexed little-endian (variable
//! `k` is bit `k`). Sumchecks here consume variables from either end, so folding
//! and `eq`-marginalization come in low and high variants. Committed data is
//! `K`-valued (`F64`) while randomness is `E`-valued (`F128`), so the first
//! fold of a committed table also lifts it into `E`.

use crate::field::{F64, F128, F128Unreduced};

/// Multilinear interpolation in one variable over `E`: `lo + t·(lo+hi)`, the
/// char-2 form of `(1−t)·lo + t·hi`.
#[inline]
pub fn interp(lo: F128, hi: F128, t: F128) -> F128 {
    lo + t * (lo + hi)
}

/// Mixed interpolation: two `K` endpoints against an `E` parameter, one
/// `mul_base` (`lo + t·(lo+hi)` with `lo, hi ∈ K`).
#[inline]
pub fn interp_k(lo: F64, hi: F64, t: F128) -> F128 {
    F128::from(lo) + t.mul_base(lo + hi)
}

/// `eq(r, x) = ∏_i (1 + r_i + x_i)`. For Boolean `r`, this is the indicator
/// of `x = r`; for arbitrary `r`, it is the multilinear interpolation weight.
pub fn eq_eval(r: &[F128], x: &[F128]) -> F128 {
    debug_assert_eq!(r.len(), x.len());
    r.iter().zip(x).map(|(&ri, &xi)| F128::ONE + ri + xi).product()
}

/// The `eq(r, ·)` table over `n = r.len()` variables. See [`fill_eq_table`].
pub fn eq_table(r: &[F128]) -> Vec<F128> {
    let mut eq = zeroed(1 << r.len());
    fill_eq_table(r, F128::ONE, &mut eq);
    eq
}

/// A zeroed table, allocated in parallel when [`fill_eq_table`] would fill it in parallel.
fn zeroed(len: usize) -> Vec<F128> {
    if len < EQ_PAR_LEN {
        vec![F128::ZERO; len]
    } else {
        parallel::filled(len, F128::ZERO)
    }
}

/// The `eq(r, ·)` table, built on the calling thread.
pub fn eq_table_serial(r: &[F128]) -> Vec<F128> {
    let mut eq = vec![F128::ZERO; 1 << r.len()];
    fill_eq_doubling(r, F128::ONE, &mut eq);
    eq
}

/// Fill `out` with `seed * eq(r, .)`, in LSB-first order. The old contents of `out` are never read.
///
/// A small table doubles a level at a time on the calling thread. A large one is a tensor product,
/// written row by row in parallel:
///
/// ```text
///     out[h * 2^L + l] = high[h] * low[l],    low = eq(r[..L]),  high = seed * eq(r[L..])
/// ```
///
/// A caller inside a dispatch must keep the table below `EQ_PAR_LEN`.
pub fn fill_eq_table(r: &[F128], seed: F128, out: &mut [F128]) {
    assert_eq!(out.len(), 1usize << r.len(), "out must have length 2^r.len()");
    if out.len() < EQ_PAR_LEN {
        return fill_eq_doubling(r, seed, out);
    }
    let (r_low, r_high) = r.split_at(EQ_LOW_VARS);
    let low = eq_table_serial(r_low);
    let mut high = zeroed(1 << r_high.len());
    fill_eq_table(r_high, seed, &mut high);
    parallel::chunks_mut(out, low.len(), |h, row| {
        for (o, &l) in row.iter_mut().zip(&low) {
            *o = high[h] * l;
        }
    });
}

/// Tables below this size are built on the calling thread.
const EQ_PAR_LEN: usize = 1 << 16;

/// The variables of the row factor of a large `eq` table.
const EQ_LOW_VARS: usize = 10;

/// The level-by-level `eq` build: each level writes the high half from the low half, then rewrites the low half.
///
/// In characteristic 2 the low child is the high child plus the parent, so each pair costs one product.
fn fill_eq_doubling(r: &[F128], seed: F128, out: &mut [F128]) {
    out[0] = seed;
    for (i, &rk) in r.iter().enumerate() {
        let (lo, hi) = out[..2 << i].split_at_mut(1 << i);
        for (l, h) in lo.iter_mut().zip(hi) {
            *h = *l * rk;
            *l += *h;
        }
    }
}

/// Below this a parallel dispatch costs more than the evaluation it replaces.
const PAR_THRESHOLD: usize = 1 << 12;

/// Marginalize the highest variable out of an `eq` table (in place), for a top-down sumcheck.
/// `eq(r, 0) + eq(r, 1) = 1`, so summing the two halves drops `r` with no multiplies.
pub fn shrink_eq_high(table: &mut Vec<F128>) {
    let half = table.len() / 2;
    let (lo, hi) = table.split_at_mut(half);
    for (l, h) in lo.iter_mut().zip(&*hi) {
        *l += *h;
    }
    table.truncate(half);
}

/// A polynomial at `point`, by Horner over its coefficients, constant first.
#[inline]
pub fn poly_eval(coeffs: &[F128], point: F128) -> F128 {
    coeffs.iter().rev().fold(F128::ZERO, |acc, &c| acc * point + c)
}

/// The variables of the low `eq` table of an MLE evaluation.
const MLE_LOW_VARS: usize = 10;

/// `sum_i w_i * k_i`, reduced once.
fn dot(w: &[F128], k: &[F64]) -> F128 {
    w.iter()
        .zip(k)
        .fold(F128Unreduced::ZERO, |acc, (w, &k)| acc ^ w.mul_base_unreduced(k))
        .reduce()
}

/// Evaluate the MLE of a `K`-valued truth table at an `E`-point (length `log2(len)`).
///
/// The `eq` weights factor into a low and a high table, one dot product per row:
///
/// ```text
///     f(point) = sum_h eq(point_high, h) * sum_l eq(point_low, l) * f[h * 2^L + l]
/// ```
pub fn mle_eval(table: &[F64], point: &[F128]) -> F128 {
    assert_eq!(table.len(), 1 << point.len());
    let low_vars = point.len().min(MLE_LOW_VARS);
    let low = eq_table_serial(&point[..low_vars]);
    let high = eq_table_serial(&point[low_vars..]);
    table
        .chunks_exact(low.len())
        .zip(high)
        .map(|(row, h)| h * dot(&low, row))
        .sum()
}

/// [`mle_eval`] with the rows spread over the worker pool. A shorter `table` is zero past its end, which must be a
/// whole number of rows.
/// A caller already inside a dispatch must use [`mle_eval`] to avoid nesting.
pub fn mle_eval_par(table: &[F64], point: &[F128]) -> F128 {
    assert!(table.len() <= 1 << point.len());
    if table.len() == 1 << point.len() && table.len() < PAR_THRESHOLD {
        return mle_eval(table, point);
    }
    let low_vars = point.len().min(MLE_LOW_VARS);
    let low = eq_table_serial(&point[..low_vars]);
    let high = eq_table(&point[low_vars..]);
    assert!(table.len().is_multiple_of(low.len()));
    let eval = |row: usize| high[row] * dot(&low, &table[row * low.len()..][..low.len()]);
    parallel::map_reduce(table.len() / low.len(), || F128::ZERO, eval, |a, b| a + b)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The plain fold, one variable at a time, lowest first.
    fn fold(table: &[F64], point: &[F128]) -> F128 {
        let mut cur: Vec<F128> = table.iter().map(|&k| F128::from(k)).collect();
        for &p in point {
            cur = cur
                .as_chunks::<2>()
                .0
                .iter()
                .map(|&[lo, hi]| interp(lo, hi, p))
                .collect();
        }
        cur[0]
    }

    #[test]
    fn mle_matches_folding() {
        for n in [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 16] {
            let table: Vec<_> = (0..1 << n)
                .map(|i: u64| F64(i.wrapping_mul(0x9E37_79B9_7F4A_7C15)))
                .collect();
            let point: Vec<_> = (0..n).map(|i| F128::new(17 + i, 231 + 3 * i)).collect();
            assert_eq!(mle_eval(&table, &point), fold(&table, &point));
            assert_eq!(mle_eval_par(&table, &point), fold(&table, &point));
            let point: Vec<_> = (0..n).map(|i| F128::from(F64(i % 2))).collect();
            assert_eq!(mle_eval(&table, &point), fold(&table, &point));
            assert_eq!(mle_eval_par(&table, &point), fold(&table, &point));
        }
    }
}
