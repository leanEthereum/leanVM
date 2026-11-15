// CREDIT: https://github.com/succinctlabs/flock (`build_eq`), MIT OR Apache-2.0.
//! Multilinear helpers: one-variable interpolation, the equality polynomial and its tables, and the evaluation of a
//! committed table's multilinear extension. A table is indexed little-endian: variable `k` is bit `k` of the index.
//! Committed data is `K`-valued ([`F64`]) and randomness `E`-valued ([`F128`]).

use crate::field::{F64, F128, F128Unreduced};

/// Multilinear interpolation in one variable: `lo + t·(lo+hi)`, the characteristic-2 form of `(1−t)·lo + t·hi`.
#[inline]
pub fn interp(lo: F128, hi: F128, t: F128) -> F128 {
    lo + t * (lo + hi)
}

/// [`interp`] between two `K` endpoints: one mixed product.
#[inline]
pub fn interp_k(lo: F64, hi: F64, t: F128) -> F128 {
    F128::from(lo) + t.mul_base(lo + hi)
}

/// `eq(r, x) = ∏_i (1 + r_i + x_i)`: for Boolean `r` the indicator of `x = r`, for any `r` the multilinear
/// interpolation weight of `x`.
pub fn eq_eval(r: &[F128], x: &[F128]) -> F128 {
    debug_assert_eq!(r.len(), x.len());
    r.iter().zip(x).map(|(&ri, &xi)| F128::ONE + ri + xi).product()
}

/// Tables of at least this many variables are built in parallel.
const EQ_PAR_VARS: usize = 16;

/// The variables of the row factor of a large `eq` table.
const EQ_LOW_VARS: usize = 10;

/// The `eq(r, ·)` table over `r.len()` variables.
///
/// A small one is [`eq_table_serial`]. A large one is a tensor product, each entry written once, in parallel:
///
/// ```text
///     eq[h * 2^L + l] = high[h] * low[l],    low = eq(r[..L]),  high = eq(r[L..])
/// ```
///
/// A caller inside a dispatch must use [`eq_table_serial`].
pub fn eq_table(r: &[F128]) -> Vec<F128> {
    if r.len() < EQ_PAR_VARS {
        return eq_table_serial(r);
    }
    let (low, high) = (eq_table_serial(&r[..EQ_LOW_VARS]), eq_table(&r[EQ_LOW_VARS..]));
    parallel::map_collect(1 << r.len(), |i| high[i >> EQ_LOW_VARS] * low[i % low.len()])
}

/// The `eq(r, ·)` table, built on the calling thread a level at a time: each level writes the high half from the low
/// half, then rewrites the low half. In characteristic 2 the low child is the high child plus the parent, so each
/// pair costs one product.
pub fn eq_table_serial(r: &[F128]) -> Vec<F128> {
    let mut eq = vec![F128::ZERO; 1 << r.len()];
    eq[0] = F128::ONE;
    for (i, &rk) in r.iter().enumerate() {
        let (lo, hi) = eq[..2 << i].split_at_mut(1 << i);
        for (l, h) in lo.iter_mut().zip(hi) {
            *h = *l * rk;
            *l += *h;
        }
    }
    eq
}

/// Marginalize the highest variable out of an `eq` table, in place, for a sumcheck that binds the top variable
/// first: `eq(r, 0) + eq(r, 1) = 1`, so summing the two halves drops it without a product.
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

/// Below this many entries, an evaluation stays on the calling thread.
const MLE_PAR_LEN: usize = 1 << 12;

/// The MLE of a `K`-valued table at an `E`-point of `log2(table.len())` coordinates.
///
/// The `eq` weights factor into a low and a high table, so the evaluation is one dot product per row of `2^L` entries,
/// each reduced once:
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

/// [`mle_eval`] with the rows spread over the pool. A shorter `table` is zero past its end, which must be a whole
/// number of rows. A caller inside a dispatch must use [`mle_eval`].
pub fn mle_eval_par(table: &[F64], point: &[F128]) -> F128 {
    assert!(table.len() <= 1 << point.len());
    if table.len() == 1 << point.len() && table.len() < MLE_PAR_LEN {
        return mle_eval(table, point);
    }
    let low_vars = point.len().min(MLE_LOW_VARS);
    let low = eq_table_serial(&point[..low_vars]);
    let high = eq_table(&point[low_vars..]);
    assert!(table.len().is_multiple_of(low.len()));
    let eval = |row: usize| high[row] * dot(&low, &table[row * low.len()..][..low.len()]);
    parallel::map_reduce(table.len() / low.len(), || F128::ZERO, eval, |a, b| a + b)
}

/// `sum_i w_i * k_i`, reduced once.
fn dot(w: &[F128], k: &[F64]) -> F128 {
    w.iter()
        .zip(k)
        .fold(F128Unreduced::ZERO, |acc, (w, &k)| acc ^ w.mul_base_unreduced(k))
        .reduce()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_rng::Rng;

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

    /// The tensor form against the level-by-level one, on both sides of the parallel threshold.
    #[test]
    fn parallel_eq_table_matches_serial() {
        let mut rng = Rng::new(21);
        for n in [0, 1, 6, EQ_PAR_VARS - 1, EQ_PAR_VARS, EQ_PAR_VARS + 1] {
            let point = rng.ext_vec(n);
            assert_eq!(eq_table(&point), eq_table_serial(&point), "n = {n}");
        }
    }
}
