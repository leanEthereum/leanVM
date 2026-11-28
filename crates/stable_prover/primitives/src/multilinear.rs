// CREDIT: https://github.com/succinctlabs/flock (`build_eq`), MIT OR Apache-2.0.
//! Multilinear helpers: one-variable interpolation and folding, the equality polynomial and its tables, the evaluation
//! of committed columns' multilinear extensions. A table is indexed little-endian: variable `k` is bit `k` of the index.
//! Committed data is `K`-valued ([`F64`]) and randomness `E`-valued ([`F128`]).

use crate::field::{Acc8, F64, F64x8, F128, F128x8};

/// Multilinear interpolation in one variable: `lo + t·(lo+hi)`, the characteristic-2 form of `(1−t)·lo + t·hi`.
#[inline]
pub fn interp(lo: F128, hi: F128, t: F128) -> F128 {
    lo + t * (lo + hi)
}

/// `table`, rows of `width`, with the row index's lowest variable bound at `challenge`.
pub fn fold(table: &[F128], width: usize, challenge: F128) -> Vec<F128> {
    let mut out = Vec::with_capacity(table.len() / 2);
    for pair in table.chunks_exact(2 * width) {
        let (lo, hi) = pair.split_at(width);
        out.extend(lo.iter().zip(hi).map(|(&lo, &hi)| interp(lo, hi, challenge)));
    }
    out
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
/// A caller inside a dispatch must use [`eq_table_serial`]. Out of line: one copy for every caller.
#[inline(never)]
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

/// A polynomial at `point`, by Horner over its coefficients, constant first. Out of line: one copy for every caller.
#[inline(never)]
pub fn poly_eval(coeffs: &[F128], point: F128) -> F128 {
    coeffs.iter().rev().fold(F128::ZERO, |acc, &c| acc * point + c)
}

/// `eq(point, z) = lo[z mod 2^lo_bits]·hi[z >> lo_bits]`: a table over the low variables, up to `LO_BITS`
/// of them, and one over the rest, so that none of the hypercube's size is built.
pub struct SplitEq {
    pub lo: Vec<F128>,
    pub hi: Vec<F128>,
    lo_bits: usize,
}

impl SplitEq {
    /// The low table's variables: a few kilobytes, which stay in cache.
    const LO_BITS: usize = 10;

    pub fn new(point: &[F128]) -> Self {
        let lo_bits = point.len().min(Self::LO_BITS);
        Self {
            lo: eq_table(&point[..lo_bits]),
            hi: eq_table(&point[lo_bits..]),
            lo_bits,
        }
    }

    /// `eq` at `8k..8k + 8`, zero past the hypercube.
    #[inline(never)]
    pub fn lanes(&self, k: usize) -> F128x8 {
        let (block, at) = ((8 * k) >> self.lo_bits, (8 * k) & (self.lo.len() - 1));
        match self.hi.get(block) {
            Some(&hi) => load_e(&self.lo, at, self.lo.len() - at) * F128x8::splat(hi),
            None => F128x8::ZERO,
        }
    }
}

/// Below this many points of the hypercube, [`eq_sums`] runs on the calling thread.
const EQ_SUMS_SERIAL: usize = 1 << 13;

/// `Σ_z eq(point, z)·c(z)` for every column `c`, the multilinear extensions of `K`-valued columns at an `E` point, in
/// one pass over the rows. A column shorter than `2^point.len()` is zero past its end.
///
/// A task is a run of rows of the high table, one row unless the sum is small: each row's sums are taken against the
/// low table, reduced once, and scaled once.
pub fn eq_sums(point: &[F128], columns: &[&[F64]]) -> Vec<F128> {
    let SplitEq { lo, hi, lo_bits } = SplitEq::new(point);
    let rows = if hi.len() * lo.len() < EQ_SUMS_SERIAL {
        hi.len()
    } else {
        1
    };
    let zero = || vec![F128::ZERO; columns.len()];
    let task = |sums: &mut Vec<F128>, task: usize| {
        for h in task * rows..hi.len().min((task + 1) * rows) {
            let z0 = h << lo_bits;
            for (sum, column) in sums.iter_mut().zip(columns) {
                let row = (0..lo.len().div_ceil(8)).fold(Acc8::ZERO, |acc, v| {
                    let (i, z) = (8 * v, z0 + 8 * v);
                    acc + load_e(&lo, i, lo.len() - i).mul_base_unreduced(load_k(
                        column,
                        z,
                        column.len().saturating_sub(z),
                    ))
                });
                *sum += hi[h] * row.sum();
            }
        }
    };
    let add = |mut a: Vec<F128>, b: Vec<F128>| {
        for (a, b) in a.iter_mut().zip(b) {
            *a += b;
        }
        a
    };
    parallel::fold_reduce(hi.len().div_ceil(rows), zero, task, add)
}

/// `values[i..i + n]` as lanes, zero past `n` (`n` at least eight takes eight).
#[inline]
pub fn load_k(values: &[F64], i: usize, n: usize) -> F64x8 {
    if n >= 8 {
        F64x8::load(&values[i..i + 8])
    } else {
        F64x8::from_array(&partial(values, i, n, F64::ZERO))
    }
}

/// `values[i..i + n]` as lanes, zero past `n` (`n` at least eight takes eight).
#[inline]
pub fn load_e(values: &[F128], i: usize, n: usize) -> F128x8 {
    if n >= 8 {
        F128x8::load(&values[i..i + 8])
    } else {
        F128x8::from_array(&partial(values, i, n, F128::ZERO))
    }
}

/// The `n < 8` values from `values[i]`, then `zero`: out of line, as only the last vector of a pass takes it.
#[inline(never)]
fn partial<T: Copy>(values: &[T], i: usize, n: usize, zero: T) -> [T; 8] {
    std::array::from_fn(|p| if p < n { values[i + p] } else { zero })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_rng::Rng;

    /// The evaluation by folding one variable at a time, lowest first.
    fn folded(table: &[F64], point: &[F128]) -> F128 {
        let table = table.iter().map(|&k| F128::from(k)).collect();
        point.iter().fold(table, |t: Vec<F128>, &p| fold(&t, 1, p))[0]
    }

    #[test]
    fn eq_sums_match_folding() {
        for n in [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 16] {
            let table: Vec<_> = (0..1 << n)
                .map(|i: u64| F64(i.wrapping_mul(0x9E37_79B9_7F4A_7C15)))
                .collect();
            // A column zero past its end, not at a row or vector boundary.
            let short = &table[..(1 << n) * 5 / 8];
            let mut padded = short.to_vec();
            padded.resize(1 << n, F64::ZERO);
            for point in [
                (0..n).map(|i| F128::new(17 + i, 231 + 3 * i)).collect::<Vec<_>>(),
                (0..n).map(|i| F128::from(F64(i % 2))).collect(),
            ] {
                let want = [folded(&table, &point), folded(&padded, &point), F128::ZERO];
                assert_eq!(eq_sums(&point, &[&table, short, &[]]), want);
            }
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
