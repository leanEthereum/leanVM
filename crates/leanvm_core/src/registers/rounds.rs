//! A sumcheck over a log's rows, highest variable first, on tables stored row by row.
//!
//! - The first round reads every row from the trace, so no table is built at full height.
//! - Each later round folds the rows at the last challenge in the pass that sums it.

use fiat_shamir::transcript::Transmitter;
use parallel::SendPtr;
use primitives::field::{F192, F192Unreduced};

/// Rows per task of a pass.
const TASK_ROWS: usize = 1 << 12;

/// `(a_0 + X a_1)(b_0 + X b_1)` by Karatsuba: three products.
#[inline(always)]
pub(super) fn mul2((a0, a1): (F192, F192), (b0, b1): (F192, F192)) -> [F192; 3] {
    let (low, high) = (a0 * b0, a1 * b1);
    [low, (a0 + a1) * (b0 + b1) + low + high, high]
}

/// `q (u_0 + X u_1)` for a quadratic `q`, its coefficients unreduced.
#[inline(always)]
pub(super) fn quadratic_times((q, (u0, u1)): ([F192; 3], (F192, F192))) -> [F192Unreduced; 4] {
    [
        q[0].mul_unreduced(u0),
        q[0].mul_unreduced(u1) ^ q[1].mul_unreduced(u0),
        q[1].mul_unreduced(u1) ^ q[2].mul_unreduced(u0),
        q[2].mul_unreduced(u1),
    ]
}

/// `c (u_0 + X u_1)` for a cubic `c`, its coefficients unreduced.
#[inline(always)]
pub(super) fn cubic_times(c: [F192; 4], (u0, u1): (F192, F192)) -> [F192Unreduced; 5] {
    [
        c[0].mul_unreduced(u0),
        c[0].mul_unreduced(u1) ^ c[1].mul_unreduced(u0),
        c[1].mul_unreduced(u1) ^ c[2].mul_unreduced(u0),
        c[2].mul_unreduced(u1) ^ c[3].mul_unreduced(u0),
        c[3].mul_unreduced(u1),
    ]
}

/// `(c + X d)^3`: in characteristic 2 every binomial coefficient of a cube is one.
#[inline(always)]
pub(super) fn cube((c, d): (F192, F192)) -> [F192; 4] {
    let (c2, d2) = (c.square(), d.square());
    [c2 * c, c2 * d, c * d2, d2 * d]
}

/// Whether a pair's linear polynomial is zero, so that its product terms can be skipped.
#[inline(always)]
pub(super) const fn is_zero((c, d): (F192, F192)) -> bool {
    c.is_zero() && d.is_zero()
}

/// Row `k` of a pair as the linear polynomial `lo + X (lo + hi)`.
#[inline(always)]
pub(super) fn linear<const N: usize>(lo: &[F192; N], hi: &[F192; N], k: usize) -> (F192, F192) {
    (lo[k], lo[k] + hi[k])
}

/// Run the sumcheck of the tables `row` gives, whose pairs' round polynomials `pair` sums.
///
/// Sends each round's first `n_coeffs` coefficients, the rest being zero, and returns the point and each table there.
pub(super) fn rounds<const N: usize, const D: usize>(
    ps: &mut impl Transmitter,
    n: usize,
    n_coeffs: usize,
    row: impl Fn(usize) -> [F192; N] + Sync,
    pair: impl Fn(&[F192; N], &[F192; N]) -> [F192Unreduced; D] + Sync,
) -> (Vec<F192>, [F192; N]) {
    let send = |ps: &mut _, sums: [F192; D]| {
        debug_assert!(
            sums[n_coeffs..].iter().all(|c| c.is_zero()),
            "a round's degree is its shape's"
        );
        Transmitter::add_round_poly(ps, &sums[..n_coeffs], false);
    };
    let mut point = vec![F192::ZERO; n];
    let half = 1 << (n - 1);
    let mut sums = sum(half, |i| pair(&row(i), &row(i + half)));
    let mut rows: Vec<[F192; N]> = Vec::new();
    for var in (1..n).rev() {
        send(ps, sums);
        let r = ps.sample();
        point[var] = r;
        sums = if rows.is_empty() {
            let (folded, sums) = fold_rows(&row, r, var - 1, &pair);
            rows = folded;
            sums
        } else {
            fold_rows_in_place(&mut rows, r, var - 1, &pair)
        };
    }
    send(ps, sums);
    let r = ps.sample();
    point[0] = r;
    let last = match rows.as_slice() {
        [lo, hi] => fold(*lo, *hi, r),
        _ => fold(row(0), row(1), r),
    };
    (point, last)
}

/// The first fold: `2^(var + 1)` rows from the trace's `2^(var + 2)`, and the next round's sums over them.
fn fold_rows<const N: usize, const D: usize>(
    row: &(impl Fn(usize) -> [F192; N] + Sync),
    r: F192,
    var: usize,
    pair: &(impl Fn(&[F192; N], &[F192; N]) -> [F192Unreduced; D] + Sync),
) -> (Vec<[F192; N]>, [F192; D]) {
    let q = 1 << var;
    let mut rows = Vec::with_capacity(2 * q);
    let out = SendPtr(rows.spare_capacity_mut().as_mut_ptr().cast::<[F192; N]>());
    let sums = sum(q, |i| {
        let lo = fold(row(i), row(i + 2 * q), r);
        let hi = fold(row(i + q), row(i + 3 * q), r);
        // SAFETY: `i < q`, and slots `i` and `i + q` of the `2q` reserved belong to this item alone.
        unsafe {
            out.add(i).write(lo);
            out.add(i + q).write(hi);
        }
        pair(&lo, &hi)
    });
    // SAFETY: the items `0..q` wrote every slot of `0..2q`.
    unsafe { rows.set_len(2 * q) };
    (rows, sums)
}

/// A later fold, in place: the first `2^(var + 1)` of `2^(var + 2)` rows, and the next round's sums over them.
fn fold_rows_in_place<const N: usize, const D: usize>(
    rows: &mut Vec<[F192; N]>,
    r: F192,
    var: usize,
    pair: &(impl Fn(&[F192; N], &[F192; N]) -> [F192Unreduced; D] + Sync),
) -> [F192; D] {
    let q = 1 << var;
    assert_eq!(rows.len(), 4 * q);
    let base = SendPtr(rows.as_mut_ptr());
    let sums = sum(q, |i| {
        // SAFETY: item `i < q` reads slots `i`, `i + q`, `i + 2q`, `i + 3q` of the `4q`, then writes `i` and `i + q`.
        // No other item touches `i` or `i + q`, and no item writes a slot at or past `2q`.
        let (lo, hi) = unsafe {
            let lo = fold(base.add(i).read(), base.add(i + 2 * q).read(), r);
            let hi = fold(base.add(i + q).read(), base.add(i + 3 * q).read(), r);
            base.add(i).write(lo);
            base.add(i + q).write(hi);
            (lo, hi)
        };
        pair(&lo, &hi)
    });
    rows.truncate(2 * q);
    sums
}

/// `sum_{i < len} f(i)`, reduced once.
fn sum<const D: usize>(len: usize, f: impl Fn(usize) -> [F192Unreduced; D] + Sync) -> [F192; D] {
    let chunk = len.min(TASK_ROWS);
    let add = |a: [F192Unreduced; D], b: [F192Unreduced; D]| std::array::from_fn(|d| a[d] ^ b[d]);
    let sums = parallel::map_reduce(
        len / chunk,
        || [F192Unreduced::ZERO; D],
        |c| (c * chunk..(c + 1) * chunk).fold([F192Unreduced::ZERO; D], |acc, i| add(acc, f(i))),
        add,
    );
    sums.map(F192Unreduced::reduce)
}

/// Bind one variable: `lo + r (lo + hi)` entrywise.
#[inline(always)]
fn fold<const N: usize>(lo: [F192; N], hi: [F192; N], r: F192) -> [F192; N] {
    std::array::from_fn(|k| lo[k] + r * (lo[k] + hi[k]))
}
