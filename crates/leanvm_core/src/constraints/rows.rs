//! The constraint message passes a row at a time, for targets where the tiles of
//! [`super::table_message`] and its folds do not pay.

use primitives::PrimeCharacteristicRing;

use super::Summand;
use crate::PAR_THRESHOLD;
use crate::colval::ColVal;
use parallel::Chunks;
use primitives::F192;
use std::mem::MaybeUninit;
use std::ops::Deref;

/// [`super::table_message`], one row at a time.
#[inline(always)]
pub(super) fn table_message<T: ColVal, C: Deref<Target = [T]> + Sync>(
    cols: &[C],
    summand: &impl Summand,
    half: usize,
    eqr: &[F192],
    at_one: bool,
) -> [F192; 2] {
    let ncols = cols.len();
    // The X² coefficient is Q(hi + lo); linear and constant terms cannot contribute.
    let summand = |i: usize, scratch: &mut [T]| -> [F192; 2] {
        let e = eqr[i];
        let (endpoint, slope) = scratch.split_at_mut(ncols);
        for (ci, c) in cols.iter().enumerate() {
            let (lo, hi) = (c[i], c[i + half]);
            endpoint[ci] = if at_one { hi } else { lo };
            slope[ci] = lo + hi;
        }
        [(e * summand.eval(endpoint, false)), (e * summand.eval(slope, true))]
    };
    let xor = |a: [F192; 2], b: [F192; 2]| [a[0] + b[0], a[1] + b[1]];

    if half >= PAR_THRESHOLD {
        // The `2 * ncols` scratch is per-worker, not per-row: `map_reduce_with_state`
        // creates it once and threads it through every row that worker claims.
        parallel::map_reduce_with_state(
            half,
            || vec![T::ZERO; 2 * ncols],
            || [F192::ZERO; 2],
            |scratch, acc, i| *acc = xor(*acc, summand(i, scratch)),
            xor,
        )
    } else {
        let mut scratch = vec![T::ZERO; 2 * ncols];
        (0..half).fold([F192::ZERO; 2], |acc, i| xor(acc, summand(i, &mut scratch)))
    }
}

/// Fold two row pairs and accumulate their next-round summand before publishing the rows.
fn folded_message(
    ncols: usize,
    eqr: &[F192],
    summand: &impl Summand,
    at_one: bool,
    fold: impl Fn(usize, &mut [F192], &mut [F192]) + Sync,
) -> [F192; 2] {
    let accumulate = |scratch: &mut Vec<F192>, acc: &mut [F192; 2], i: usize| {
        // Layout: [next low row | next high row | their difference].
        let (lo, rest) = scratch.split_at_mut(ncols);
        let (hi, slope) = rest.split_at_mut(ncols);
        fold(i, lo, hi);
        for c in 0..ncols {
            slope[c] = lo[c] + hi[c];
        }
        let endpoint = if at_one { &*hi } else { &*lo };
        // The quadratic coefficient depends only on the difference of the endpoint rows.
        acc[0] += eqr[i] * summand.eval(endpoint, false);
        acc[1] += eqr[i] * summand.eval(slope, true);
    };

    if eqr.len() >= PAR_THRESHOLD {
        parallel::map_reduce_with_state(
            eqr.len(),
            || vec![F192::ZERO; 3 * ncols],
            || [F192::ZERO; 2],
            accumulate,
            |a, b| [a[0] + b[0], a[1] + b[1]],
        )
    } else {
        // Reuse scratch across the small final rounds without dispatching workers.
        let mut scratch = vec![F192::ZERO; 3 * ncols];
        let mut acc = [F192::ZERO; 2];
        for i in 0..eqr.len() {
            accumulate(&mut scratch, &mut acc, i);
        }
        acc
    }
}

/// [`super::fold_columns_and_message`]'s row pairs, `half / 2` of them, written into every slot of `out`.
pub(super) fn fold_columns_and_message<T: ColVal + Into<F192>, C: Deref<Target = [T]> + Sync>(
    cols: &[C],
    out: &mut [MaybeUninit<F192>],
    rk: F192,
    summand: &impl Summand,
    eqr: &[F192],
    at_one: bool,
) -> [F192; 2] {
    let ncols = cols.len();
    let half = cols[0].len() / 2;
    let pairs = half / 2;
    let interp = |a: T, b: T| a.into() + (a + b).mul_e(rk);
    let (lo, hi) = out.split_at_mut(pairs * ncols);
    let lo = Chunks::new(lo, ncols);
    let hi = Chunks::new(hi, ncols);
    folded_message(ncols, eqr, summand, at_one, |i, a, b| {
        for (c, col) in cols.iter().enumerate() {
            a[c] = interp(col[i], col[i + half]);
            b[c] = interp(col[i + pairs], col[i + pairs + half]);
        }
        // SAFETY: task i owns row i in each disjoint output half for the whole dispatch.
        unsafe {
            lo.get(i).write_copy_of_slice(a);
            hi.get(i).write_copy_of_slice(b);
        }
    })
}

/// [`super::fold_rows_and_message`]'s row pairs, in the four quarters of `table`'s rows.
pub(super) fn fold_rows_and_message(
    table: &mut [F192],
    ncols: usize,
    rk: F192,
    summand: &impl Summand,
    eqr: &[F192],
    at_one: bool,
) -> [F192; 2] {
    let half = table.len() / (2 * ncols);
    let pairs = half / 2;
    // Each task owns one row in all four quarters, including its two output rows.
    let (left, right) = table.split_at_mut(half * ncols);
    let (q0, q1) = left.split_at_mut(pairs * ncols);
    let (q2, q3) = right.split_at_mut(pairs * ncols);
    let q0 = Chunks::new(q0, ncols);
    let q1 = Chunks::new(q1, ncols);
    let q2 = Chunks::new(q2, ncols);
    let q3 = Chunks::new(q3, ncols);
    folded_message(ncols, eqr, summand, at_one, |i, a, b| {
        // SAFETY: task i exclusively borrows row i in each disjoint quarter exactly once.
        let (lo, hi, upper_lo, upper_hi) = unsafe { (q0.get(i), q1.get(i), q2.get(i), q3.get(i)) };
        for c in 0..ncols {
            a[c] = lo[c] + (lo[c] + upper_lo[c]) * rk;
            b[c] = hi[c] + (hi[c] + upper_hi[c]) * rk;
        }
        // Read all four input rows before overwriting either output row.
        lo.copy_from_slice(a);
        hi.copy_from_slice(b);
    })
}
