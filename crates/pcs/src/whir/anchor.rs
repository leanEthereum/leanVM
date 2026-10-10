//! Commitment-time MLE anchors, restricted to the occupied lane prefix.

use super::commit::CommitmentShape;
use fiat_shamir::arith::Arith;
use primitives::field::{F64, F192};
use primitives::multilinear::mle_eval_par;

/// Evaluate the witness with its omitted, whole-lane tail equal to zero.
/// Only the base evaluator allocates its small working tables; the lane
/// interpolation neither lifts the witness nor materializes high eq weights.
pub(crate) fn anchor_value(message: &[F64], log_rows: usize, point: &[F192]) -> F192 {
    assert!(log_rows <= point.len() && point.len() < usize::BITS as usize);
    let block_len = 1usize << log_rows;
    assert!(!message.is_empty() && message.len().is_multiple_of(block_len));
    let n_lanes = message.len() >> log_rows;
    let (low, high) = point.split_at(log_rows);
    let used_vars = (usize::BITS - (n_lanes - 1).leading_zeros()) as usize;
    assert!(used_vars <= high.len(), "occupied lanes fit the anchor cube");

    fn eval(message: &[F64], low: &[F192], high: &[F192]) -> F192 {
        let Some((&r, rest)) = high.split_last() else {
            return mle_eval_par(message, low);
        };
        let split = 1usize << (low.len() + rest.len());
        if message.len() <= split {
            let lo = eval(message, low, rest);
            lo + r * lo
        } else {
            let (left, right) = message.split_at(split);
            let lo = eval(left, low, rest);
            let hi = eval(right, low, rest);
            lo + r * (lo + hi)
        }
    }

    let value = eval(message, low, &high[..used_vars]);
    if used_vars == high.len() {
        value
    } else {
        let zero_tail = high[used_vars..]
            .iter()
            .fold(F192::ONE, |acc, &r| acc * (F192::ONE + r));
        value * zero_tail
    }
}

/// The first `count` entries of `seed * eq(point, .)`, without a full-cube table.
pub(crate) fn eq_prefix(point: &[F192], count: usize, mut seed: F192) -> Vec<F192> {
    if count == 0 {
        return Vec::new();
    }
    let used_vars = (usize::BITS - (count - 1).leading_zeros()) as usize;
    assert!(used_vars <= point.len(), "prefix fits the equality cube");
    for &r in &point[used_vars..] {
        seed *= F192::ONE + r;
    }
    let mut out = vec![F192::ZERO; count];
    out[0] = seed;
    for (j, &r) in point[..used_vars].iter().enumerate() {
        let half = 1usize << j;
        let high_len = half.min(count - half);
        for i in 0..half {
            let hi = out[i] * r;
            out[i] += hi;
            if i < high_len {
                out[half + i] = hi;
            }
        }
    }
    out
}

/// The multilinear extension of the anchor weight on the occupied support.
///
/// The low coordinates span whole lane blocks. On the high coordinates the
/// weight is `sum_{lane < n_lanes} eq(lane, r) * eq(lane, point)`, not the
/// full-cube equality product when the last lanes are absent.
pub(crate) fn anchor_eq_at<A: Arith>(a: &mut A, shape: CommitmentShape, r: &[A::E], point: &[A::E]) -> A::E {
    assert!(shape.valid());
    assert_eq!(r.len(), shape.log_n);
    assert_eq!(point.len(), shape.log_n);
    if shape.n_lanes == 1usize << shape.log_batch_size {
        return a.eq_eval(r, point);
    }
    let log_rows = shape.log_n - shape.log_batch_size;
    let low = a.eq_eval(&r[..log_rows], &point[..log_rows]);
    let mut full = a.one();
    let mut partial = full;
    let mut started = false;
    let mut j = 0;
    while j < shape.log_batch_size {
        let rj = r[log_rows + j];
        let xj = point[log_rows + j];
        // full_j sums over all Boolean lower-j lane bits. partial_j sums
        // over the prefix below n_lanes mod 2^j; it is zero until its first 1.
        let sum = a.add(rj, xj);
        let factor = a.add_const(sum, F192::ONE);
        let bit = (shape.n_lanes >> j) & 1;
        if bit != 0 || started {
            let hi = a.mul(rj, xj);
            let lo = a.add(factor, hi);
            if bit != 0 {
                let lower_full = if j == 0 { lo } else { a.mul(lo, full) };
                partial = if started {
                    a.mul_add(hi, partial, lower_full)
                } else {
                    lower_full
                };
                started = true;
            } else {
                partial = a.mul(lo, partial);
            }
        }
        // Higher zero count bits never consume full_j, so do not build it.
        if shape.n_lanes >> (j + 1) != 0 {
            full = if j == 0 { factor } else { a.mul(full, factor) };
        }
        j += 1;
    }
    a.mul(low, partial)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fiat_shamir::arith::Native;

    fn point(n: usize, salt: u64) -> Vec<F192> {
        (0..n)
            .map(|j| F192::new(salt + 3 * j as u64, salt + j as u64 + 7, 11))
            .collect()
    }

    fn eq_bits(index: usize, point: &[F192]) -> F192 {
        point.iter().enumerate().fold(F192::ONE, |acc, (j, &r)| {
            acc * if (index >> j) & 1 == 0 { F192::ONE + r } else { r }
        })
    }

    #[test]
    fn prefix_weights_respect_non_power_of_two_and_zero_high_tails() {
        let seed = F192::new(23, 17, 5);
        let mut r = point(8, 19);
        for count in [1, 3, 64, 255] {
            let expected: Vec<_> = (0..count).map(|i| seed * eq_bits(i, &r)).collect();
            assert_eq!(eq_prefix(&r, count, seed), expected, "count {count}");
        }
        r[7] = F192::ONE;
        for count in [1, 3, 64] {
            assert_eq!(eq_prefix(&r, count, seed), vec![F192::ZERO; count]);
        }
    }

    #[test]
    fn anchor_value_and_terminal_weight_use_only_occupied_lanes() {
        let log_rows = 3;
        let log_batch_size = 6;
        let log_n = log_rows + log_batch_size;
        let r = point(log_n, 29);
        let x = point(log_n, 43);
        for n_lanes in [1, 3, 64] {
            let message: Vec<F64> = (0..(n_lanes << log_rows)).map(|i| F64(13 * i as u64 + 7)).collect();
            let expected_value = message
                .iter()
                .enumerate()
                .fold(F192::ZERO, |sum, (i, &v)| sum + eq_bits(i, &r).mul_base(v));
            assert_eq!(anchor_value(&message, log_rows, &r), expected_value);
            let expected_weight = (0..message.len()).fold(F192::ZERO, |sum, i| sum + eq_bits(i, &r) * eq_bits(i, &x));
            let shape = CommitmentShape {
                log_n,
                log_batch_size,
                log_inv_rate: 1,
                n_lanes,
            };
            assert_eq!(
                anchor_eq_at(&mut Native, shape, &r, &x),
                expected_weight,
                "lanes {n_lanes}"
            );
        }
    }
}
