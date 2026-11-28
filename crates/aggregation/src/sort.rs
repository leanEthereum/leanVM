//! A stable sort of indices, short where the standard library's is long: a bottom-up merge sort.

use std::cmp::Ordering;

/// The indices `0..n` sorted by `key`, stably: equal keys keep their order.
pub(super) fn order_by_key<K: Ord>(n: usize, mut key: impl FnMut(usize) -> K) -> Vec<usize> {
    let mut cmp = |a, b| key(a).cmp(&key(b));
    let mut order: Vec<usize> = (0..n).collect();
    let mut merged = vec![0; n];
    let mut width = 1;
    while width < n {
        for lo in (0..n).step_by(2 * width) {
            let (mid, hi) = ((lo + width).min(n), (lo + 2 * width).min(n));
            let (mut i, mut j) = (lo, mid);
            for slot in &mut merged[lo..hi] {
                // The left run takes ties, which keeps the sort stable.
                if j == hi || i < mid && cmp(order[i], order[j]) != Ordering::Greater {
                    *slot = order[i];
                    i += 1;
                } else {
                    *slot = order[j];
                    j += 1;
                }
            }
        }
        std::mem::swap(&mut order, &mut merged);
        width *= 2;
    }
    order
}

#[cfg(test)]
mod tests {
    /// Up to seven elements with pseudo-random keys out of three, so with ties, against the standard library's
    /// stable sort.
    #[test]
    fn matches_the_standard_stable_sort() {
        for n in 0..8u32 {
            for seed in 0..5040u32 {
                let keys: Vec<u32> = (0..n).map(|i| (seed.wrapping_mul(2654435761) >> (3 * i)) % 3).collect();
                let mut std: Vec<usize> = (0..keys.len()).collect();
                std.sort_by_key(|&i| keys[i]);
                assert_eq!(super::order_by_key(keys.len(), |i| keys[i]), std);
            }
        }
    }
}
