//! A stable sort for the provers, short where the standard library's is long: a bottom-up merge sort of the indices,
//! then the permutation applied in place by swaps.

use std::cmp::Ordering;

/// The indices `0..n` sorted by `cmp`, stably: equal ones keep their order.
pub fn order_by(n: usize, mut cmp: impl FnMut(usize, usize) -> Ordering) -> Vec<usize> {
    let mut order = vec![0; n];
    for (i, slot) in order.iter_mut().enumerate() {
        *slot = i;
    }
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

/// The indices `0..n` sorted by `key`, stably.
pub fn order_by_key<K: Ord>(n: usize, mut key: impl FnMut(usize) -> K) -> Vec<usize> {
    order_by(n, |a, b| key(a).cmp(&key(b)))
}

/// `v` sorted by `cmp`, stably: equal elements keep their order.
pub fn sort_by<T>(v: &mut [T], mut cmp: impl FnMut(&T, &T) -> Ordering) {
    let n = v.len();
    let order = order_by(n, |i, j| cmp(&v[i], &v[j]));
    // Position `k` takes the element at `order[k]`: each cycle of the permutation once, by swaps.
    let mut placed = vec![false; n];
    for start in 0..n {
        let mut k = start;
        while !placed[k] {
            placed[k] = true;
            let next = order[k];
            if next == start {
                break;
            }
            v.swap(k, next);
            k = next;
        }
    }
}

/// `v` sorted by `key`, stably.
pub fn sort_by_key<T, K: Ord>(v: &mut [T], mut key: impl FnMut(&T) -> K) {
    sort_by(v, |a, b| key(a).cmp(&key(b)));
}

/// `v` sorted, stably.
pub fn sort<T: Ord>(v: &mut [T]) {
    sort_by(v, T::cmp);
}

#[cfg(test)]
mod tests {
    /// Up to seven elements with pseudo-random keys out of three, so with ties, against the standard library's
    /// stable sort.
    #[test]
    fn matches_the_standard_stable_sort() {
        for n in 0..8u32 {
            for seed in 0..5040u32 {
                let v: Vec<(u32, u32)> = (0..n)
                    .map(|i| ((seed.wrapping_mul(2654435761) >> (3 * i)) % 3, i))
                    .collect();
                let (mut ours, mut std) = (v.clone(), v.clone());
                super::sort_by_key(&mut ours, |&(k, _)| k);
                std.sort_by_key(|&(k, _)| k);
                assert_eq!(ours, std);
            }
        }
    }
}
