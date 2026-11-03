//! The grinds: the least randomizer or encoding counter a scheme admits, searched a
//! batch of counters at a time.

use primitives::hash::{self, OUT_LANES, OUT_LEN, RATE};
use std::sync::atomic::{AtomicU64, Ordering};

/// Counters a worker claims and hashes at once.
const BATCH: usize = 64;

/// The least `c` in `0..limit` whose hash `admit` accepts. Counter `c`'s hash input is
/// `data` with `words(c)` XORed into its two little-endian words from byte `at`, which
/// `data` leaves zero: they lie in the final block, so the blocks before it are absorbed
/// once and a counter costs one permutation.
///
/// Workers claim batches in ascending order from one counter and stop at the first
/// claim past the least hit so far, so every batch below the answer is searched
/// however the pool interleaves. That determinism is what keeps one key to one
/// codeword.
pub fn least_admissible(
    data: &[u8],
    at: usize,
    limit: u64,
    words: impl Fn(u64) -> [u64; 2] + Sync,
    admit: impl Fn(&[u8; OUT_LEN]) -> bool + Sync,
) -> Option<u64> {
    let lane = at % RATE / 8;
    assert!(at.is_multiple_of(8) && at / RATE == data.len() / RATE && lane + 2 <= RATE / 8);
    let template = hash::final_state(data);
    let (next, least) = (AtomicU64::new(0), AtomicU64::new(u64::MAX));
    parallel::for_each(parallel::num_threads(), |_| {
        let mut input = [0u64; 2 * BATCH];
        let mut digests = [[0u64; OUT_LANES]; BATCH];
        loop {
            let first = next.fetch_add(BATCH as u64, Ordering::Relaxed);
            if first >= limit.min(least.load(Ordering::Relaxed)) {
                return;
            }
            let lanes = (limit - first).min(BATCH as u64) as usize;
            for (c, pair) in (first..).zip(input.as_chunks_mut::<2>().0[..lanes].iter_mut()) {
                *pair = words(c);
            }
            hash::permute_many_from(&template, lane, 2, &input[..2 * lanes], &mut digests[..lanes]);
            if let Some(hit) = digests[..lanes].iter().position(|d| admit(&digest_bytes(d))) {
                // Every later claim of this worker starts past this hit.
                least.fetch_min(first + hit as u64, Ordering::Relaxed);
                return;
            }
        }
    });
    let least = least.into_inner();
    (least != u64::MAX).then_some(least)
}

fn digest_bytes(words: &[u64; OUT_LANES]) -> [u8; OUT_LEN] {
    let mut out = [0u8; OUT_LEN];
    for (chunk, word) in out.as_chunks_mut::<8>().0.iter_mut().zip(words) {
        *chunk = word.to_le_bytes();
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A counter is admissible when its digest's first byte is below `bound`.
    fn admits(bound: u8) -> impl Fn(&[u8; OUT_LEN]) -> bool + Sync {
        move |digest| digest[0] < bound
    }

    /// The one-counter-at-a-time search the batched one has to agree with.
    fn scalar(data: &[u8], at: usize, limit: u64, admit: impl Fn(&[u8; OUT_LEN]) -> bool) -> Option<u64> {
        (0..limit).find(|&counter| {
            let mut input = data.to_vec();
            let n = (input.len() - at).min(8);
            input[at..at + n].copy_from_slice(&counter.to_le_bytes()[..n]);
            admit(&hash::hash(&input))
        })
    }

    #[test]
    fn the_batched_search_finds_the_least_admissible_counter() {
        // One block, and a counter in the third block of a longer input.
        for (len, at) in [(80, 64), (292, 288)] {
            let data: Vec<u8> = (0..len).map(|i| if i < at { i as u8 } else { 0 }).collect();
            for bound in [255, 64, 8] {
                for limit in [1, 33, 4097, 20_000] {
                    assert_eq!(
                        least_admissible(&data, at, limit, |c| [c, 0], admits(bound)),
                        scalar(&data, at, limit, admits(bound)),
                        "len {len}, bound {bound}, limit {limit}"
                    );
                }
            }
        }
    }

    #[test]
    fn a_limit_that_admits_nothing_is_none() {
        assert_eq!(least_admissible(&[0; 16], 0, 0, |c| [c, 0], admits(0)), None);
        assert_eq!(least_admissible(&[0; 16], 0, 100, |c| [c, 0], admits(0)), None);
    }
}
