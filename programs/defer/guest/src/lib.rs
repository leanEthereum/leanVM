//! The next Fibonacci number from two proven ones.
//!
//! A run of the Fibonacci program (`programs/fibonacci`) on `n` outputs the digest of `n` and `F(n) mod 2^64`, so two
//! of its runs, on `n` and on `n + 1`, give `F(n + 2) = F(n) + F(n + 1)`. The guest assumes both runs rather than
//! repeat them: its proof holds once theirs are given.
#![no_std]

use leanvm_guest::hash_with;

/// The output of the Fibonacci program run on `n`, `f` being `F(n) mod 2^64`: the BLAKE2s of the two words it commits.
#[inline(always)]
pub fn fibonacci_output(n: u64, f: u64) -> [u64; 4] {
    hash_with(|stream| {
        stream.write([n, f]);
    })
}

/// `n + 2` and `F(n + 2) mod 2^64`, from `F(n)` and `F(n + 1)`.
///
/// # Panics
///
/// If `n + 2` overflows a word.
pub const fn next(n: u64, f0: u64, f1: u64) -> [u64; 2] {
    [n.checked_add(2).expect("n + 2 fits a word"), f0.wrapping_add(f1)]
}
