//! `F(n) mod 2^64`, `n` read from the advice: the output is the digest of `n` and `F(n)`.
#![no_std]
#![no_main]

use leanvm_guest::{commit, read};

#[unsafe(no_mangle)]
extern "C" fn main() {
    let n = *read::<u64>();
    let (mut a, mut b) = (0u64, 1u64);
    for _ in 0..n {
        (a, b) = (b, a.wrapping_add(b));
    }
    commit(&[n, a]);
}
