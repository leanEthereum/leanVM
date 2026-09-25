//! `F(n) mod 2^64`, `n` being the first input word.
#![no_std]
#![no_main]

use leanvm_guest::{input, output};

#[unsafe(no_mangle)]
extern "C" fn main() {
    let n = input()[0];
    let (mut a, mut b) = (0u64, 1u64);
    for _ in 0..n {
        (a, b) = (b, a.wrapping_add(b));
    }
    output([a, 0, 0, 0]);
}
