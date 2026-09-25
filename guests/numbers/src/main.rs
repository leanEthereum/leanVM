//! Multiplication and division at work: `base^exponent mod modulus` through 128-bit
//! products, a gcd, and signed division, on the first three input words.
#![no_std]
#![no_main]

use leanvm_guest::{input, output};

fn pow_mod(mut base: u64, mut exponent: u64, modulus: u64) -> u64 {
    let mut result = 1 % modulus;
    base %= modulus;
    while exponent > 0 {
        if exponent & 1 == 1 {
            result = (result as u128 * base as u128 % modulus as u128) as u64;
        }
        base = (base as u128 * base as u128 % modulus as u128) as u64;
        exponent >>= 1;
    }
    result
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

#[unsafe(no_mangle)]
extern "C" fn main() {
    let [base, exponent, modulus, _] = input();
    assert!(modulus != 0, "no modulus");
    let signed = (base as i64).wrapping_neg() / (exponent as i64 | 1);
    let mixed = ((base as i32) / (exponent as i32 | 1)) as i64 % 1000;
    output([
        pow_mod(base, exponent, modulus),
        gcd(base, modulus),
        signed as u64,
        mixed as u64,
    ]);
}
