//! BLAKE2s-256 of the bytes `0, 1, 2, ...` (mod 251), as many as the advice's first word says,
//! through the machine's compression instruction: the `blake2s` guest's digest, at a fraction
//! of its cycles. The length and the digest are committed.
#![no_std]
#![no_main]

use leanvm_guest::{Blake2s, commit, read};

#[unsafe(no_mangle)]
extern "C" fn main() {
    let mut hasher = Blake2s::new();
    let mut chunk = [0u8; 64];
    let (length, mut next) = (*read::<u64>(), 0u64);
    while next < length {
        let n = (length - next).min(64) as usize;
        for byte in &mut chunk[..n] {
            *byte = (next % 251) as u8;
            next += 1;
        }
        hasher.update(&chunk[..n]);
    }
    commit(&length);
    commit(&hasher.finalize_words());
}
