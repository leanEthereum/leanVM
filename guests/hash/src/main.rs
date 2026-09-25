//! BLAKE2s-256 of the `input()[0]` bytes `0, 1, 2, ...` (mod 251) through the
//! machine's compression instruction: the `blake2s` guest's digest, at a fraction of
//! its cycles.
#![no_std]
#![no_main]

use leanvm_guest::{Blake2s, input, output};

#[unsafe(no_mangle)]
extern "C" fn main() {
    let mut hasher = Blake2s::new();
    let mut chunk = [0u8; 64];
    let (length, mut next) = (input()[0], 0u64);
    while next < length {
        let n = (length - next).min(64) as usize;
        for byte in &mut chunk[..n] {
            *byte = (next % 251) as u8;
            next += 1;
        }
        hasher.update(&chunk[..n]);
    }
    let digest = hasher.finalize();
    output(core::array::from_fn(|i| u64::from_le_bytes(digest[8 * i..8 * i + 8].try_into().unwrap())));
}
