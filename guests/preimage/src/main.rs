//! The BLAKE2s-256 digest of a message the prover supplies: the advice's first word
//! is the message's byte length, the words after it hold its bytes. A proof says the
//! prover knows a preimage of the output.
#![no_std]
#![no_main]

use leanvm_guest::{Blake2s, advice, output};

#[unsafe(no_mangle)]
extern "C" fn main() {
    let advice = advice();
    let length = advice[0] as usize;
    assert!(length <= 8 * (advice.len() - 1));
    let mut hasher = Blake2s::new();
    for (i, word) in advice[1..].iter().enumerate() {
        let n = length.saturating_sub(8 * i).min(8);
        hasher.update(&word.to_le_bytes()[..n]);
    }
    let digest = hasher.finalize();
    output(core::array::from_fn(|i| u64::from_le_bytes(digest[8 * i..8 * i + 8].try_into().unwrap())));
}
