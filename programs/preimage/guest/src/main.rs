//! The BLAKE2s-256 digest of a message the prover supplies: the advice's first word
//! is the message's byte length, the words after it hold its bytes. Only the digest is
//! committed, so a proof says the prover knows a preimage of it.
#![no_std]
#![no_main]

use leanvm_guest::{Blake2s, commit, read, read_slice};

#[unsafe(no_mangle)]
extern "C" fn main() {
    let length = *read::<u64>() as usize;
    let mut hasher = Blake2s::new();
    for (i, word) in read_slice::<u64>(length.div_ceil(8)).iter().enumerate() {
        let n = length.saturating_sub(8 * i).min(8);
        hasher.update(&word.to_le_bytes()[..n]);
    }
    commit(&hasher.finalize_words());
}
