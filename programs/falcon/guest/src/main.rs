//! Verify the Falcon-512 signatures the advice holds: their count, then for each a public
//! key, a message and a signature.
//!
//! Each claim (key, message) is committed, so the output is the digest of the claims.
//!
//! A bad signature leaves the run without a proof.
#![no_std]
#![no_main]

use falcon::{Message, PublicKey, Signature, Verifier};
use leanvm_guest::{commit, read, read_unchecked};

leanvm_guest::advice_words!(1 << 14);

#[unsafe(no_mangle)]
extern "C" fn main() {
    let n = *read::<u64>();
    let mut verifier = Verifier::new();
    for _ in 0..n {
        // Read in place. SAFETY: both types are `repr(C)` words, with no padding, and any
        // words are one (see their definitions).
        let public_key = unsafe { read_unchecked::<PublicKey>() };
        let message = read::<Message>();
        let signature = unsafe { read_unchecked::<Signature>() };

        verifier
            .verify(public_key, message, signature)
            .expect("every signature verifies");

        commit(&public_key.h);
        commit(message);
    }
}
