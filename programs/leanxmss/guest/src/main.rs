//! Verify the leanXMSS signatures the advice holds: their count, then for each a public
//! key, a leaf index, a message and a signature.
//!
//! Each claim (key, leaf index, message) is committed, so the output is the digest of the
//! claims.
//!
//! A bad signature leaves the run without a proof.
#![no_std]
#![no_main]

use leanvm_guest::{commit, read, read_unchecked};
use leanxmss::{LeafIndex, Message, PublicKey, Signature};

leanvm_guest::advice_words!(1 << 16);
leanvm_guest::stack_words!(1 << 9);

#[unsafe(no_mangle)]
extern "C" fn main() {
    let n = *read::<u64>();
    for _ in 0..n {
        // Read in place. SAFETY: both types are `repr(C)` words, with no padding, and any
        // words are one (see their definitions).
        let public_key = unsafe { read_unchecked::<PublicKey>() };
        let leaf_index = *read::<u64>();
        let message = read::<Message>();
        let signature = unsafe { read_unchecked::<Signature>() };

        // A leaf index past `2^32 - 1` would be committed whole but verified truncated.
        let leaf = LeafIndex::try_from(leaf_index).expect("a leaf index below 2^32");
        leanxmss::verify(public_key, leaf, message, signature).expect("every signature verifies");

        commit(&public_key.merkle_root);
        commit(&public_key.public_param);
        commit(&leaf_index);
        commit(message);
    }
}
