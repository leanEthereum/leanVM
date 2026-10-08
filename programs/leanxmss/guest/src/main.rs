//! Verify the leanXMSS signatures the advice holds: their count, then for each a public
//! key, a leaf index, a message and a signature.
//!
//! Each claim (key, leaf index, message) is committed, so the output is the digest of the
//! claims.
//!
//! A bad signature leaves the run without a proof.
#![no_std]
#![no_main]

use leanvm_guest::{Words, commit, read, read_slice};
use leanxmss::{LeafIndex, Message, PublicKey, Signature, Verifier};

leanvm_guest::advice_words!(1 << 16);

/// What a signature is checked against, and what the guest commits: nine words.
#[repr(C)]
struct Claim {
    public_key: PublicKey,
    leaf_index: u64,
    message: Message,
}

/// One signature's advice: the claim, then the signature.
#[repr(C)]
struct Entry {
    claim: Claim,
    signature: Signature,
}

// SAFETY: `repr(C)` words, with no padding, and any words are one (see the fields' definitions).
unsafe impl Words for Claim {}
// SAFETY: as for `Claim`.
unsafe impl Words for Entry {}

#[unsafe(no_mangle)]
extern "C" fn main() {
    let n = *read::<u64>();
    let mut verifier = Verifier::new();
    // Read in place, all at once: one bounds check for the batch rather than one per field.
    for entry in read_slice::<Entry>(usize::try_from(n).expect("a count of entries")) {
        let Entry { claim, signature } = entry;
        let Claim {
            public_key,
            leaf_index,
            message,
        } = claim;

        // A leaf index past `2^32 - 1` would be committed whole but verified truncated.
        let leaf = LeafIndex::try_from(*leaf_index).expect("a leaf index below 2^32");
        verifier
            .verify(public_key, leaf, message, signature)
            .expect("every signature verifies");

        // The claim's words are the key's, the leaf index and the message's, in that order.
        commit(claim);
    }
}
