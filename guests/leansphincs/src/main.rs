//! Verify the `input()[0]` leanSPHINCS signatures the advice holds, laid out as entries.
//!
//! The output is the digest of their claims.
//!
//! A bad signature leaves the run without a proof.
#![no_std]
#![no_main]

use leanvm_guest::{advice, input, output};

leanvm_guest::advice_words!(1 << 16);

#[unsafe(no_mangle)]
extern "C" fn main() {
    // The entries are read in place from the advice.
    let entries = leansphincs::entries(advice(), input()[0] as usize).expect("the entries fit the advice");
    output(leansphincs::verify_batch(entries).expect("every signature verifies"));
}
