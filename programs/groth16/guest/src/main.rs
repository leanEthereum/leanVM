//! Verify the Groth16 proofs the advice holds: their count, then for each a proof and its
//! public inputs.
//!
//! Each proof's public inputs are committed, so the output is the digest of the statements
//! proven; the verification key is the program's own.
//!
//! An invalid proof leaves the run without a proof.
#![no_std]
#![no_main]

use groth16::{Inputs, Proof, verify};
use leanvm_guest::{commit, read, read_unchecked};

leanvm_guest::advice_words!(1 << 12);

#[unsafe(no_mangle)]
extern "C" fn main() {
    let n = *read::<u64>();
    for _ in 0..n {
        // Read in place. SAFETY: `Proof` is `repr(C)` words, with no padding, and any words are
        // one (see its definition).
        let proof = unsafe { read_unchecked::<Proof>() };
        let inputs = read::<Inputs>();

        verify(proof, inputs).expect("every proof verifies");

        commit(inputs);
    }
}
