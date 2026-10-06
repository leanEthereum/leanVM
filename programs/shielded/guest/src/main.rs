//! Check the shielded transfers the advice holds, and commit their statement digests.
//!
//! The advice: the count, then each spend's words.
//!
//! The output is the digest of the statement digests, in order.
//!
//! A spend breaking a rule leaves the run without a proof.
#![no_std]
#![no_main]

use leanvm_guest::{commit, read};
use shielded::Spend;

leanvm_guest::advice_words!(1 << 18);

#[unsafe(no_mangle)]
extern "C" fn main() {
    let n = *read::<u64>();
    for _ in 0..n {
        // Read in place: a spend is words.
        let spend = read::<Spend>();
        let digest = spend.verify().expect("every spend follows the pool's rules");
        commit(&digest);
    }
}
