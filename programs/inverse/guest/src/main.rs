//! Invert the BN254 base-field elements the advice holds: how, their count, then each element below `p`. Each inverse
//! is committed, so the output is the digest of the inverses, whichever way they were found.
#![no_std]
#![no_main]

use inverse::{BY_EXPONENT, BY_HINT, checked, from_canonical, inverse, inverse_by_hint, to_canonical};
use leanvm_guest::{commit, hint, read, read_slice};

#[unsafe(no_mangle)]
extern "C" fn main() {
    let &[how, n] = read::<[u64; 2]>();
    for x in read_slice::<[u64; 4]>(n as usize) {
        let x = from_canonical(x);
        let inv = match how {
            BY_EXPONENT => inverse(&x),
            BY_HINT => inverse_by_hint(&x),
            // A prover's wrong hint, which the check refuses.
            _ => checked(&x, *hint(|| inverse(&x).map(|word| word ^ 1))),
        };
        commit(&to_canonical(&inv));
    }
}
