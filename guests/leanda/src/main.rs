//! Check the `input()[0]` encoded blobs of the advice, and output `H(root, H(L))`.
//!
//! The advice is the dual codeword `L`, `m` entries of three words, then the blobs.
//!
//! A blob that is not a codeword leaves the run without a proof.
#![no_std]
#![no_main]

use leanda::{CELLS, M};
use leanvm_guest::{advice, input, output};

/// The advice region: `L` and one blob, which is what one proof holds.
const ADVICE_WORDS: usize = 4 * M;
/// The most blobs the advice region holds.
const MAX_BLOBS: usize = (ADVICE_WORDS - 3 * M) / M;

leanvm_guest::advice_words!(ADVICE_WORDS);

#[unsafe(no_mangle)]
extern "C" fn main() {
    let n = input()[0] as usize;
    assert!(n <= MAX_BLOBS, "the blobs fit the advice");
    // The advice, read in place:
    //
    //     words 0..3m      L, three limbs per entry
    //     words 3m..4m     the blob
    let (dual, blobs) = advice().split_at(3 * M);
    let dual = dual.as_chunks::<3>().0.try_into().unwrap();
    let blobs = &blobs.as_chunks::<M>().0[..n];
    // Scratch for the cell digests of every row, padding included.
    let mut cells = [[[0; 4]; CELLS]; MAX_BLOBS.next_power_of_two()];
    output(leanda::check(dual, blobs, &mut cells).expect("every blob is a codeword"));
}
