//! Check the encoded blobs of the advice, and commit the root and `H(L)`.
//!
//! The advice is the blob count, the dual codeword `L` (`m` entries of three words), then
//! the blobs.
//!
//! A blob that is not a codeword leaves the run without a proof.
#![no_std]
#![no_main]

use leanda::{CELLS, Dual, M};
use leanvm_guest::ext::Registers;
use leanvm_guest::{commit, read, read_slice};

/// The most blobs a run checks: one, which is what one proof holds.
const MAX_BLOBS: usize = 1;

leanvm_guest::advice_words!((1 + 3 * M + MAX_BLOBS * M).next_power_of_two());

#[unsafe(no_mangle)]
extern "C" fn main() {
    // The advice, read in place.
    let n = *read::<u64>() as usize;
    assert!(n <= MAX_BLOBS, "the blobs fit the advice");
    let dual = read::<[Dual; M]>();
    let blobs = read_slice::<[u64; M]>(n);
    // Scratch for the cell digests of every row, padding included.
    let mut cells = [[[0; 4]; CELLS]; MAX_BLOBS.next_power_of_two()];
    let mut e = Registers::new();
    commit(&leanda::check(&mut e, dual, blobs, &mut cells).expect("every blob is a codeword"));
}
