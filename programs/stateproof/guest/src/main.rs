//! Verify L1 state reads against one block, and commit their claims.
//!
//! The advice:
//!
//! ```text
//!   header                     its length in bytes, then its words
//!   n                          the reads
//!   n times:
//!     address, slot            3 words, 4 words
//!     account proof            its node count, then each node as a header is
//!     storage proof            the same
//! ```
//!
//! The output is the digest of the block hash, then each read's address, account, slot and value.
//!
//! A bad proof leaves the run without a proof.
#![no_std]
#![no_main]

use leanvm_guest::{commit, read, read_slice};
use stateproof::{Address, Hash, Node};

leanvm_guest::advice_words!(1 << 15);

/// A byte string: its length in bytes, then its words.
fn bytes() -> Node<'static> {
    let len = *read::<u64>() as usize;
    Node::new(read_slice(len.div_ceil(8)), len).expect("the words hold the bytes")
}

/// A proof: its node count, then its nodes, read as the walk takes them.
fn proof() -> impl Iterator<Item = Node<'static>> {
    let n = *read::<u64>();
    (0..n).map(|_| bytes())
}

#[unsafe(no_mangle)]
extern "C" fn main() {
    // The block: its hash is the anchor every claim hangs from.
    let header = bytes();
    let state_root = stateproof::state_root(&header).expect("the header holds a state root");
    commit(&header.hash());

    let n = *read::<u64>();
    for _ in 0..n {
        let address = read::<Address>();
        let slot = read::<Hash>();

        // The walk consumes every node of a proof it accepts.
        // So the next read starts where this one ends.
        let account = stateproof::account(&state_root, address, proof()).expect("the account proof verifies");
        let value = stateproof::storage(&account.storage_root, slot, proof()).expect("the storage proof verifies");

        commit(address);
        commit(&account);
        commit(slot);
        commit(&value);
    }
}
