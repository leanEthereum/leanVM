//! The spend's hashes: BLAKE2s-256 of a one-byte tag, then fixed-width fields.
//!
//! The tag shifts every field one byte past a word boundary.
//!
//! So each word written holds the last byte of one input word and the first seven bytes of the next.
//!
//! For a tag followed by two words `a` and `b`:
//!
//! ```text
//!   word 0 = tag       | a << 8
//!   word 1 = a >> 56   | b << 8
//!   word 2 = b >> 56
//! ```

use crate::Hash;
use leanvm_guest::{Stream, hash_prefix_with};

/// What a hash is of: the first byte of its message, so no two kinds of value share a hash.
#[derive(Clone, Copy)]
#[repr(u8)]
pub(crate) enum Tag {
    /// A note owner's key, from its spend key.
    Owner = 1,
    /// A note commitment, from its inner part and its value.
    Commitment = 2,
    /// A nullifier, from the nullifier key and the note's occurrence.
    Nullifier = 3,
    /// A Merkle tree node, from its two children.
    Node = 4,
    /// A note's inner part, from its owner and its randomness.
    Inner = 5,
    /// A nullifier key, from the pool's domain and the spend key.
    NullifierKey = 6,
    /// A note's occurrence, from its commitment and its leaf index.
    Occurrence = 7,
    /// The statement digest, from everything the spend makes public.
    Statement = 8,
}

impl Tag {
    /// BLAKE2s-256 of this tag and what `write` appends: `LEN` bytes in all.
    #[inline(always)]
    pub(crate) fn hash<const LEN: usize>(self, write: impl FnOnce(&mut Tagged<'_, '_>)) -> Hash {
        hash_prefix_with::<LEN>(|stream| {
            // The tag is the first byte of the first word.
            let mut message = Tagged {
                stream,
                carry: self as u64,
            };
            write(&mut message);
            // The last word: the byte the last full word carried over, and any tail.
            message.stream.write([message.carry]);
        })
    }

    /// BLAKE2s-256 of this tag and two 32-byte values: 65 bytes, two compressions.
    #[inline(always)]
    pub(crate) fn pair(self, a: &Hash, b: &Hash) -> Hash {
        self.hash::<65>(|m| {
            m.words(*a).words(*b);
        })
    }
}

/// A message being written one byte off its words: the tag, then whole-word fields, then at most a short tail.
pub(crate) struct Tagged<'s, 'a> {
    /// Where the words go.
    stream: &'s mut Stream<'a>,
    /// The bytes not yet written: the previous word's top byte, or the tag.
    carry: u64,
}

impl Tagged<'_, '_> {
    /// Append whole words, little-endian: each word's top byte waits for the next.
    #[inline(always)]
    pub(crate) fn words<const N: usize>(&mut self, words: [u64; N]) -> &mut Self {
        for word in words {
            self.stream.write([self.carry | word << 8]);
            self.carry = word >> 56;
        }
        self
    }

    /// Append the last bytes, at most seven, little-endian: they join the carried byte in the last word.
    #[inline(always)]
    pub(crate) const fn tail(&mut self, bytes: u64) {
        debug_assert!(bytes >> 56 == 0, "at most seven bytes");
        self.carry |= bytes << 8;
    }
}
