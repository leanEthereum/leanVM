//! The leanVM SDK as the leanXMSS guest sees it, for Charon: the same names and signatures as `sdk/`, no bodies.
//!
//! Charon translates the guest's own source, unchanged, against this crate in place of `sdk/`.
//!
//! Every item here is opaque: its meaning is its Lean model, in `Leanxmss/FunsExternal.lean`.
//!
//! Why not `sdk/` itself: its bodies are raw pointers and inline assembly, which Aeneas does not translate.
//!
//! Opaque, only its signatures would be used, and these are the same but for two things the models need:
//!
//! - `Stream` holds no borrow: `sdk/`'s holds the block it writes, and Aeneas cannot pass such a type to a closure.
//! - `Plain` names a value's size, alignment and bytes, so that one model of `Template::write` covers every type.
#![no_std]

/// What `Template::write` takes: an integer or an array of them, whose bytes are all initialized.
pub mod plain {
    pub trait Plain: Copy {
        /// The value's size in bytes: `size_of::<Self>()`.
        const SIZE: usize;
        /// The value's alignment in bytes: `align_of::<Self>()`.
        const ALIGN: usize;
        /// Byte `i` of the value as it lies in memory, little-endian, for `i < SIZE`.
        fn byte(self, i: usize) -> u8;
    }

    impl Plain for u8 {
        const SIZE: usize = 1;
        const ALIGN: usize = 1;
        fn byte(self, _: usize) -> u8 {
            unimplemented!()
        }
    }
    impl Plain for u16 {
        const SIZE: usize = 2;
        const ALIGN: usize = 2;
        fn byte(self, _: usize) -> u8 {
            unimplemented!()
        }
    }
    impl Plain for u32 {
        const SIZE: usize = 4;
        const ALIGN: usize = 4;
        fn byte(self, _: usize) -> u8 {
            unimplemented!()
        }
    }
    impl Plain for u64 {
        const SIZE: usize = 8;
        const ALIGN: usize = 8;
        fn byte(self, _: usize) -> u8 {
            unimplemented!()
        }
    }
    impl<T: Plain, const N: usize> Plain for [T; N] {
        const SIZE: usize = N * T::SIZE;
        const ALIGN: usize = T::ALIGN;
        fn byte(self, _: usize) -> u8 {
            unimplemented!()
        }
    }
}

use core::ops::Range;
use plain::Plain;

/// Streaming BLAKE2s-256 (the signer's randomness; verification does not call it).
pub struct Blake2s(());

impl Blake2s {
    pub const fn new() -> Self {
        unimplemented!()
    }

    pub fn update_words(&mut self, _words: &[u64]) -> &mut Self {
        unimplemented!()
    }

    pub fn finalize_words(self) -> [u64; 4] {
        unimplemented!()
    }
}

/// A one-block message of `W` words, hashed again and again.
pub struct Template<const W: usize>(());

impl<const W: usize> Template<W> {
    pub fn new(_words: [u64; W]) -> Self {
        unimplemented!()
    }

    pub fn write<T: Plain>(&mut self, _at: usize, _value: T) {
        unimplemented!()
    }

    pub fn digest(&mut self) -> [u64; 4] {
        unimplemented!()
    }

    pub fn chain<const COUNTER: usize, const VALUE: usize>(
        &mut self,
        _counters: Range<u32>,
        _value: [u64; 2],
    ) -> [u64; 2] {
        unimplemented!()
    }
}

/// A message being written for [`hash_with`], in words.
pub struct Stream(());

impl Stream {
    pub fn write<const N: usize>(&mut self, _words: [u64; N]) -> &mut Self {
        unimplemented!()
    }
}

/// BLAKE2s-256 of the words `write` puts in a [`Stream`], as four little-endian words.
pub fn hash_with(_write: impl FnOnce(&mut Stream)) -> [u64; 4] {
    unimplemented!()
}

/// A type made of 64-bit words and nothing else, so that any words are one.
///
/// # Safety
///
/// As `sdk/`'s.
pub unsafe trait Words: Sized + 'static {}

// SAFETY: a word is a word.
unsafe impl Words for u64 {}
// SAFETY: an array of word types is its elements' words, back to back.
unsafe impl<T: Words, const N: usize> Words for [T; N] {}

/// The next value of the advice, in place.
pub fn read<T: Words>() -> &'static T {
    unimplemented!()
}

/// The next value of the advice as a type from another crate, in place.
///
/// # Safety
///
/// `T` is words only, as [`Words`] says.
pub unsafe fn read_unchecked<T>() -> &'static T {
    unimplemented!()
}

/// Make a value public.
pub fn commit<T: Words>(_value: &T) {
    unimplemented!()
}

/// Size the guest's advice region, in words: nothing to translate.
#[macro_export]
macro_rules! advice_words {
    ($words:expr) => {};
}
