//! Streaming BLAKE2s-256: the machine's compression instruction on the VM, portable Rust elsewhere.
//!
//! Words are the fast path.
//!
//! The machine moves a word in one instruction, and a byte-aligned value one byte at a time.

use core::mem::MaybeUninit;
use core::ops::Range;
use plain::Plain;

/// The initialization vector with the parameter block folded in, as little-endian words.
///
/// The parameter block says: no key, a 32-byte digest, so `0x0101_0020` is folded into the first lane.
pub(crate) const IV: [u64; 4] = [
    0xBB67_AE85_6A09_E667 ^ 0x0101_0020,
    0xA54F_F53A_3C6E_F372,
    0x9B05_688C_510E_527F,
    0x5BE0_CD19_1F83_D9AB,
];

/// Streaming BLAKE2s-256.
pub struct Blake2s {
    /// The chaining value.
    h: [u64; 4],
    /// The message block being filled.
    m: [u64; 8],
    /// Bytes in the message block.
    filled: usize,
    /// Bytes compressed before the message block.
    done: u64,
}

impl Default for Blake2s {
    fn default() -> Self {
        Self::new()
    }
}

impl Blake2s {
    #[inline(always)]
    pub const fn new() -> Self {
        Self {
            h: IV,
            m: [0; 8],
            filled: 0,
            done: 0,
        }
    }

    /// Absorb bytes.
    #[inline(always)]
    pub fn update(&mut self, mut data: &[u8]) -> &mut Self {
        while !data.is_empty() {
            // A full block is compressed only now, once more input is known to follow.
            self.make_room();
            // Copy as much as the block still takes.
            let (at, n) = (self.filled, data.len().min(64 - self.filled));
            self.m_bytes()[at..at + n].copy_from_slice(&data[..n]);
            self.filled += n;
            data = &data[n..];
        }
        self
    }

    /// Absorb the little-endian bytes of words, the same as absorbing those bytes.
    ///
    /// Inlined with its length known, a call folds to plain word stores.
    #[inline(always)]
    pub fn update_words(&mut self, mut words: &[u64]) -> &mut Self {
        // A block filled to a byte that is not a word boundary takes the byte path.
        if !self.filled.is_multiple_of(8) {
            for word in words {
                self.update(&word.to_le_bytes());
            }
            return self;
        }
        if !words.is_empty() {
            self.make_room();
        }
        // Whole blocks go straight from the input to the compression, with no copy.
        //
        // Why `> 8`: a block with nothing after it may be the last, which is compressed differently.
        while self.filled == 0 && words.len() > 8 {
            let (block, rest) = words.split_first_chunk::<8>().unwrap();
            self.done += 64;
            self.h = compress(&self.h, block, self.done, false);
            words = rest;
        }
        // The rest, at most one block, goes word by word into the buffer.
        for &word in words {
            self.make_room();
            self.m[self.filled / 8] = word;
            self.filled += 8;
        }
        self
    }

    /// The digest.
    #[inline(always)]
    pub fn finalize(self) -> [u8; 32] {
        let words = self.finalize_words();
        // Digest byte `i` is byte `i % 8` of word `i / 8`.
        core::array::from_fn(|i| (words[i / 8] >> (8 * (i % 8))) as u8)
    }

    /// The digest as four little-endian words.
    #[inline(always)]
    pub fn finalize_words(mut self) -> [u64; 4] {
        // BLAKE2s pads the last block with zeros.
        //
        // Each word keeps its first `filled - 8i` bytes, clamped to `0..=8`:
        //
        //     filled = 20:  word 0 keeps 8,  word 1 keeps 8,  word 2 keeps 4,  words 3..8 keep 0
        //
        // Why a mask: a zeroing loop of unknown length becomes a `memset` call.
        for (i, word) in self.m.iter_mut().enumerate() {
            let keep = self.filled.saturating_sub(8 * i).min(8);
            *word &= if keep == 8 { u64::MAX } else { (1 << (8 * keep)) - 1 };
        }
        // The counter of the last block counts every byte of the message.
        compress(&self.h, &self.m, self.done + self.filled as u64, true)
    }

    pub fn hash(data: &[u8]) -> [u8; 32] {
        let mut hasher = Self::new();
        hasher.update(data);
        hasher.finalize()
    }

    /// Compress the block if it is full.
    #[inline(always)]
    fn make_room(&mut self) {
        if self.filled == 64 {
            // The counter covers every byte up to the end of this block.
            self.done += 64;
            self.h = compress(&self.h, &self.m, self.done, false);
            self.filled = 0;
        }
    }

    /// The message block as its 64 bytes.
    #[inline(always)]
    fn m_bytes(&mut self) -> &mut [u8; 64] {
        const { assert!(cfg!(target_endian = "little"), "the message words are little-endian") };
        // SAFETY: eight words are readable and writable as their 64 bytes.
        unsafe { &mut *(&raw mut self.m).cast() }
    }
}

/// A one-block message of `W` words, hashed again and again: rewritten in place between hashes, where it changed.
///
/// Hashes of one shape write the words they share (a key, a prefix, the padding) once, not once per hash: the
/// message stays in the block the instruction reads, which writes the compression and nothing else.
pub struct Template<const W: usize> {
    block: Block,
}

impl<const W: usize> Template<W> {
    #[inline(always)]
    pub fn new(words: [u64; W]) -> Self {
        const { assert!(W <= 8, "a template is one block") };
        let mut m = [0; 8];
        m[..W].copy_from_slice(&words);
        Self {
            block: Block {
                h: IV,
                out: MaybeUninit::uninit(),
                m,
            },
        }
    }

    /// Rewrite the message from word `at`.
    #[inline(always)]
    pub fn set<const N: usize>(&mut self, at: usize, words: [u64; N]) {
        self.block.m[..W][at..at + N].copy_from_slice(&words);
    }

    /// Write `value` at byte `at` of the message: a field narrower than a word, or an offset already in bytes,
    /// which then needs no shift to become an address as [`Self::set`]'s word index does.
    #[inline(always)]
    pub fn write<T: Plain>(&mut self, at: usize, value: T) {
        assert!(
            at.is_multiple_of(align_of::<T>()) && size_of::<T>() <= 8 * W && at <= 8 * W - size_of::<T>(),
            "an aligned field inside the message"
        );
        // SAFETY: the field is inside the message and aligned (checked above), and `T` has no padding, so the
        // message stays initialized words.
        unsafe { self.block.m.as_mut_ptr().byte_add(at).cast::<T>().write(value) }
    }

    /// The digest of the message as it stands, as four little-endian words.
    #[inline(always)]
    pub fn digest(&mut self) -> [u64; 4] {
        self.block.compress(8 * W as u64, true)
    }

    /// The digest of the message's first `LEN` bytes, as four little-endian words: a message ending inside its last
    /// word, whose bytes from `LEN` on must be zero, as BLAKE2s pads the last block with zeros.
    #[inline(always)]
    pub fn digest_prefix<const LEN: usize>(&mut self) -> [u64; 4] {
        const {
            assert!(
                8 * W - 8 < LEN && LEN <= 8 * W,
                "a length inside the message's last word"
            );
        };
        self.block.compress(LEN as u64, true)
    }

    /// A hash chain: for each `c` in `counters`, write `c` as the `u32` at message byte `COUNTER` and `value` at
    /// message byte `VALUE`, then `value` becomes the digest's first two words. Returns the last `value`, or `value`
    /// itself for no counters.
    ///
    /// On the VM the loop is written by hand: eight instructions a step, the compression one of them.
    #[inline(always)]
    pub fn chain<const COUNTER: usize, const VALUE: usize>(
        &mut self,
        counters: Range<u32>,
        value: [u64; 2],
    ) -> [u64; 2] {
        const {
            assert!(
                COUNTER.is_multiple_of(4) && COUNTER + 4 <= 8 * W,
                "a u32 field inside the message"
            );
        };
        const {
            assert!(
                VALUE.is_multiple_of(8) && VALUE + 16 <= 8 * W,
                "two words inside the message"
            );
        };
        assert!(counters.start <= counters.end, "a chain of no negative length");
        #[cfg(all(target_arch = "riscv64", target_os = "none"))]
        // SAFETY: the block is this template's, its chaining value and message initialized, the fields inside the
        // message (checked above), and the range is not reversed (checked above).
        unsafe {
            crate::precompile::blake2s_chain::<COUNTER, VALUE>(
                &mut self.block,
                8 * W as u64,
                counters.start,
                counters.end,
                value,
            )
        }
        #[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
        counters.fold(value, |value, c| {
            self.write(COUNTER, c);
            self.write(VALUE, value);
            let [d0, d1, ..] = self.digest();
            [d0, d1]
        })
    }

    /// [`Self::chain`] with the counter a whole word at message byte `COUNTER`, going up by `step` a hash: for each
    /// `c` in `first, first + step, ..` up to `end`, write `c` as the word at message byte `COUNTER` and `value` at
    /// message byte `VALUE`, then `value` becomes the digest's first two words. Returns the last `value`, or `value`
    /// itself if `first == end`.
    ///
    /// A counter in a word's high half, with the rest of the word fixed in `first`, then costs a 64-bit store a hash
    /// rather than a 32-bit one: the loop is the same eight instructions. `end` must be `first` plus a multiple of
    /// `step`, or the chain never ends.
    #[inline(always)]
    pub fn chain_word<const COUNTER: usize, const VALUE: usize>(
        &mut self,
        first: u64,
        end: u64,
        step: u64,
        value: [u64; 2],
    ) -> [u64; 2] {
        const {
            assert!(
                COUNTER.is_multiple_of(8) && COUNTER + 8 <= 8 * W,
                "a word inside the message"
            );
        };
        const {
            assert!(
                VALUE.is_multiple_of(8) && VALUE + 16 <= 8 * W,
                "two words inside the message"
            );
        };
        #[cfg(all(target_arch = "riscv64", target_os = "none"))]
        // SAFETY: the block is this template's, its chaining value and message initialized, and the fields inside the
        // message (checked above).
        unsafe {
            crate::precompile::blake2s_chain_word::<COUNTER, VALUE>(
                &mut self.block,
                8 * W as u64,
                first,
                end,
                step,
                value,
            )
        }
        #[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
        {
            let (mut c, mut value) = (first, value);
            while c != end {
                self.write(COUNTER, c);
                self.write(VALUE, value);
                let [d0, d1, ..] = self.digest();
                value = [d0, d1];
                c = c.wrapping_add(step);
            }
            value
        }
    }
}

/// What [`Template::write`] takes: an integer or an array of them, whose bytes are all initialized.
mod plain {
    pub trait Plain: Copy {}
    impl Plain for u8 {}
    impl Plain for u16 {}
    impl Plain for u32 {}
    impl Plain for u64 {}
    impl<T: Plain, const N: usize> Plain for [T; N] {}
}

/// BLAKE2s-256 of the words `write` puts in a [`Stream`], as four little-endian words.
///
/// The stream writes straight into the block the instruction reads, and its position stays in registers: the block
/// is this call's, and the stream only borrows it. [`Blake2s`] copies its message into the instruction's block at
/// each compression instead, which keeps a hasher that lives across calls in registers too.
#[inline(always)]
pub fn hash_with(write: impl FnOnce(&mut Stream<'_>)) -> [u64; 4] {
    with_stream(|stream| {
        write(stream);
        stream.finish()
    })
}

/// BLAKE2s-256 of the first `LEN` bytes of the words `write` puts in a stream, as four little-endian words.
///
/// The message ends inside its last word, whose bytes from `LEN` on must be zero: BLAKE2s pads with zeros.
///
/// It may span blocks: a template's prefix digest is the one-block counterpart.
#[inline(always)]
pub fn hash_prefix_with<const LEN: usize>(write: impl FnOnce(&mut Stream<'_>)) -> [u64; 4] {
    with_stream(|stream| {
        write(stream);
        stream.finish_prefix(LEN as u64)
    })
}

/// Run `f` on a fresh stream over a block this frame owns.
#[inline(always)]
fn with_stream(f: impl FnOnce(&mut Stream<'_>) -> [u64; 4]) -> [u64; 4] {
    // Only the chaining value is written here: the stream writes each message word before a compression reads it,
    // padding the last block itself.
    let mut block = MaybeUninit::<Block>::uninit();
    // SAFETY: a field of the block this frame owns.
    unsafe { (&raw mut (*block.as_mut_ptr()).h).write(IV) };
    f(&mut Stream {
        block: &mut block,
        filled: 0,
        done: 0,
    })
}

/// A message being written for [`hash_with`], in words: each full block absorbed once more of it follows.
pub struct Stream<'a> {
    /// The block: its chaining value written, and its message's words below `filled`, which are all eight once a
    /// block is full.
    block: &'a mut MaybeUninit<Block>,
    /// Words in the message block.
    filled: usize,
    /// Bytes absorbed before it.
    done: u64,
}

impl Stream<'_> {
    /// Append words to the message.
    #[inline(always)]
    pub fn write<const N: usize>(&mut self, words: [u64; N]) -> &mut Self {
        for word in words {
            // A full block is absorbed only now, once more of the message is known to follow.
            if self.filled == 8 {
                self.absorb();
            }
            self.put([word]);
        }
        self
    }

    /// Append `count` arrays of words, `array(i)` for `i` in order: [`Self::write`] of each.
    ///
    /// Where `N` divides a block and the message is at a multiple of `N` words, the arrays go a block at a time: the
    /// compiler unrolls a block's arrays, so their words go to fixed places, with no check that the block is full.
    #[inline(always)]
    pub fn write_each<const N: usize>(&mut self, count: usize, mut array: impl FnMut(usize) -> [u64; N]) -> &mut Self {
        if !(const { N > 0 && 8 % N == 0 } && self.filled.is_multiple_of(N)) {
            for i in 0..count {
                self.write(array(i));
            }
            return self;
        }
        let mut i = 0;
        // The rest of this block.
        while self.filled < 8 && i < count {
            self.put(array(i));
            i += 1;
        }
        // Then whole blocks, the full one absorbed only once an array is known to follow.
        while i < count {
            self.absorb();
            if i + 8 / N <= count {
                for j in 0..8 / N {
                    self.put(array(i + j));
                }
                i += 8 / N;
            } else {
                while i < count {
                    self.put(array(i));
                    i += 1;
                }
            }
        }
        self
    }

    /// Write words where the block has room for them.
    #[inline(always)]
    fn put<const N: usize>(&mut self, words: [u64; N]) {
        for word in words {
            let filled = self.filled;
            self.message()[filled].write(word);
            self.filled += 1;
        }
    }

    /// The message words, written or not.
    #[inline(always)]
    fn message(&mut self) -> &mut [MaybeUninit<u64>; 8] {
        // SAFETY: the message of the block this stream holds, as words that need not be initialized.
        unsafe { &mut *(&raw mut (*self.block.as_mut_ptr()).m).cast() }
    }

    /// The block, once its chaining value and its eight message words are written.
    #[inline(always)]
    fn full(&mut self) -> &mut Block {
        debug_assert_eq!(self.filled, 8);
        // SAFETY: the chaining value and every message word are written (`filled` is 8 only once each word below it
        // is), and `out` may be uninitialized.
        unsafe { self.block.assume_init_mut() }
    }

    /// Absorb the full message block, which more of the message follows.
    #[inline(always)]
    fn absorb(&mut self) {
        self.done += 64;
        let done = self.done;
        let block = self.full();
        block.h = block.compress(done, false);
        self.filled = 0;
    }

    /// The digest: the last block zero-padded, the counter every byte of the message.
    #[inline(always)]
    fn finish(&mut self) -> [u64; 4] {
        let t = self.done + 8 * self.filled as u64;
        self.finish_prefix(t)
    }

    /// The digest of the message's first `len` bytes, which end inside its last word.
    ///
    /// BLAKE2s counts bytes, not words: the counter is `len`, the bytes past it already zero.
    #[inline(always)]
    fn finish_prefix(&mut self, len: u64) -> [u64; 4] {
        let written = self.done + 8 * self.filled as u64;
        assert!(
            len <= written && written < len + 8,
            "a length inside the message's last word"
        );
        while self.filled < 8 {
            self.put([0]);
        }
        self.full().compress(len, true)
    }
}

/// The block the instruction works on, in words.
///
/// ```text
///     words 0..4    chaining value, read
///     words 4..8    compression, written
///     words 8..16   message, read
/// ```
///
/// Aligned to its size, so word `k` is the cell at `base ^ 8k`.
#[repr(C, align(128))]
pub(crate) struct Block {
    pub(crate) h: [u64; 4],
    /// Written by the instruction before anything reads it.
    pub(crate) out: MaybeUninit<[u64; 4]>,
    pub(crate) m: [u64; 8],
}

impl Block {
    /// The compression of `m` onto `h`, in place, `t` bytes into the message.
    #[inline(always)]
    // The instruction writes `out`; off the VM the portable compression only reads the block.
    #[cfg_attr(
        not(all(target_arch = "riscv64", target_os = "none")),
        allow(clippy::needless_pass_by_ref_mut)
    )]
    pub(crate) fn compress(&mut self, t: u64, last: bool) -> [u64; 4] {
        #[cfg(all(target_arch = "riscv64", target_os = "none"))]
        // SAFETY: the block is this borrow's, its chaining value and message initialized; the instruction writes
        // the compression.
        unsafe {
            crate::precompile::blake2s_compress_in_place(self, t, last);
            self.out.assume_init()
        }
        #[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
        {
            portable::compress(&self.h, &self.m, t, last)
        }
    }
}

/// The compression of a message block onto a chaining value, `t` bytes into the message:
/// the machine's instruction on the VM, portable Rust elsewhere.
#[inline(always)]
fn compress(h: &[u64; 4], m: &[u64; 8], t: u64, last: bool) -> [u64; 4] {
    #[cfg(all(target_arch = "riscv64", target_os = "none"))]
    {
        crate::precompile::blake2s_compress(h, m, t, last)
    }
    #[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
    {
        portable::compress(h, m, t, last)
    }
}

/// The compression function of RFC 7693, section 3.2, for a host.
#[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
mod portable {
    /// The initialization vector, which also seeds the second half of the working vector.
    const IV: [u32; 8] = [
        0x6A09_E667,
        0xBB67_AE85,
        0x3C6E_F372,
        0xA54F_F53A,
        0x510E_527F,
        0x9B05_688C,
        0x1F83_D9AB,
        0x5BE0_CD19,
    ];
    /// The message word each round feeds to each mixing step.
    const SIGMA: [[usize; 16]; 10] = [
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
        [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
        [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
        [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
        [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
        [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
        [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
        [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
        [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
        [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
    ];

    /// The 32-bit little-endian lane `i` of a word array.
    const fn lane(words: &[u64], i: usize) -> u32 {
        (words[i / 2] >> (32 * (i % 2))) as u32
    }

    pub fn compress(h: &[u64; 4], block: &[u64; 8], t: u64, last: bool) -> [u64; 4] {
        // The message as sixteen 32-bit words.
        let m: [u32; 16] = core::array::from_fn(|i| lane(block, i));
        // The working vector: the chaining value, then the IV.
        let mut v: [u32; 16] = core::array::from_fn(|i| if i < 8 { lane(h, i) } else { IV[i - 8] });
        // The 64-bit byte counter enters lanes 12 and 13.
        v[12] ^= t as u32;
        v[13] ^= (t >> 32) as u32;
        // The last block inverts lane 14.
        if last {
            v[14] = !v[14];
        }
        // Ten rounds: four column steps, then four diagonal steps.
        for s in &SIGMA {
            let mut g = |a: usize, b: usize, c: usize, d: usize, x: u32, y: u32| {
                v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
                v[d] = (v[d] ^ v[a]).rotate_right(16);
                v[c] = v[c].wrapping_add(v[d]);
                v[b] = (v[b] ^ v[c]).rotate_right(12);
                v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
                v[d] = (v[d] ^ v[a]).rotate_right(8);
                v[c] = v[c].wrapping_add(v[d]);
                v[b] = (v[b] ^ v[c]).rotate_right(7);
            };
            g(0, 4, 8, 12, m[s[0]], m[s[1]]);
            g(1, 5, 9, 13, m[s[2]], m[s[3]]);
            g(2, 6, 10, 14, m[s[4]], m[s[5]]);
            g(3, 7, 11, 15, m[s[6]], m[s[7]]);
            g(0, 5, 10, 15, m[s[8]], m[s[9]]);
            g(1, 6, 11, 12, m[s[10]], m[s[11]]);
            g(2, 7, 8, 13, m[s[12]], m[s[13]]);
            g(3, 4, 9, 14, m[s[14]], m[s[15]]);
        }
        // The new chaining value `h ^ v_lo ^ v_hi`, packed back into words.
        let word = |i: usize| u64::from(lane(h, i) ^ v[i] ^ v[i + 8]);
        core::array::from_fn(|k| word(2 * k) | word(2 * k + 1) << 32)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::hash::{digest_words, hash};
    use primitives::test_util::Rng;

    /// The reference BLAKE2s-256 of `bytes`, as little-endian words.
    fn reference(bytes: &[u8]) -> [u64; 4] {
        digest_words(&hash(bytes))
    }

    /// A template and the bytes its message should be, rewritten together.
    struct Mirror<const W: usize> {
        template: Template<W>,
        bytes: [u8; 64],
    }

    impl<const W: usize> Mirror<W> {
        fn new(words: [u64; W]) -> Self {
            let mut bytes = [0; 64];
            for (k, word) in words.iter().enumerate() {
                bytes[8 * k..8 * k + 8].copy_from_slice(&word.to_le_bytes());
            }
            Self {
                template: Template::new(words),
                bytes,
            }
        }

        fn put(&mut self, at: usize, le: &[u8]) {
            self.bytes[at..at + le.len()].copy_from_slice(le);
        }

        fn check(&mut self) {
            let expected = reference(&self.bytes[..8 * W]);
            assert_eq!(self.template.digest(), expected, "{W} words");
            assert_eq!(self.template.digest(), expected, "hashing leaves the message as it was");
        }
    }

    fn hashes_its_message<const W: usize>(rng: &mut Rng) {
        Mirror::<W>::new(core::array::from_fn(|_| rng.next_u64())).check();
    }

    #[test]
    fn a_template_is_the_blake2s_of_its_message() {
        // Invariant: a template of `W` words hashes as BLAKE2s-256 of those `8W` bytes, the empty message included.
        let mut rng = Rng::new(0x7E3);
        hashes_its_message::<0>(&mut rng);
        hashes_its_message::<1>(&mut rng);
        hashes_its_message::<2>(&mut rng);
        hashes_its_message::<3>(&mut rng);
        hashes_its_message::<4>(&mut rng);
        hashes_its_message::<5>(&mut rng);
        hashes_its_message::<6>(&mut rng);
        hashes_its_message::<7>(&mut rng);
        hashes_its_message::<8>(&mut rng);
    }

    fn hashes_its_prefix<const LEN: usize>(rng: &mut Rng) {
        let mut mirror = Mirror::<7>::new(core::array::from_fn(|_| rng.next_u64()));
        // The last word keeps its first `LEN - 48` bytes.
        let last = rng.next_u64() & (u64::MAX >> (8 * (56 - LEN)));
        mirror.template.set(6, [last]);
        mirror.put(48, &last.to_le_bytes());
        assert_eq!(
            mirror.template.digest_prefix::<LEN>(),
            reference(&mirror.bytes[..LEN]),
            "{LEN} bytes"
        );
    }

    #[test]
    fn a_template_prefix_is_the_blake2s_of_those_bytes() {
        // Invariant: a message ending inside its last word, zero after it, hashes as BLAKE2s-256 of its bytes alone.
        let mut rng = Rng::new(0x7E5);
        hashes_its_prefix::<49>(&mut rng);
        hashes_its_prefix::<52>(&mut rng);
        hashes_its_prefix::<56>(&mut rng);
    }

    /// A random offset of a `size`-byte field, aligned to its size and inside a message of `W` words.
    fn offset<const W: usize>(rng: &mut Rng, size: usize) -> usize {
        rng.next_u64() as usize % (8 * W / size) * size
    }

    fn rewrites<const W: usize>(rng: &mut Rng) {
        let mut mirror = Mirror::<W>::new(core::array::from_fn(|_| rng.next_u64()));
        mirror.check();
        for _ in 0..256 {
            let value = rng.next_u64();
            match rng.next_u64() % 7 {
                0 => {
                    let at = offset::<W>(rng, 8) / 8;
                    mirror.template.set(at, [value]);
                    mirror.put(8 * at, &value.to_le_bytes());
                }
                1 => {
                    let at = offset::<W>(rng, 8) / 8;
                    let at = at.min(W - 2);
                    mirror.template.set(at, [value, !value]);
                    mirror.put(8 * at, &value.to_le_bytes());
                    mirror.put(8 * at + 8, &(!value).to_le_bytes());
                }
                2 => {
                    let at = offset::<W>(rng, 1);
                    mirror.template.write(at, value as u8);
                    mirror.put(at, &[value as u8]);
                }
                3 => {
                    let at = offset::<W>(rng, 2);
                    mirror.template.write(at, value as u16);
                    mirror.put(at, &(value as u16).to_le_bytes());
                }
                4 => {
                    let at = offset::<W>(rng, 4);
                    mirror.template.write(at, value as u32);
                    mirror.put(at, &(value as u32).to_le_bytes());
                }
                5 => {
                    let at = offset::<W>(rng, 8);
                    mirror.template.write(at, value);
                    mirror.put(at, &value.to_le_bytes());
                }
                _ => {
                    // A digest-sized field at any word, not only at a multiple of its size.
                    let at = offset::<W>(rng, 8).min(8 * W - 16);
                    mirror.template.write(at, [value, !value]);
                    mirror.put(at, &value.to_le_bytes());
                    mirror.put(at + 8, &(!value).to_le_bytes());
                }
            }
            mirror.check();
        }
        // The last field of each width ends at the message's end, and is inside it.
        mirror.template.write(8 * W - 1, 0xA5u8);
        mirror.put(8 * W - 1, &[0xA5]);
        mirror.template.write(8 * W - 2, 0xA55Au16);
        mirror.put(8 * W - 2, &0xA55Au16.to_le_bytes());
        mirror.template.write(8 * W - 4, 0xA55A_5AA5u32);
        mirror.put(8 * W - 4, &0xA55A_5AA5u32.to_le_bytes());
        mirror.check();
    }

    #[test]
    fn a_rewritten_template_is_the_blake2s_of_its_new_message() {
        // Invariant: after any run of `set`s and `write`s, a template hashes the message those leave, as bytes in
        // little-endian words; hashing leaves the message as it was.
        //
        // Fixture: the chain step's shape (6 words), a whole block, and two words; a field of every width.
        let mut rng = Rng::new(0x7E4);
        rewrites::<2>(&mut rng);
        rewrites::<6>(&mut rng);
        rewrites::<8>(&mut rng);
    }

    #[test]
    #[should_panic(expected = "an aligned field inside the message")]
    fn write_rejects_a_misaligned_field() {
        Template::new([0; 6]).write(2, 0u32);
    }

    #[test]
    #[should_panic(expected = "an aligned field inside the message")]
    fn write_rejects_a_field_past_the_message_inside_the_block() {
        // Words 6 and 7 of the block are padding, not the message.
        Template::new([0; 6]).write(48, 0u32);
    }

    #[test]
    #[should_panic(expected = "an aligned field inside the message")]
    fn write_rejects_a_field_wider_than_the_message() {
        Template::new([0; 1]).write(0, [0u64; 2]);
    }

    #[test]
    #[should_panic(expected = "an aligned field inside the message")]
    fn write_rejects_an_offset_whose_end_would_wrap() {
        Template::new([0; 6]).write(usize::MAX, 0u8);
    }

    /// `chain::<COUNTER, VALUE>` over every length from 0 to 16 and a few first counters, against the reference
    /// BLAKE2s of each step's message; the template is left holding the last step's message.
    fn chains<const W: usize, const COUNTER: usize, const VALUE: usize>(rng: &mut Rng) {
        for first in [0, 1, 0x1234_5678, u32::MAX - 16] {
            for len in 0..=16 {
                let mut mirror = Mirror::<W>::new(core::array::from_fn(|_| rng.next_u64()));
                let start = [rng.next_u64(), rng.next_u64()];
                let mut value = start;
                for c in first..first + len {
                    mirror.put(COUNTER, &c.to_le_bytes());
                    mirror.put(VALUE, &value[0].to_le_bytes());
                    mirror.put(VALUE + 8, &value[1].to_le_bytes());
                    let [d0, d1, ..] = reference(&mirror.bytes[..8 * W]);
                    value = [d0, d1];
                }
                let chained = mirror.template.chain::<COUNTER, VALUE>(first..first + len, start);
                assert_eq!(
                    chained, value,
                    "counter at {COUNTER}, value at {VALUE}, {len} steps from {first}"
                );
                mirror.check();
            }
        }
    }

    #[test]
    fn a_chain_is_its_steps_hashed_in_turn() {
        // Invariant: `chain` is the fold of its steps, each writing its counter and the value, the value becoming the
        // digest's first two words; no steps return the value as given.
        //
        // Fixture: leanXMSS's and leanSPHINCS's shape (6 words, the counter in the tweak, the value after the
        // parameter), the counter after the value and in the last word, a whole block, and counters up to `u32::MAX`.
        let mut rng = Rng::new(0xC4A);
        chains::<6, 4, 32>(&mut rng);
        chains::<6, 44, 0>(&mut rng);
        chains::<4, 24, 0>(&mut rng);
        chains::<8, 0, 48>(&mut rng);
        chains::<8, 60, 8>(&mut rng);
    }

    #[test]
    #[should_panic(expected = "a chain of no negative length")]
    fn chain_rejects_a_reversed_range() {
        let (start, end) = (2, 1);
        Template::new([0; 6]).chain::<4, 32>(start..end, [0; 2]);
    }

    /// The reference BLAKE2s-256 of up to 256 words, as little-endian bytes.
    fn reference_of_words(words: &[u64]) -> [u64; 4] {
        let mut bytes = [0; 8 * 256];
        for (k, word) in words.iter().enumerate() {
            bytes[8 * k..8 * k + 8].copy_from_slice(&word.to_le_bytes());
        }
        reference(&bytes[..8 * words.len()])
    }

    /// `hash_with` of `words`: the first `prefix` one at a time, then `N` at a time, the rest one at a time.
    fn in_pieces<const N: usize>(words: &[u64], prefix: usize) -> [u64; 4] {
        hash_with(|s| {
            let (head, rest) = words.split_at(prefix);
            for &word in head {
                s.write([word]);
            }
            let (pieces, tail) = rest.as_chunks::<N>();
            for &piece in pieces {
                s.write(piece);
            }
            for &word in tail {
                s.write([word]);
            }
        })
    }

    #[test]
    fn hash_with_is_the_blake2s_of_its_words() {
        // Invariant: whatever the pieces it is written in, `hash_with` hashes as BLAKE2s-256 of the words' bytes.
        //
        // Fixture: every length from the empty message through one block, one block and a word, to five blocks, each
        // starting its pieces at every offset within a block, so that pieces straddle every block boundary. The stream
        // leaves the message unwritten until a word goes there, so a last block shorter than the one before still
        // holds that block's words past its end: each length that ends short of a block checks they hash as zeros.
        let mut rng = Rng::new(0x5E6);
        let words: [u64; 40] = core::array::from_fn(|_| rng.next_u64());
        for len in 0..=40 {
            let message = &words[..len];
            let expected = reference_of_words(message);
            for prefix in 0..=len.min(8) {
                let check = |digest, n| assert_eq!(digest, expected, "{len} words, {n} at a time after {prefix}");
                check(in_pieces::<1>(message, prefix), 1);
                check(in_pieces::<2>(message, prefix), 2);
                check(in_pieces::<3>(message, prefix), 3);
                check(in_pieces::<4>(message, prefix), 4);
                check(in_pieces::<8>(message, prefix), 8);
                check(in_pieces::<11>(message, prefix), 11);
            }
        }
    }

    /// `hash_prefix_with` of `LEN` random bytes, written a word at a time, against the reference of those bytes.
    fn streams_its_prefix<const LEN: usize>(rng: &mut Rng) {
        // The message's words: `LEN` random bytes, then zeros to the end of the last word.
        let mut bytes = [0u8; 8 * 40];
        bytes[..LEN].iter_mut().for_each(|b| *b = rng.next_u64() as u8);
        let words: [u64; 40] =
            core::array::from_fn(|k| u64::from_le_bytes(bytes[8 * k..8 * k + 8].try_into().unwrap()));
        let digest = hash_prefix_with::<LEN>(|s| {
            for &word in &words[..LEN.div_ceil(8)] {
                s.write([word]);
            }
        });
        assert_eq!(digest, reference(&bytes[..LEN]), "{LEN} bytes");
    }

    #[test]
    fn hash_prefix_with_is_the_blake2s_of_those_bytes() {
        // Invariant: the counter is the byte length, not the words written.
        //
        // Fixture: lengths ending at every kind of place.
        //
        //     1, 33, 63      inside the first block
        //     64             on its end: the block is the last one, compressed once
        //     65             one byte into a second block
        //     129, 265       three and five blocks, ending one byte past a block and a word
        let mut rng = Rng::new(0x9EF);
        streams_its_prefix::<1>(&mut rng);
        streams_its_prefix::<33>(&mut rng);
        streams_its_prefix::<63>(&mut rng);
        streams_its_prefix::<64>(&mut rng);
        streams_its_prefix::<65>(&mut rng);
        streams_its_prefix::<129>(&mut rng);
        streams_its_prefix::<265>(&mut rng);
    }

    /// `write_each` of `count` arrays of `N` words after `prefix` single words and before `suffix` more, against the
    /// reference of the same words; the arrays must be asked for once each, in order.
    fn writes_each<const N: usize>(words: &[u64; 256]) {
        for prefix in 0..=8 {
            for count in 0..=12 {
                for suffix in 0..=2 {
                    let len = prefix + N * count + suffix;
                    let mut next = 0;
                    let digest = hash_with(|s| {
                        for &word in &words[..prefix] {
                            s.write([word]);
                        }
                        s.write_each(count, |i| {
                            assert_eq!(i, next, "arrays asked for in order");
                            next += 1;
                            core::array::from_fn::<_, N, _>(|k| words[prefix + N * i + k])
                        });
                        for &word in &words[prefix + N * count..len] {
                            s.write([word]);
                        }
                    });
                    assert_eq!(next, count, "each array asked for once");
                    assert_eq!(
                        digest,
                        reference_of_words(&words[..len]),
                        "{count} arrays of {N} words after {prefix}, then {suffix}"
                    );
                }
            }
        }
    }

    #[test]
    fn write_each_puts_each_array_where_write_would() {
        // Invariant: `write_each(count, array)` is `write(array(i))` for `i` in order, whether it takes the block at a
        // time path (`N` divides 8 and the message is at a multiple of `N`) or the word at a time one.
        //
        // Fixture: arrays of every width dividing a block, and of 3, 5 and 16 words, which do not; empty arrays; every
        // starting offset in a block, up to 12 arrays (several blocks), then nothing or more words.
        let mut rng = Rng::new(0x5E7);
        let words = core::array::from_fn(|_| rng.next_u64());
        writes_each::<0>(&words);
        writes_each::<1>(&words);
        writes_each::<2>(&words);
        writes_each::<3>(&words);
        writes_each::<4>(&words);
        writes_each::<5>(&words);
        writes_each::<8>(&words);
        writes_each::<16>(&words);
    }
}
