//! The BLAKE2s compression instruction, and its access to its block.

use super::InstructionClass;
use crate::rv::entry::Class;

/// One BLAKE2s compression instance, `blake2s rs1, rs2`: the finalization word, the counter, the block.
///
/// It compresses the 128-byte block at `rs1`, with the byte counter in `rs2`.
///
/// The block holds three parts:
///
/// - bytes 0 to 31: the chaining value;
/// - bytes 32 to 63: where the new chaining value goes;
/// - bytes 64 to 127: the message.
///
/// Word `k` of the block is the cell at `rs1 ^ 8k`.
///
/// That is `rs1 + 8k` when `rs1` is aligned to the block, as the guest library ensures.
///
/// An unaligned `rs1` permutes the words.
///
/// That is a guest bug, but a deterministic and provable one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Hash {
    /// The finalization word: one of the legal words.
    pub flags: u64,
    /// The byte counter.
    pub t: u64,
    /// The block's words as found.
    pub block: [u64; Hash::WORDS],
}

impl Hash {
    /// The chaining value's byte offset.
    pub const H: u64 = 0;
    /// The result's byte offset.
    pub const OUT: u64 = 32;
    /// The message's byte offset.
    pub const M: u64 = 64;
    /// The block's words.
    pub const WORDS: usize = 16;
    /// The block's bytes.
    pub const BLOCK_BYTES: u64 = 8 * Self::WORDS as u64;
    /// The finalization word of the last block: all ones.
    pub const FINAL: u64 = u32::MAX as u64;
}

impl InstructionClass for Hash {
    const CLASS: Class = Class::Hash;

    /// Not the last block, or the last.
    const LEGAL: &'static [u64] = &[0, Self::FINAL];

    /// The four words the instruction writes back: the new chaining value.
    type Output = [u64; 4];

    fn eval(&self) -> [u64; 4] {
        debug_assert!(Self::LEGAL.contains(&self.flags));

        // Split each 64-bit word into its two 32-bit halves, low first.
        let block = &self.block;
        let mut h: [u32; 8] = std::array::from_fn(|i| (block[i / 2] >> (32 * (i % 2))) as u32);
        let m: [u32; 16] = std::array::from_fn(|i| (block[8 + i / 2] >> (32 * (i % 2))) as u32);

        // Compress, then pair the halves back into words.
        primitives::hash::compress(&mut h, &m, self.t, self.flags == Self::FINAL);
        std::array::from_fn(|i| h[2 * i] as u64 | (h[2 * i + 1] as u64) << 32)
    }

    /// The counter, the finalization word, the chaining value, then the message.
    fn input_words(&self) -> Vec<u64> {
        [self.t, self.flags]
            .into_iter()
            .chain(self.block[..4].iter().chain(&self.block[8..]).copied())
            .collect()
    }

    fn output_words(out: &[u64; 4]) -> Vec<u64> {
        out.to_vec()
    }
}

/// A hash row's access to its block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockAccess {
    /// The block's words as the row found them.
    pub block: [u64; Hash::WORDS],
    /// The new chaining value, written to the block's result words.
    pub out: [u64; 4],
}

impl From<Hash> for BlockAccess {
    /// The access of a compression: its block, and the result it writes.
    fn from(hash: Hash) -> Self {
        Self {
            block: hash.block,
            out: hash.eval(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::semantics::tests::edge_word;
    use proptest::prelude::*;
    use proptest::sample::select;
    use proptest::strategy::BoxedStrategy;

    /// Any compression instance with a legal finalization word.
    impl Arbitrary for Hash {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            (
                select(Self::LEGAL),
                edge_word(),
                proptest::array::uniform16(edge_word()),
            )
                .prop_map(|(flags, t, block)| Self { flags, t, block })
                .boxed()
        }
    }
}
