//! The address space: three disjoint regions of words.

use std::ops::Range;

/// A region of the address space: a power of two of words at a fixed base.
///
/// Each base is a multiple of its region's largest size.
///
/// So word `i` sits at `base + (i << log_word_bytes)`, which is also `base ^ (i << log_word_bytes)`.
///
/// The proof relies on that: an address coordinate is then linear in the word index.
///
/// The three regions tile `0x1000_0000..0x8000_0000`:
///
/// - the text at `0x1000_0000`, up to 2^26 instructions of 4 bytes;
/// - the advice at `0x2000_0000`, up to 2^26 words of 8 bytes;
/// - RAM at `0x4000_0000`, up to 2^27 words of 8 bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Region {
    /// The byte address of word zero.
    base: u64,
    /// The base-two logarithm of a word's size in bytes.
    log_word_bytes: u32,
    /// The base-two logarithm of the most words the region holds.
    max_log_words: usize,
}

impl Region {
    /// The instructions.
    ///
    /// The base is nonzero, so no Rust function of a guest sits at the null address.
    pub const TEXT: Self = Self::new(0x1000_0000..0x2000_0000, 4);

    /// A second read-write memory, filled by the prover before the run.
    ///
    /// The statement does not fix its contents.
    ///
    /// A guest must check whatever it reads from it.
    pub const ADVICE: Self = Self::new(0x2000_0000..0x4000_0000, 8);

    /// The read-write memory whose initial image the program fixes.
    ///
    /// It lies in the text's 2 GiB window, as the medany code model needs.
    ///
    /// A full RAM ends at `0x8000_0000`.
    ///
    /// Its last 2 KiB are out of reach of an absolute `LUI` address, since RV64 sign-extends bit 31.
    pub const RAM: Self = Self::new(0x4000_0000..0x8000_0000, 8);

    /// A byte range partitioned into equal words, both sizes powers of two.
    const fn new(range: Range<u64>, word_bytes: u64) -> Self {
        // A region holds at least one whole word.
        assert!(range.start < range.end);
        let bytes = range.end - range.start;
        assert!(bytes.is_power_of_two());
        assert!(word_bytes.is_power_of_two());
        assert!(word_bytes <= bytes);

        // Aligning the base to the region's size makes addition and XOR addressing agree.
        assert!(range.start.is_multiple_of(bytes));

        // Dividing two powers of two subtracts their logarithms.
        let log_word_bytes = word_bytes.trailing_zeros();
        Self {
            base: range.start,
            log_word_bytes,
            max_log_words: (bytes.trailing_zeros() - log_word_bytes) as usize,
        }
    }

    /// The byte address of word zero.
    pub const fn base(self) -> u64 {
        self.base
    }

    /// The bytes per word.
    pub const fn word_bytes(self) -> u64 {
        1 << self.log_word_bytes
    }

    /// The base-two logarithm of the most words the region holds.
    pub const fn max_log_words(self) -> usize {
        self.max_log_words
    }

    /// The byte address of word `index`.
    pub const fn address(self, index: usize) -> u64 {
        self.base + ((index as u64) << self.log_word_bytes)
    }

    /// The address one past the last byte of a region of `2^log_words` words.
    pub const fn end(self, log_words: usize) -> u64 {
        self.address(1 << log_words)
    }

    /// The index of the word holding `address`, in a region of `2^log_words` words.
    ///
    /// Returns `None` for an address outside the region.
    pub fn index(self, address: u64, log_words: usize) -> Option<usize> {
        // Below the base, the subtraction fails and the address is outside.
        let offset = address.checked_sub(self.base)?;

        // The word holding a byte rounds its offset down to a whole word.
        let index = offset >> self.log_word_bytes;
        (index < 1 << log_words).then_some(index as usize)
    }

    /// Whether the byte range lies in the largest region.
    pub const fn contains(self, range: Range<u64>) -> bool {
        range.start >= self.base && range.end <= self.end(self.max_log_words)
    }

    /// The size, as a base-two logarithm of words, of the region ending at `end`.
    ///
    /// Returns `None` unless the region holds a power of two of whole words, at most the largest size.
    pub fn log_words_ending_at(self, end: u64) -> Option<usize> {
        // An end at or below the base leaves no word.
        let bytes = end.checked_sub(self.base).filter(|&bytes| bytes != 0)?;

        // A power of two of bytes, at least one word, is a power of two of words.
        let log_bytes = bytes.is_power_of_two().then(|| bytes.trailing_zeros())?;
        let log_words = log_bytes.checked_sub(self.log_word_bytes)? as usize;
        (log_words <= self.max_log_words).then_some(log_words)
    }
}

// The regions are adjacent and do not overlap.
const _: () = {
    assert!(Region::TEXT.end(Region::TEXT.max_log_words()) == Region::ADVICE.base());
    assert!(Region::ADVICE.end(Region::ADVICE.max_log_words()) == Region::RAM.base());
};

#[cfg(test)]
mod tests {
    use std::panic::catch_unwind;

    use super::*;
    use proptest::prelude::*;

    const REGIONS: [Region; 3] = [Region::TEXT, Region::ADVICE, Region::RAM];

    #[test]
    fn malformed_regions_are_refused() {
        // Empty or reversed ranges, partial sizes, invalid words, and a misaligned base.
        for (start, end, word_bytes) in [
            (8, 8, 8),
            (16, 8, 8),
            (0, 24, 8),
            (0, 16, 0),
            (0, 16, 3),
            (0, 8, 16),
            (8, 24, 8),
        ] {
            assert!(catch_unwind(|| Region::new(start..end, word_bytes)).is_err());
        }
    }

    proptest! {
        #[test]
        fn index_inverts_address(region in proptest::sample::select(&REGIONS[..]), log_words in 0usize..=26, raw in any::<usize>()) {
            // Any word of a region of 2^log_words words.
            let index = raw % (1 << log_words);

            // Every byte of that word maps back to it.
            let address = region.address(index);
            for byte in 0..region.word_bytes() {
                prop_assert_eq!(region.index(address + byte, log_words), Some(index));
            }
        }

        #[test]
        fn index_rejects_addresses_outside(region in proptest::sample::select(&REGIONS[..]), log_words in 0usize..=26, address in any::<u64>()) {
            // An address is inside exactly when it lies in base..end.
            let inside = (region.base()..region.end(log_words)).contains(&address);
            prop_assert_eq!(region.index(address, log_words).is_some(), inside);
        }

        #[test]
        fn log_words_ending_at_inverts_end(region in proptest::sample::select(&REGIONS[..]), log_words in 0usize..=27) {
            // Sizes up to the largest round-trip; one past it is refused.
            let expected = (log_words <= region.max_log_words()).then_some(log_words);
            prop_assert_eq!(region.log_words_ending_at(region.end(log_words)), expected);
        }
    }

    #[test]
    fn log_words_ending_at_refuses_partial_regions() {
        // Fixture: RAM, whose words are 8 bytes.
        let ram = Region::RAM;

        // No word, part of a word, three words, an end below the base.
        for end in [ram.base(), ram.base() + 4, ram.base() + 24, ram.base() - 8] {
            assert_eq!(ram.log_words_ending_at(end), None, "{end:#x}");
        }
    }
}
