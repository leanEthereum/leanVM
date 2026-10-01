//! The address space: three disjoint regions of words.

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
    pub const TEXT: Self = Self::new(0x1000_0000, 2, 26);

    /// A second read-write memory, filled by the prover before the run.
    ///
    /// The statement does not fix its contents.
    ///
    /// A guest must check whatever it reads from it.
    pub const ADVICE: Self = Self::new(0x2000_0000, 3, 26);

    /// The read-write memory whose initial image the program fixes.
    ///
    /// It lies in the text's 2 GiB window, as the medany code model needs.
    ///
    /// A full RAM ends at `0x8000_0000`.
    ///
    /// Its last 2 KiB are out of reach of an absolute `LUI` address, since RV64 sign-extends bit 31.
    pub const RAM: Self = Self::new(0x4000_0000, 3, 27);

    /// A region at `base` of at most `2^max_log_words` words of `2^log_word_bytes` bytes.
    const fn new(base: u64, log_word_bytes: u32, max_log_words: usize) -> Self {
        // The XOR addressing above needs a base aligned to the largest region.
        assert!(base.is_multiple_of(1 << (log_word_bytes as usize + max_log_words)));
        Self {
            base,
            log_word_bytes,
            max_log_words,
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

    /// Whether the bytes `start..end` lie in the largest region.
    pub const fn contains(self, start: u64, end: u64) -> bool {
        start >= self.base && end <= self.end(self.max_log_words)
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

// Invariant: the regions tile the address space without overlap.
//
//     text   ends where the advice starts
//     advice ends where RAM starts
const _: () = assert!(Region::TEXT.end(Region::TEXT.max_log_words) == Region::ADVICE.base);
const _: () = assert!(Region::ADVICE.end(Region::ADVICE.max_log_words) == Region::RAM.base);

/// The byte address of the first instruction.
pub const TEXT_BASE: u64 = Region::TEXT.base;

/// The base-two logarithm of the most instructions a program holds.
pub const MAX_LOG_TEXT: usize = Region::TEXT.max_log_words;

/// The byte address of the first RAM word.
pub const RAM_BASE: u64 = Region::RAM.base;

/// The base-two logarithm of the most words RAM holds.
pub const MAX_LOG_RAM: usize = Region::RAM.max_log_words;

/// The byte address of the first advice word.
pub const ADVICE_BASE: u64 = Region::ADVICE.base;

/// The base-two logarithm of the most words the advice holds.
pub const MAX_LOG_ADVICE: usize = Region::ADVICE.max_log_words;

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    const REGIONS: [Region; 3] = [Region::TEXT, Region::ADVICE, Region::RAM];

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
        for end in [RAM_BASE, RAM_BASE + 4, RAM_BASE + 24, RAM_BASE - 8] {
            assert_eq!(ram.log_words_ending_at(end), None, "{end:#x}");
        }
    }
}
