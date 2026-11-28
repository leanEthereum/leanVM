//! The decoded proof's area (`NativeVm/Input.lean`'s `Decoded`): the stream's count at word `0`,
//! element `i` at words `1 + 2i`, `2 + 2i`; from `streamEnd L` the phase count, then phase `k` at
//! `phaseBase L k`: its query count, height and leaf width, then opening `j` at
//! `3 + j · openingWords` past it (the leaf index, `wireMaxLeafWords` leaf words, `wireMaxHeight`
//! digests).

use crate::field::EW;

/// `wireMaxPhases`.
pub const MAX_PHASES: usize = 8;
/// `wireMaxQueries`.
pub const MAX_QUERIES: usize = 256;
/// `wireMaxLeafWords`.
pub const MAX_LEAF_WORDS: usize = 64;
/// `wireMaxHeight`.
pub const MAX_HEIGHT: usize = 32;
/// `openingWords`.
pub const OPENING_WORDS: usize = 1 + MAX_LEAF_WORDS + 4 * MAX_HEIGHT;
/// `phaseWords`.
pub const PHASE_WORDS: usize = 3 + MAX_QUERIES * OPENING_WORDS;

/// `maxStream L`.
#[inline(always)]
pub const fn max_stream(l: usize) -> usize {
    l / 16
}

/// `streamEnd L`.
#[inline(always)]
pub const fn stream_end(l: usize) -> usize {
    1 + 2 * max_stream(l)
}

/// `phaseBase L k`.
#[inline(always)]
pub const fn phase_base(l: usize, k: usize) -> usize {
    stream_end(l) + 1 + k * PHASE_WORDS
}

/// `decodedWords L`.
#[inline(always)]
pub const fn decoded_words(l: usize) -> usize {
    phase_base(l, MAX_PHASES)
}

/// The decoded proof of a wire of `l` bytes, read only.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Decoded<'a> {
    pub words: &'a [u64],
    pub l: usize,
}

impl<'a> Decoded<'a> {
    /// The stream's element `i`, if `i` is below its count.
    #[inline(never)]
    pub fn stream_element(&self, i: usize) -> Option<EW> {
        let n = usize::try_from(*self.words.first()?).ok()?;
        if i >= n {
            return None;
        }
        match self.words.get(1 + 2 * i..3 + 2 * i)? {
            &[c0, c1] => Some(EW::new(c0, c1)),
            _ => None,
        }
    }

    /// The stream's count.
    #[inline(always)]
    pub fn stream_len(&self) -> u64 {
        self.words.first().copied().unwrap_or(0)
    }

    /// The phase count.
    #[inline(never)]
    pub fn phase_count(&self) -> u64 {
        self.words.get(stream_end(self.l)).copied().unwrap_or(0)
    }

    /// Phase `k`'s words, if `k` is below the phase count.
    #[inline(never)]
    pub fn phase(&self, k: usize) -> Option<&'a [u64]> {
        if (k as u64) >= self.phase_count() || k >= MAX_PHASES {
            return None;
        }
        let base = phase_base(self.l, k);
        self.words.get(base..base + PHASE_WORDS)
    }
}
