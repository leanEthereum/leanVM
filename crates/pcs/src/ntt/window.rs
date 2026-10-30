//! The buffer under transform: the DRAM intermediate of an encode, or half of it.

use primitives::field::F64;

/// Buffers of at least this many words get streaming stores for data a pass does not read back.
///
/// # Why this value
///
/// - 2^23 words is 64 MiB, more than L3 keeps until the next pass.
/// - A streaming store then skips the read an ordinary store makes before it writes.
/// - A smaller buffer stays in L3 for the next pass, which a streaming store would give up.
pub(super) const STREAM_MIN_WORDS: usize = 1 << 23;

/// The words an encode transforms, and which part of the codeword they are.
///
/// - The buffer is whole blocks of `num_ntts`-word rows: all the cosets, or the cosets from row `first_row` on.
/// - It owns `first_row`, which shifts every row and block index to its place in the whole domain.
/// - It owns `stream`: a buffer this large is evicted before the next pass reads it back.
/// - Tasks write disjoint pieces through [`Window::base`], so they never hold the `&mut`.
pub(super) struct Window<'a> {
    words: &'a mut [F64],
    num_ntts: usize,
    first_row: usize,
    stream: bool,
}

impl<'a> Window<'a> {
    pub(super) fn new(words: &'a mut [F64], num_ntts: usize, first_row: usize) -> Self {
        assert!(num_ntts > 0);
        assert_eq!(words.len() % num_ntts, 0);
        let stream = words.len() >= STREAM_MIN_WORDS;
        Self {
            words,
            num_ntts,
            first_row,
            stream,
        }
    }

    pub(super) fn num_ntts(&self) -> usize {
        self.num_ntts
    }

    /// The buffer's first row, in the whole domain.
    pub(super) fn first_row(&self) -> usize {
        self.first_row
    }

    /// Whether this buffer's write-backs stream.
    pub(super) fn stream(&self) -> bool {
        self.stream
    }

    /// Whether write-backs stream whole aligned cache lines: this buffer streams and its rows are whole aligned lines.
    pub(super) fn streams_lines(&self) -> bool {
        self.stream && self.num_ntts.is_multiple_of(8) && self.words.as_ptr().align_offset(64) == 0
    }

    pub(super) fn len(&self) -> usize {
        self.words.len()
    }

    pub(super) fn words_mut(&mut self) -> &mut [F64] {
        self.words
    }

    /// The first word, for tasks that write disjoint pieces of the buffer.
    pub(super) fn base(&mut self) -> parallel::SendPtr<F64> {
        parallel::SendPtr(self.words.as_mut_ptr())
    }

    /// The first word of row `r` of layer block `block`, in a buffer of blocks of `block_rows` rows.
    #[inline(always)]
    pub(super) fn row(&self, block_rows: usize, block: usize, r: usize) -> usize {
        (block * block_rows + r - self.first_row) * self.num_ntts
    }
}
