//! Write-back of a finished row group from its scratch to the buffer.

use primitives::field::F64;
use primitives::stream::Stream;

use super::scratch::Line;

/// Where a finished row group lands in the buffer.
///
/// - `dst` is the group's first row in the buffer, `dst_stride` words before its next.
/// - A scratch row is `row_len` words and lands in pieces of `piece` words, `piece_stride` words apart.
/// - A streaming drain moves whole aligned cache lines: `piece` is 8, and the caller checks the alignment.
pub(super) struct Drain {
    pub(super) dst: *mut F64,
    pub(super) row_len: usize,
    pub(super) dst_stride: usize,
    pub(super) piece: usize,
    pub(super) piece_stride: usize,
    pub(super) rows: usize,
}

impl Drain {
    /// Move the group out of its contiguous scratch `src`: streamed, or stored normally without a stream.
    #[inline(always)]
    pub(super) fn run(&self, src: &[F64], stream: Option<&Stream>) {
        debug_assert_eq!(src.len(), self.rows * self.row_len);
        for (row, src) in src.chunks_exact(self.row_len).enumerate() {
            for (k, src) in src.chunks_exact(self.piece).enumerate() {
                // SAFETY:
                // - The group lies inside the buffer, so every piece is in bounds, and line-aligned when streamed.
                // - Only this group's owner writes these rows of the buffer.
                unsafe {
                    let dst = self.dst.add(row * self.dst_stride + k * self.piece_stride);
                    match stream {
                        Some(s) => s.copy_lines(dst.cast::<Line>(), &primitives::cast_slice::<F64, Line>(src)[0]),
                        None => dst.copy_from_nonoverlapping(src.as_ptr(), self.piece),
                    }
                }
            }
        }
    }
}
