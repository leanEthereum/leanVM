//! Streaming stores for x86 buffers written once and read in a later pass. Other targets use ordinary copies.

#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;
use std::marker::PhantomData;
use std::mem::MaybeUninit;

/// A region of streaming stores.
///
/// Streaming stores are weakly ordered, so nothing else may observe them until
/// an `sfence`. Dropping the region emits it, once for the whole region rather
/// than once per copy, which is what makes the small copies of a fold kernel
/// worth streaming at all. The type is neither `Send` nor `Sync`: a region
/// belongs to the thread that opened it, so a parallel kernel opens one per
/// task and its fence lands before the task returns.
pub struct Stream(PhantomData<*const ()>);

impl Default for Stream {
    fn default() -> Self {
        Self::new()
    }
}

impl Stream {
    pub const fn new() -> Self {
        Self(PhantomData)
    }

    /// Copy `src` over `dst` without fetching `dst` first. Whole cache lines
    /// stream; a ragged head or tail is stored normally.
    #[inline]
    pub fn copy<T: Copy>(&self, dst: &mut [T], src: &[T]) {
        assert_eq!(dst.len(), src.len(), "a streaming copy is elementwise");
        // SAFETY: distinct slices are valid for `size_of_val(src)` bytes each
        // and cannot overlap.
        unsafe { copy_raw(dst.as_mut_ptr().cast(), src.as_ptr().cast(), size_of_val(src)) }
    }

    /// Copy `src` into unwritten slots, streaming whole cache lines as a copy does.
    #[inline]
    pub fn write<T: Copy>(&self, dst: &mut [MaybeUninit<T>], src: &[T]) {
        assert_eq!(dst.len(), src.len(), "a streaming copy is elementwise");
        // SAFETY: distinct slices are valid for `size_of_val(src)` bytes each and cannot overlap.
        unsafe { copy_raw(dst.as_mut_ptr().cast(), src.as_ptr().cast(), size_of_val(src)) }
    }
}

/// # Safety
/// `dst` and `src` must be valid for `bytes` and must not overlap.
#[cfg_attr(
    not(target_arch = "x86_64"),
    expect(
        clippy::missing_const_for_fn,
        reason = "The x86 implementation requires runtime streaming stores."
    )
)]
#[inline]
unsafe fn copy_raw(dst: *mut u8, src: *const u8, bytes: usize) {
    #[cfg(target_arch = "x86_64")]
    {
        const LINE: usize = 64;
        let head = dst.align_offset(LINE).min(bytes);
        let body = (bytes - head) & !(LINE - 1);
        // SAFETY: the three runs partition `bytes`, which both pointers cover,
        // and `dst + head` is line-aligned by construction.
        unsafe {
            std::ptr::copy_nonoverlapping(src, dst, head);
            stream_lines(dst.add(head), src.add(head), body);
            std::ptr::copy_nonoverlapping(src.add(head + body), dst.add(head + body), bytes - head - body);
        }
    }
    #[cfg(not(target_arch = "x86_64"))]
    // SAFETY: forwarded to the caller's obligation.
    unsafe {
        std::ptr::copy_nonoverlapping(src, dst, bytes);
    };
}

impl Drop for Stream {
    #[inline]
    fn drop(&mut self) {
        #[cfg(target_arch = "x86_64")]
        // SAFETY: `sfence` is unconditionally available on x86-64.
        unsafe {
            core::arch::x86_64::_mm_sfence();
        };
    }
}

/// Stream `bytes` (a multiple of 64) from `src` to the line-aligned `dst`.
///
/// # Safety
/// Both pointers must be valid for `bytes`, `dst` 64-byte aligned, and the
/// ranges must not overlap.
#[cfg(target_arch = "x86_64")]
#[inline]
unsafe fn stream_lines(dst: *mut u8, src: *const u8, bytes: usize) {
    // SAFETY: every access covers `off..off + 64` with `off + 64 <= bytes`, since `bytes` is a multiple of 64, so
    // it stays inside both ranges the caller vouches for; each store's target is 64-byte aligned because `dst` is;
    // each arm runs only under the target feature its `cfg` names.
    unsafe {
        let mut off = 0;
        while off < bytes {
            #[cfg(target_feature = "avx512f")]
            _mm512_stream_si512(dst.add(off).cast(), _mm512_loadu_si512(src.add(off).cast()));
            #[cfg(all(not(target_feature = "avx512f"), target_feature = "avx"))]
            {
                _mm256_stream_si256(dst.add(off).cast(), _mm256_loadu_si256(src.add(off).cast()));
                _mm256_stream_si256(dst.add(off + 32).cast(), _mm256_loadu_si256(src.add(off + 32).cast()));
            }
            #[cfg(not(any(target_feature = "avx512f", target_feature = "avx")))]
            for q in 0..4 {
                let o = off + 16 * q;
                _mm_stream_si128(dst.add(o).cast(), _mm_loadu_si128(src.add(o).cast()));
            }
            off += 64;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn streamed_copy_matches_a_plain_one() {
        let src: Vec<u32> = (0..600u32).collect();
        for head in 0..20 {
            for len in [0, 1, 15, 16, 17, 64, 129, 500] {
                let mut got = vec![0u32; head + len];
                let mut want = got.clone();
                {
                    let stream = Stream::new();
                    stream.copy(&mut got[head..], &src[..len]);
                }
                want[head..].copy_from_slice(&src[..len]);
                assert_eq!(got, want, "head {head}, len {len}");
            }
        }
    }
}
