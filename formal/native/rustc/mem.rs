//! `memcpy` and `memset`, which LLVM lowers large copies and fills to (an array's initializer, a struct's move),
//! defined here so that the assembly holds every instruction a verification runs. The crate is `no_builtins`, so these
//! loops are not turned back into calls of themselves. A word at a time when the operands allow it. The empty `asm!`
//! in each loop keeps LLVM from unrolling it: one load and one store per iteration, the shape the proofs follow.

use core::arch::asm;
use core::ffi::c_void;

/// # Safety
/// `dest` and `src` hold `n` bytes each, apart.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn memcpy(dest: *mut c_void, src: *const c_void, n: usize) -> *mut c_void {
    let (d, s) = (dest as *mut u8, src as *const u8);
    let mut i = 0;
    if (d as usize | s as usize | n) % 8 == 0 {
        while i < n {
            // SAFETY: the caller's contract, the word inside both areas and aligned.
            unsafe { *(d.add(i) as *mut u64) = *(s.add(i) as *const u64) };
            i += 8;
            // SAFETY: an empty instruction sequence.
            unsafe { asm!("", options(nomem, nostack, preserves_flags)) };
        }
    } else {
        while i < n {
            // SAFETY: the caller's contract.
            unsafe { *d.add(i) = *s.add(i) };
            i += 1;
            // SAFETY: an empty instruction sequence.
            unsafe { asm!("", options(nomem, nostack, preserves_flags)) };
        }
    }
    dest
}

/// # Safety
/// `dest` holds `n` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn memset(dest: *mut c_void, c: i32, n: usize) -> *mut c_void {
    let (d, byte) = (dest as *mut u8, c as u8);
    let mut i = 0;
    if (d as usize | n) % 8 == 0 {
        let word = u64::from(byte) * 0x0101_0101_0101_0101;
        while i < n {
            // SAFETY: the caller's contract, the word inside the area and aligned.
            unsafe { *(d.add(i) as *mut u64) = word };
            i += 8;
            // SAFETY: an empty instruction sequence.
            unsafe { asm!("", options(nomem, nostack, preserves_flags)) };
        }
    } else {
        while i < n {
            // SAFETY: the caller's contract.
            unsafe { *d.add(i) = byte };
            i += 1;
            // SAFETY: an empty instruction sequence.
            unsafe { asm!("", options(nomem, nostack, preserves_flags)) };
        }
    }
    dest
}
