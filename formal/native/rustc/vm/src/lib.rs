//! leanVM's verifier, wire bytes to verdict, for rustc to compile to x86-64 and AArch64 assembly:
//! `no_std`, no allocation, no dependency. `leanvm_verify(ctx)` takes the context of
//! `formal/native/NativeVm/Entry.lean` (`EntryPre`) and returns `1`
//! exactly when the bytes decode (`NativeVm.Wire.decodeM`) to a proof the model accepts
//! (`NativeVm.Model.verify`), else `0`.
//!
//! Each module mirrors a module of the model (`NativeVm/Model/*.lean`, `NativeVm/Wire/Model.lean`),
//! function for function, with its names, order and constants; an `Array` of the model is a
//! fixed-capacity buffer in the caller's areas or on the stack, and a step past a capacity rejects.
//! The model's `none` is `None`.
//!
//! The assembly is proved function by function (`formal/native/NativeRustcVm{Arm,X64}`), so every
//! function says whether it stays one: `#[inline(never)]` on each but the few-instruction helpers,
//! which are `#[inline(always)]` (in particular `kmul` and `EW::mul` are one copy each of the
//! carry-less arithmetic). Every struct is `#[repr(C)]`, so that its fields' offsets are its
//! declaration's.

#![no_std]
#![no_builtins]

mod buf;
mod bus;
mod data;
mod field;
mod gkr;
mod input;
mod keccak;
mod keccak_gkr;
mod layout;
#[cfg(target_os = "none")]
mod mem;
mod ring_switch;
mod stack;
mod tables;
mod transcript;
mod verify;
mod whir;
mod wire;

use input::{Decoded, decoded_words};
use verify::{Work, verify};
use wire::{DecodeWork, decode};

/// The working area's words: `Work`'s or the decoder's, which use it in turn.
pub const WORK_WORDS: usize = {
    let (a, b) = (size_of::<Work>(), size_of::<DecodeWork>());
    (if a > b { a } else { b }).div_ceil(8)
};

/// The context's words the verifier reads.
const CTX_WORDS: usize = 12;

/// `leanvm_verify(ctx)`: `1` when the wire bytes decode to a proof that verifies, else `0`.
///
/// # Safety
///
/// `ctx` must be non-null, 8-byte aligned, and readable over its first 12 words (`NativeVm/Entry.lean`):
/// words `0`, `1` the wire bytes' address and count, `2`, `3` the bytecode's words' address and count,
/// `4 .. 7` the public input, `8`, `9` the decoded area's address and word count, `10`, `11` the working
/// area's. The wire count is in bytes; the other area counts are in `u64` words. Every area must be
/// readable over its count, with no address-space wrapping. The decoded and working areas
/// must also be writable and initialized over their counts (Rust references require initialized
/// integer memory). All nonempty areas must be apart from one another except the read-only wire and
/// bytecode. The context must also be apart from all nonempty areas. No wire padding is required.
/// The context and areas, including empty-area pointers, neither overlap nor point into the
/// verifier's own static data or GOT entries; regions from the caller's allocations or statics
/// always satisfy this.
/// The area counts and alignments (other than `ctx` itself) are checked here.
/// Like `Statement/LeanVmVerifier.lean`, this entry point does
/// not check `is_valid_encoding_of_a_leanisa_program`; callers on untrusted bytecode must validate it
/// externally to match `crates/verifier::Bytecode::new`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn leanvm_verify(ctx: *mut u64) -> u64 {
    // SAFETY: the caller's contract, the context's first words readable.
    let c: [u64; CTX_WORDS] = unsafe { core::ptr::read(ctx as *const [u64; CTX_WORDS]) };
    let [wire, l, bytecode, n, p0, p1, p2, p3, dec, dec_n, work, work_n] = c;
    let (l, n) = (l as usize, n as usize);
    let aligned = |a: u64| a != 0 && a % 8 == 0;
    let dec_words = decoded_words(l);
    // Reject sizes outside the verifier's supported bounds.
    if l as u64 >= 1 << 32
        || (n as u64) > ((1 << 32) - 10) / 8
        || (dec_n as usize) < dec_words
        || (work_n as usize) < WORK_WORDS
        || !aligned(dec)
        || !aligned(work)
        || (n > 0 && !aligned(bytecode))
        || (l > 0 && wire == 0)
    {
        return 0;
    }
    // SAFETY: the areas are the caller's, of the sizes checked above, aligned, and apart but for
    // the wire and the bytecode, which are only read.
    let (wire, bytecode, dec) = unsafe {
        (
            if l > 0 { core::slice::from_raw_parts(wire as *const u8, l) } else { &[][..] },
            if n > 0 { core::slice::from_raw_parts(bytecode as *const u64, n) } else { &[][..] },
            core::slice::from_raw_parts_mut(dec as *mut u64, dec_words),
        )
    };
    let public_input = [p0, p1, p2, p3];
    {
        // SAFETY: the working area holds `WORK_WORDS` aligned words, every bit pattern a value of
        // `DecodeWork`'s integer fields; the reference ends before `Work`'s begins.
        let w = unsafe { &mut *(work as *mut DecodeWork) };
        if decode(wire, dec, w).is_none() {
            return 0;
        }
    }
    // SAFETY: as above, for `Work`.
    let w = unsafe { &mut *(work as *mut Work) };
    u64::from(verify(bytecode, &public_input, Decoded { words: dec, l }, w))
}

#[cfg(target_os = "none")]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    // SAFETY: aborting does not access memory or return.
    unsafe {
        #[cfg(target_arch = "x86_64")]
        core::arch::asm!("ud2", options(noreturn, nomem, nostack));
        #[cfg(target_arch = "aarch64")]
        core::arch::asm!("udf #0", options(noreturn, nomem, nostack));
    }
}
