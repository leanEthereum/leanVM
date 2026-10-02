//! What a guest reads and what it proves: `read` takes values from the advice, in place,
//! and `commit` makes values public. There are no system calls: the advice is memory the
//! prover fills before the run, at the addresses `link.ld` fixes, and the run's output is
//! the BLAKE2s digest of everything committed, in order, which the verifier recomputes from
//! the public values.

use crate::Blake2s;

/// A type made of 64-bit words and nothing else, so that any words are one.
///
/// # Safety
///
/// The type is `repr(C)` (or an array), its size a multiple of 8 and its alignment 8, it
/// has no padding, and every bit pattern of its words is a valid value: integers and arrays
/// of them, never a `bool`, an enum, a reference or a pointer.
pub unsafe trait Words: Sized + 'static {}

// SAFETY: a word is a word.
unsafe impl Words for u64 {}
// SAFETY: an array of word types is its elements' words, back to back.
unsafe impl<T: Words, const N: usize> Words for [T; N] {}

/// A value of a type from another crate as its words, for a host laying out advice that
/// the guest reads with `read_unchecked`.
///
/// # Safety
///
/// `T` is words only, as [`Words`] says.
pub const unsafe fn as_words_unchecked<T>(value: &T) -> &[u64] {
    const { assert_words::<T>() };
    // SAFETY: `T` is its words with no padding (the caller's).
    unsafe { core::slice::from_raw_parts((value as *const T).cast(), size_of::<T>() / 8) }
}

/// That `T` is whole, aligned words, at compile time.
const fn assert_words<T>() {
    assert!(
        size_of::<T>().is_multiple_of(8) && align_of::<T>() == 8,
        "a type of whole words"
    );
}

/// The public values a run commits, and the output they make: their BLAKE2s digest.
///
/// On the VM, `commit` feeds the run's own; off it, this is how a host computes the output
/// a guest must give.
pub struct PublicValues(Blake2s);

impl Default for PublicValues {
    fn default() -> Self {
        Self::new()
    }
}

impl PublicValues {
    pub const fn new() -> Self {
        Self(Blake2s::new())
    }

    /// Commit a value.
    #[inline(always)]
    pub fn commit<T: Words>(&mut self, value: &T) -> &mut Self {
        // SAFETY: `T` is words only (`Words`).
        self.0.update_words(unsafe { as_words_unchecked(value) });
        self
    }

    /// The output: the digest of everything committed.
    pub fn digest(self) -> [u64; 4] {
        self.0.finalize_words()
    }
}

#[cfg(all(target_arch = "riscv64", target_os = "none"))]
pub use vm::{commit, read, read_slice, read_unchecked};

#[cfg(all(target_arch = "riscv64", target_os = "none"))]
pub(crate) mod vm {
    use super::{PublicValues, Words, assert_words};

    /// The output `_start` loads into `a0..a3` when the run ends.
    pub(crate) static mut OUTPUT: [u64; 4] = [0; 4];
    /// What the run has committed so far.
    static mut PUBLIC: PublicValues = PublicValues::new();
    /// The advice words read so far.
    static mut READ: usize = 0;

    unsafe extern "C" {
        /// The advice region's bounds (`link.ld`).
        static __advice: u64;
        static __advice_top: u64;
    }

    /// The advice: words the prover supplies, which the statement says nothing about.
    fn advice() -> &'static [u64] {
        // The two symbols bound the region without belonging to one object, so the length
        // is address arithmetic rather than `offset_from`, which asks for one allocation.
        let (start, end) = (&raw const __advice, &raw const __advice_top);
        let words = (end as usize - start as usize) / size_of::<u64>();
        // SAFETY: the linker script reserves the region, it holds whole words, and nothing
        // in this crate writes it.
        unsafe { core::slice::from_raw_parts(start, words) }
    }

    /// The next value of the advice, in place: nothing is copied or decoded.
    ///
    /// The prover chose it, so the guest has to check it. Reading past the advice panics,
    /// so the run has no proof.
    #[inline(always)]
    pub fn read<T: Words>() -> &'static T {
        &read_slice::<T>(1)[0]
    }

    /// The next `n` values of the advice, in place.
    #[inline(always)]
    pub fn read_slice<T: Words>(n: usize) -> &'static [T] {
        // SAFETY: any words are a `T` (`Words`).
        unsafe { take(n) }
    }

    /// The next value of the advice as a type from another crate, in place: how a guest's
    /// `main` reads its library's types, which need not know the VM.
    ///
    /// # Safety
    ///
    /// `T` is words only, as [`Words`] says.
    #[inline(always)]
    pub unsafe fn read_unchecked<T>() -> &'static T {
        // SAFETY: the caller's.
        unsafe { &take::<T>(1)[0] }
    }

    /// # Safety
    ///
    /// `T` is words only, as [`Words`] says.
    #[inline(always)]
    unsafe fn take<T>(n: usize) -> &'static [T] {
        const { assert_words::<T>() };
        let words = n.checked_mul(size_of::<T>() / 8).expect("the values fit the advice");
        // SAFETY: one hart, no interrupts: nothing else touches `READ`.
        let start = unsafe { READ };
        let end = start.checked_add(words).expect("the values fit the advice");
        let taken = advice().get(start..end).expect("the values fit the advice");
        // SAFETY: as above.
        unsafe { READ = end };
        // SAFETY: the words are aligned to 8, as `T` is, and any words are a `T` (the caller's).
        unsafe { core::slice::from_raw_parts(taken.as_ptr().cast(), n) }
    }

    /// Make a value public: the run's output is the digest of everything committed, in order.
    #[inline(always)]
    pub fn commit<T: Words>(value: &T) {
        // SAFETY: one hart, no interrupts: nothing else touches `PUBLIC`.
        unsafe { &mut *(&raw mut PUBLIC) }.commit(value);
    }

    /// Called by `_start` once `main` returns: the output is the digest of what was committed.
    pub(crate) extern "C" fn finish() {
        // SAFETY: the run is over, so `PUBLIC` is read once and nothing touches it after.
        let public = unsafe { core::ptr::read(&raw const PUBLIC) };
        // SAFETY: as above, for `OUTPUT`.
        unsafe { core::ptr::write_volatile(&raw mut OUTPUT, public.digest()) }
    }
}

// TODO: remove this macro by making the advice region's size per proof rather than per program:
// the prover announces a power of two, bound into the transcript before any challenge and range
// checked by both verifiers (at most `MAX_LOG_ADVICE`, inside the advice window). That is sound,
// the advice being the prover's anyway: a region too small traps the read past its end, one too
// large only costs the prover. `read` would then drop its bounds check against `__advice_top` and
// rely on that trap.
/// Size the guest's advice region, in words: a power of two.
///
/// A guest that names none gets 8192 words.
///
/// The prover commits to the whole region, so a guest sizes it to what it reads.
///
/// ```ignore
/// leanvm_guest::advice_words!(1 << 16);
/// ```
#[macro_export]
macro_rules! advice_words {
    ($words:expr) => {
        // The loader takes a region's size to be a power of two.
        const _: () = assert!(($words as u64).is_power_of_two(), "the advice region is a power of two");
        // An absolute symbol: the linker script places the region's end at the base plus its value.
        core::arch::global_asm!(
            ".globl __advice_bytes",
            ".set __advice_bytes, {bytes}",
            bytes = const 8 * ($words as u64),
        );
    };
}

/// Size the guest's stack, in words: an even number, so the stack top stays 16-byte aligned.
///
/// A guest that names none gets 8192 words.
///
/// The stack opens RAM, and RAM is the smallest power of two holding it and the data.
/// The prover commits to all of RAM, so a guest sizes its stack to what it uses.
/// A stack too small runs below RAM's base, and the run traps.
///
/// ```ignore
/// leanvm_guest::stack_words!(1 << 9);
/// ```
#[macro_export]
macro_rules! stack_words {
    ($words:expr) => {
        // RISC-V's calling convention keeps the stack pointer 16-byte aligned.
        const _: () = assert!(($words as u64).is_multiple_of(2), "the stack is a whole number of 16-byte units");
        // An absolute symbol: the linker script sizes the stack to its value.
        core::arch::global_asm!(
            ".globl __stack_bytes",
            ".set __stack_bytes, {bytes}",
            bytes = const 8 * ($words as u64),
        );
    };
}
