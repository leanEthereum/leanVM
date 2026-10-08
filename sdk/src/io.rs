//! What a guest reads and what it proves: `read` takes values from the advice, in place,
//! and `commit` makes values public. There are no system calls: the advice is memory the
//! prover fills, at the addresses `link.ld` fixes, before the run or, for a hint, as the
//! guest asks; and the run's output is the BLAKE2s digest of everything committed, in order,
//! which the verifier recomputes from the public values.

use crate::Blake2s;
#[cfg(any(test, all(target_arch = "riscv64", target_os = "none")))]
use crate::blake2s::{Block, IV};
#[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
use alloc::vec::Vec;
#[cfg(any(test, all(target_arch = "riscv64", target_os = "none")))]
use core::mem::MaybeUninit;

#[cfg(all(target_arch = "riscv64", target_os = "none"))]
pub use vm::{commit, read, read_slice, read_unchecked};

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

/// What one run of a guest is given, and what it must output.
///
/// A host builds it off the VM: the advice it lays out, and the digest of the public values it computes natively.
#[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Run {
    /// The words the guest reads.
    pub advice: Vec<u64>,
    /// The output the guest must give: the digest of what it commits.
    pub expected: [u64; 4],
}

/// The committed words' BLAKE2s, in progress, as `commit` keeps it: the block the instruction reads, where the next
/// committed word goes in its message, and the bytes compressed before the message.
///
/// A word is one store and a pointer bump, and a full block is compressed where it is, only once a word is known to
/// follow it: the last block is the one compressed as last. `next` points into the value itself, so a `Public` never
/// moves, and it is reached only through a raw pointer, which `next` derives from: a reference to it, or to its block,
/// held across a use of `next` would be invalidated by it, so a reference to the block lives only inside a compression.
#[cfg(any(test, all(target_arch = "riscv64", target_os = "none")))]
struct Public {
    block: Block,
    next: *mut u64,
    done: u64,
}

#[cfg(any(test, all(target_arch = "riscv64", target_os = "none")))]
impl Public {
    /// Nothing committed, the next word going to `next`, which must be the new value's first message word.
    const fn new(next: *mut u64) -> Self {
        Self {
            block: Block {
                h: IV,
                out: MaybeUninit::uninit(),
                m: [0; 8],
            },
            next,
            done: 0,
        }
    }

    /// Commit `words`.
    ///
    /// # Safety
    ///
    /// `this` points to a `Public` made by [`Self::new`] with its first message word, `next` derived from `this`,
    /// and nothing else reaches it.
    #[inline(always)]
    unsafe fn commit(this: *mut Self, words: &[u64]) {
        // SAFETY: the caller's; `next` is a word of the message, at most its end, and is written only below it.
        unsafe {
            let start = (&raw mut (*this).block.m).cast::<u64>();
            let end = start.add(8);
            let mut next = (*this).next;
            for &word in words {
                if next == end {
                    Self::absorb(this);
                    next = start;
                }
                next.write(word);
                next = next.add(1);
            }
            (*this).next = next;
        }
    }

    /// Compress the full message, which more words follow: the compression becomes the chaining value.
    ///
    /// # Safety
    ///
    /// As [`Self::commit`].
    #[inline(always)]
    unsafe fn absorb(this: *mut Self) {
        // SAFETY: the caller's; the reference to the block ends before `next` is used again.
        unsafe {
            (*this).done += 64;
            let done = (*this).done;
            let block = &mut (*this).block;
            block.h = block.compress(done, false);
        }
    }

    /// The digest: the last block zero-padded, the counter every byte committed.
    ///
    /// # Safety
    ///
    /// As [`Self::commit`].
    unsafe fn finish(this: *mut Self) -> [u64; 4] {
        // SAFETY: the caller's; `next` is in the message or at its end, and the reference to the block is the last
        // use of the value.
        unsafe {
            let filled = (*this)
                .next
                .offset_from_unsigned((&raw const (*this).block.m).cast::<u64>());
            let t = (*this).done + 8 * filled as u64;
            let block = &mut (*this).block;
            block.m[filled..].fill(0);
            block.compress(t, true)
        }
    }
}

#[cfg(all(target_arch = "riscv64", target_os = "none"))]
pub(crate) mod vm {
    use super::{Public, Words, as_words_unchecked, assert_words};

    /// The output `_start` loads into `a0..a3` when the run ends.
    pub(crate) static mut OUTPUT: [u64; 4] = [0; 4];
    /// What the run has committed so far, streamed through the instruction's own block.
    // SAFETY: only the address of the static's message is taken, nothing is read.
    static mut PUBLIC: Public = Public::new(unsafe { (&raw mut PUBLIC.block.m).cast() });
    /// The advice words read so far, from its start.
    static mut READ: usize = 0;
    /// The advice words hints have taken, from its end.
    static mut HINTED: usize = 0;

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
        // SAFETY: the linker script reserves the region and it holds whole words. Nothing in
        // this crate writes it, and the executor writes a hint's words before the proven code
        // reads them, where the proof has them from the start.
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
        // SAFETY: as above, for `HINTED`.
        let unhinted = advice().len() - unsafe { HINTED };
        let taken = (advice().get(start..end))
            .filter(|_| end <= unhinted)
            .expect("the values fit the advice");
        // SAFETY: as above.
        unsafe { READ = end };
        // SAFETY: the words are aligned to 8, as `T` is, and any words are a `T` (the caller's).
        unsafe { core::slice::from_raw_parts(taken.as_ptr().cast(), n) }
    }

    /// Where a hint of `T` goes: the words below the hints before it, which the executor
    /// writes when the guest asks for it.
    ///
    /// A hint meeting what `read` has taken panics, so the run has no proof.
    #[inline(always)]
    pub(crate) fn reserve<T: Words>() -> *const T {
        const { assert_words::<T>() };
        // SAFETY: one hart, no interrupts: nothing else touches `READ` or `HINTED`.
        let (read, hinted) = unsafe { (READ, HINTED) };
        let end = advice().len() - hinted;
        let start = (end.checked_sub(size_of::<T>() / 8))
            .filter(|&start| start >= read)
            .expect("the hints fit the advice");
        // SAFETY: as above.
        unsafe { HINTED = advice().len() - start };
        // SAFETY: `start` is a word of the region.
        unsafe { advice().as_ptr().add(start).cast() }
    }

    /// Make a value public: the run's output is the digest of everything committed, in order.
    #[inline(always)]
    pub fn commit<T: Words>(value: &T) {
        // SAFETY: one hart, no interrupts: nothing else touches `PUBLIC`, which is reached only by its address;
        // `T` is words only (`Words`).
        unsafe { Public::commit(&raw mut PUBLIC, as_words_unchecked(value)) }
    }

    /// Called by `_start` once `main` returns: the output is the digest of what was committed.
    pub(crate) extern "C" fn finish() {
        // SAFETY: as in `commit`; the run is over, so nothing touches `PUBLIC` after.
        let digest = unsafe { Public::finish(&raw mut PUBLIC) };
        // SAFETY: as above, for `OUTPUT`.
        unsafe { core::ptr::write_volatile(&raw mut OUTPUT, digest) }
    }
}

// TODO: remove this macro by making the advice region's size per proof rather than per program:
// the prover announces a power of two, bound into the transcript before any challenge and range
// checked by both verifiers (at most 2^26 words, inside the advice window). That is sound,
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

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_util::Rng;

    /// The digest `commit` gives for `words` committed `n` at a time: a `Public` as the VM's, made in place.
    fn committed(words: &[u64], n: usize) -> [u64; 4] {
        let mut public = MaybeUninit::<Public>::uninit();
        let this = public.as_mut_ptr();
        // SAFETY: the value is made with its own first message word, `next` derived from `this`, and is reached only
        // through `this`.
        unsafe {
            this.write(Public::new((&raw mut (*this).block.m).cast()));
            for piece in words.chunks(n) {
                Public::commit(this, piece);
            }
            Public::finish(this)
        }
    }

    #[test]
    fn commit_outputs_what_public_values_computes() {
        // Invariant: the run's output, the digest `commit` streams through its block, is the digest `PublicValues`
        // gives a host for the same words, however they are split into commits.
        //
        // Fixture: nothing committed, then every count through five blocks, so the last word falls at every offset of
        // a block and on its end; a word at a time, in pieces straddling blocks, and all at once.
        let mut rng = Rng::new(0xC0);
        let words: [u64; 40] = core::array::from_fn(|_| rng.next_u64());
        for len in 0..=40 {
            let mut host = PublicValues::new();
            for word in &words[..len] {
                host.commit(word);
            }
            let expected = host.digest();
            for n in [1, 3, 8, 9, 40] {
                assert_eq!(committed(&words[..len], n), expected, "{len} words, {n} at a time");
            }
        }
    }
}
