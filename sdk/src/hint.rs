//! Hints: values a guest has computed outside the proof, then checks.
//!
//! A hint is advice the guest asks for while it runs. On the VM, `hint(f)` makes the executor run `f` first, in the
//! run's own state but unproven, then rewind everything `f` did; what `f` returned becomes advice words, which the
//! proven code reads like any other. The proof sees none of `f`, only those words, which the prover chose, so the guest
//! checks them: a hinted inverse is multiplied back, a hinted root squared. Off the VM `f` simply runs, so a library
//! using hints runs natively as its own reference, and computes the hints the VM would.

#[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
use crate::Words;
use core::ops::Deref;

/// A hinted value: in place in the advice on the VM, owned off it.
#[cfg(all(target_arch = "riscv64", target_os = "none"))]
pub struct Hint<T: 'static>(&'static T);

/// A hinted value: in place in the advice on the VM, owned off it.
#[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
pub struct Hint<T>(T);

impl<T> Deref for Hint<T> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &T {
        #[cfg(all(target_arch = "riscv64", target_os = "none"))]
        return self.0;
        #[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
        return &self.0;
    }
}

/// The value `f` computes, as a hint the guest must check.
///
/// ```ignore
/// let inv = *leanvm_guest::hint(|| fp::inverse(&x));
/// assert_eq!(fp::mul(&x, &inv), fp::ONE);
/// ```
///
/// On the VM `f` runs unproven before the proven code goes on: the proof holds two instructions and the reads of the
/// value, never `f`'s. Its value takes words at the end of the advice region, below earlier hints and above what
/// `read` has taken, so a guest sizes the region for both (`advice_words!`). A hint may call `hint` itself.
#[cfg(all(target_arch = "riscv64", target_os = "none"))]
#[inline(always)]
pub fn hint<T: crate::Words>(f: impl FnOnce() -> T) -> Hint<T> {
    let to = crate::io::vm::reserve::<T>();
    if crate::precompile::hint_enter() {
        let value = f();
        // SAFETY: `value` is `T`'s words (`Words`), on this frame.
        unsafe { crate::precompile::hint_exit(to.cast(), (&raw const value).cast(), size_of::<T>() / 8) }
    }
    // SAFETY: the executor wrote the value's words there before the proven code reached them, and the proof has
    // them there from the start; any words are a `T` (`Words`).
    Hint(unsafe { &*to })
}

/// The value `f` computes, as a hint the guest must check: off the VM, `f` runs.
#[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
#[inline(always)]
pub fn hint<T: Words>(f: impl FnOnce() -> T) -> Hint<T> {
    Hint(f())
}
