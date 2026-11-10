//! A malicious prover, for the fuzzer: an edit to the scalars it sends.
//!
//! The edit is armed on the calling thread and taken by the next [`ProverState`](crate::transcript::ProverState)
//! it creates. Every scalar that prover sends, nonces included, passes through it with its stream index, and
//! what it returns is what is bound and sent. The prover then carries on honestly from the challenges the
//! forged message gives, so the proof is Fiat-Shamir consistent with the forgery: only the checks the
//! forged message feeds can reject it.

use primitives::field::F192;
use std::cell::RefCell;

/// Called with each scalar's stream index and honest value; returns the value sent.
pub type ScalarTamper = Box<dyn FnMut(usize, F192) -> F192>;

thread_local! {
    static ARMED: RefCell<Option<ScalarTamper>> = const { RefCell::new(None) };
}

/// The next prover created on this thread sends what `tamper` makes of its scalars.
pub fn arm(tamper: ScalarTamper) {
    ARMED.with(|armed| *armed.borrow_mut() = Some(tamper));
}

/// Drop an edit no prover took.
pub fn disarm() {
    ARMED.with(|armed| armed.borrow_mut().take());
}

pub(crate) fn take() -> Option<ScalarTamper> {
    ARMED.with(|armed| armed.borrow_mut().take())
}
