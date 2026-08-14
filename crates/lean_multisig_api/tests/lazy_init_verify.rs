//! `verify` must initialize the aggregation bytecode itself.
//!
//! This file exists to get its own process. The bytecode lives in a `OnceLock`, so only the
//! *first* call in a process can observe whether an entry point initializes it; any test sharing
//! a process with another entry point — or with `warm_up` — finds the lock already filled and
//! proves nothing. One file per entry point is the only way to keep each one first, which is why
//! these are three near-identical files rather than one with three tests.
//!
//! Getting this wrong is invisible until it is expensive: with the lock empty,
//! `SingleMessageAggregateSignature::from_bytes` silently returns `None`, so a perfectly good
//! aggregate is reported as malformed by the first `verify` in a fresh process and by no other.

#[test]
fn verify_initializes_the_bytecode() {
    // Garbage in, so this returns `Err` long before any proof work. The return value is not the
    // point; what happens to the `OnceLock` on the way is.
    let _ = lean_multisig_api::verify(&[0xffu8; 64], &[0u8; 32], 0);

    // The assertion. `get_aggregation_bytecode` panics when the lock is empty, so this fails
    // loudly if `verify` ever stops initializing, or starts doing it after it parses.
    let _ = rec_aggregation::get_aggregation_bytecode();
}
