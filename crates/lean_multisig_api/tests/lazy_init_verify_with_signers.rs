//! `verify_with_signers` must initialize the aggregation bytecode too.
//!
//! In its own file so that it owns its process; see `lazy_init_verify.rs` for why.
//!
//! It has no `init` call of its own — it inherits one by delegating to `verify` before it
//! touches anything else. That is a claim about a call this function makes first, not a
//! property of its own body, so it is worth pinning separately: reordering
//! `verify_with_signers` to do any parsing of its own before delegating would break it silently.

#[test]
fn verify_with_signers_initializes_the_bytecode() {
    let _ = lean_multisig_api::verify_with_signers(&[0xffu8; 64], &[], &[0u8; 32], 0);

    // Panics if the lock is still empty.
    let _ = rec_aggregation::get_aggregation_bytecode();
}
