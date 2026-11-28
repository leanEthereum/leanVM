//! `sphincs_verify(pk, msg, sig)`: the deployed `lean_sphincs::verify` on raw FIPS 205 byte arrays;
//! returns 1 when the signature verifies, else 0.

use lean_sphincs::{LeanSphincsPublicKey, LeanSphincsSignature, MESSAGE_LEN, PUB_KEY_SIZE, SIG_SIZE, verify};

/// # Safety
/// `pk`, `msg`, and `sig` are non-null and readable over `PUB_KEY_SIZE` (32), `MESSAGE_LEN` (32),
/// and `SIG_SIZE` (7740) bytes respectively (any alignment), remain unchanged throughout the call,
/// do not wrap the address space, and are disjoint from the callee's stack, static data, and GOT entries.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sphincs_verify(
    pk: *const [u8; PUB_KEY_SIZE],
    msg: *const [u8; MESSAGE_LEN],
    sig: *const [u8; SIG_SIZE],
) -> u64 {
    // SAFETY: the caller's contract.
    let pk = LeanSphincsPublicKey::from_bytes(unsafe { &*pk });
    let msg = unsafe { &*msg };
    let sig = LeanSphincsSignature::from_bytes(unsafe { &*sig });
    u64::from(verify(&pk, msg, &sig))
}
