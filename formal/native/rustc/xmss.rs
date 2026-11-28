//! `xmss_verify(ctx)`: the deployed `lean_xmss::verify` on the context of `Native/Context.lean`, its input words (from
//! byte 1024) laid out as `Native/Xmss/Layout.lean` says; returns 1 when the signature verifies, else 0.

use lean_xmss::{LeanXmssPublicKey, LeanXmssSignature, MESSAGE_LEN, PUB_KEY_SIZE, SIG_SIZE, verify};

/// The input's first word in the context.
const INPUT: usize = 1024 / 8;

/// # Safety
/// `ctx` is non-null and 8-byte aligned. Pointer arithmetic from `ctx` through
/// `ctx.add(128 + 309)` stays within one allocation, allowing its one-past end,
/// and does not wrap.
/// The 309 `u64` words starting 1024 bytes after `ctx` are initialized, readable,
/// and remain unchanged throughout the call. No other context bytes are read.
/// Their contents are unrestricted; the leaf index uses only its low 32 bits.
/// The input region is disjoint from the callee's stack.
/// The input does not overlap the verifier's own static data or GOT entries;
/// inputs from the caller's allocations or statics always satisfy this.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmss_verify(ctx: *const u64) -> u64 {
    // SAFETY: the caller's contract.
    let words = unsafe { core::slice::from_raw_parts(ctx.add(INPUT), 309) };
    let mut pk = [0; PUB_KEY_SIZE];
    let mut message = [0; MESSAGE_LEN];
    let mut sig = [0; SIG_SIZE];
    for (bytes, word) in pk.as_chunks_mut().0.iter_mut().zip(&words[..4]) {
        *bytes = word.to_le_bytes();
    }
    for (bytes, word) in message.as_chunks_mut().0.iter_mut().zip(&words[4..8]) {
        *bytes = word.to_le_bytes();
    }
    sig[..4].copy_from_slice(&(words[8] as u32).to_le_bytes());
    for (bytes, word) in sig[4..].as_chunks_mut().0.iter_mut().zip(&words[9..]) {
        *bytes = word.to_le_bytes();
    }
    let pk = LeanXmssPublicKey::from_bytes(&pk);
    u64::from(verify(&pk, &message, &LeanXmssSignature::from_bytes(&sig)))
}
