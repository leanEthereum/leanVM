//! `sphincs_verify(ctx)`: the deployed `lean_sphincs::verify` on the context of `Native/Context.lean`, its input words
//! (from byte 1024) laid out as `Native/Sphincs/Layout.lean` says; returns 1 when the signature verifies, else 0.

use lean_sphincs::internals::{LAYER_HEIGHTS, V};
use lean_sphincs::{LeanSphincsPublicKey, LeanSphincsSignature, MESSAGE_LEN, PUB_KEY_SIZE, SIG_SIZE, verify};

/// The input's first word in the context.
const INPUT: usize = 1024 / 8;

/// # Safety
/// `ctx` is non-null and 8-byte aligned. Pointer arithmetic from `ctx` through
/// `ctx.add(128 + 977)` stays within one allocation, allowing its one-past end,
/// and does not wrap.
/// The 977 `u64` words starting 1024 bytes after `ctx` are initialized, readable,
/// and remain unchanged throughout the call. No other context bytes are read.
/// Their contents are unrestricted; each layer counter uses only its low 32 bits.
/// The input region is disjoint from the callee's stack.
/// The input does not overlap the verifier's own static data or GOT entries;
/// inputs from the caller's allocations or statics always satisfy this.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sphincs_verify(ctx: *const u64) -> u64 {
    // SAFETY: the caller's contract.
    let words = unsafe { core::slice::from_raw_parts(ctx.add(INPUT), 977) };
    let mut pk = [0; PUB_KEY_SIZE];
    let mut message = [0; MESSAGE_LEN];
    for (bytes, word) in pk.as_chunks_mut().0.iter_mut().zip(&words[..4]) {
        *bytes = word.to_le_bytes();
    }
    for (bytes, word) in message.as_chunks_mut().0.iter_mut().zip(&words[4..8]) {
        *bytes = word.to_le_bytes();
    }
    // The randomizer and the FORS openings, words 8 .. 538; then each layer's counter (big-endian on the wire), chains
    // and path.
    let mut sig = [0; SIG_SIZE];
    let mut at = 0;
    let mut put = |bytes: &[u8]| {
        sig[at..at + bytes.len()].copy_from_slice(bytes);
        at += bytes.len();
    };
    for word in &words[8..538] {
        put(&word.to_le_bytes());
    }
    let mut k = 538;
    for height in LAYER_HEIGHTS {
        put(&(words[k] as u32).to_be_bytes());
        for word in &words[k + 1..k + 1 + 2 * (V + height)] {
            put(&word.to_le_bytes());
        }
        k += 1 + 2 * (V + height);
    }
    let pk = LeanSphincsPublicKey::from_bytes(&pk);
    u64::from(verify(&pk, &message, &LeanSphincsSignature::from_bytes(&sig)))
}
