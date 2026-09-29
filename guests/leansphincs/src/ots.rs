//! The one-time signature: `v` hash chains, and the target-sum code that replaces
//! the Winternitz checksum (WOTS+C).
//!
//! Two codewords of equal sum are never ordered chunk by chunk.
//!
//! So a revealed signature gives a forger no chain value it could extend.

use crate::*;

/// `sk_{lay,tau,e,i}`: the start of chain `i`, derived from the master secret.
pub(crate) fn secret(pp: &PublicParam, master: &[u64; 4], pos: Pos, i: usize) -> Digest {
    th(pp, &tweak(TWEAK_PRF, pos.lay, pos.tau, i as u32, pos.e), master)
}

/// `Chain`: walk chain `i` for `steps` steps from value number `start`.
///
/// The step out of value `s` is hashed at position `8i + s`, so no two steps share a tweak.
pub(crate) fn chain(pp: &PublicParam, pos: Pos, i: usize, start: usize, steps: usize, value: Digest) -> Digest {
    (start..start + steps).fold(value, |value, s| {
        th(
            pp,
            &tweak(TWEAK_CHAIN, pos.lay, pos.tau, (CHAIN_LEN * i + s) as u32, pos.e),
            &value,
        )
    })
}

/// The Merkle leaf of a one-time key: `Th` over its `v` chain ends.
pub(crate) fn leaf_hash(pp: &PublicParam, pos: Pos, ends: &[Digest; V]) -> Digest {
    th::<{ 2 * V }>(
        pp,
        &tweak(TWEAK_LEAF, pos.lay, pos.tau, 0, pos.e),
        ends.as_flattened().try_into().unwrap(),
    )
}

/// `Enc`: the codeword of `message` under `counter`, or `None` if it has none.
///
/// Each 64-bit half of the digest is 21 chunks of `w` bits and a top bit pinned to zero.
///
/// Pinning it makes the codeword determine the digest.
pub(crate) fn encode(pp: &PublicParam, pos: Pos, message: &Digest, counter: u32) -> Option<[u8; V]> {
    // `M | counter`: the counter is 4 bytes, so it takes the byte path.
    let mut hasher = Blake2s::new();
    hasher
        .update_words(&tweak(TWEAK_ENC, pos.lay, pos.tau, 0, pos.e))
        .update_words(pp);
    hasher.update_words(message).update(&counter.to_le_bytes());
    let digest = hasher.finalize_words();
    let mut x = [0; V];
    let mut sum = 0;
    for (q, &d) in digest[..2].iter().enumerate() {
        // Bit 63 of each half is pinned to zero.
        if d >> (W * V / 2) != 0 {
            return None;
        }
        // Chunk `r` of the half is bits `3r..3r+3`.
        for r in 0..V / 2 {
            let chunk = (d >> (W * r)) as u8 & (CHAIN_LEN as u8 - 1);
            x[q * V / 2 + r] = chunk;
            sum += chunk as usize;
        }
    }
    (sum == TARGET_SUM).then_some(x)
}

/// `Ots.leaf`: the leaf a one-time signature recovers, or `None` if `counter` gives no codeword.
pub(crate) fn leaf(pp: &PublicParam, pos: Pos, message: &Digest, counter: u32, ots: &[Digest; V]) -> Option<Digest> {
    let x = encode(pp, pos, message, counter)?;
    // Chain `i` was opened at value `x_i`: walk it the rest of the way to value 7.
    let ends = core::array::from_fn(|i| {
        let start = x[i] as usize;
        chain(pp, pos, i, start, CHAIN_LEN - 1 - start, ots[i])
    });
    Some(leaf_hash(pp, pos, &ends))
}
