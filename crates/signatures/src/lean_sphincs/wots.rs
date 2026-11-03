//! The one-time signature: `v` hash chains of `2^w - 1` steps, and the
//! target-sum code that replaces the Winternitz checksum (WOTS+C).
//!
//! A codeword is `v` chunks summing to `T`. Two distinct words of equal sum
//! cannot be ordered componentwise, so revealing chain position `x_i` on every
//! chain gives a forger nothing: any other codeword needs a value above one of
//! the revealed ones. The price is that most messages do not encode into the
//! code at all, hence the counter the signer searches for and the signature
//! carries.

use crate::lean_sphincs::*;

/// The starts of the `v` chains of the one-time key at leaf `e`. One hash of the
/// seed gives two of them: chains `2t` and `2t + 1` are its two halves.
pub fn wots_secrets(pp: &PublicParam, master: &MasterSecret, e: u32) -> [Digest; V] {
    let mut secrets = [[0u8; N]; V];
    for (t, pair) in secrets.as_chunks_mut::<2>().0.iter_mut().enumerate() {
        *pair = th_pair(pp, &tweak(TWEAK_PRF, t as u32, e), master);
    }
    secrets
}

/// `steps` steps of chain `i` from position `start`; a step carries the position
/// it leaves.
pub fn chain(pp: &PublicParam, e: u32, i: usize, start: usize, steps: usize, value: Digest) -> Digest {
    debug_assert!(start + steps < CHAIN_LEN);
    (start..start + steps).fold(value, |current, from| {
        th(pp, &tweak(TWEAK_CHAIN, i as u32, e).step(from), &current)
    })
}

/// The Merkle leaf of a one-time key: `Th` over its `v` chain ends.
pub fn wots_leaf_hash(pp: &PublicParam, e: u32, ends: &[Digest; V]) -> Digest {
    th_digests(pp, &tweak(TWEAK_LEAF, 0, e), ends)
}

/// Bytes of the encoder's hash input before the counter: `P | A | K`, the forest
/// key's sixteen nodes.
const ENCODER_LEN: usize = PUBLIC_PARAM_LEN + ADDRESS_LEN + N * 2 * FOREST_TREES;

/// `Enc(P, e, K, .)`'s input with its counter zero. The counter falls in the last
/// block, so a signer grinding it pays one permutation a counter.
fn encoder(pp: &PublicParam, e: u32, key: &ForestKey) -> [u8; ENCODER_LEN + COUNTER_LEN] {
    let mut input = [0u8; ENCODER_LEN + COUNTER_LEN];
    input[..PUBLIC_PARAM_LEN].copy_from_slice(pp);
    input[PUBLIC_PARAM_LEN..][..ADDRESS_LEN].copy_from_slice(&address(&tweak(TWEAK_ENC, 0, e)));
    input[PUBLIC_PARAM_LEN + ADDRESS_LEN..ENCODER_LEN].copy_from_slice(key.as_flattened().as_flattened());
    input
}

fn encode_from(encoder: &[u8; ENCODER_LEN + COUNTER_LEN], c: u32) -> Option<[u8; V]> {
    let mut input = *encoder;
    input[ENCODER_LEN..].copy_from_slice(&c.to_le_bytes());
    codeword(&primitives::hash::hash(&input)[..N].try_into().unwrap())
}

/// `Enc(P, e, K, c)`: the codeword, or `None` if this counter's digest is not one.
pub fn encode(pp: &PublicParam, e: u32, key: &ForestKey, c: u32) -> Option<[u8; V]> {
    encode_from(&encoder(pp, e, key), c)
}

/// The digest as `v` chunks of `w` bits, little endian; a codeword if they sum
/// to `T`.
fn codeword(digest: &Digest) -> Option<[u8; V]> {
    const _: () = assert!(W == 2 && W * V == 128);
    // A chunk is its low bit plus twice its high bit.
    const LOW: u128 = u128::MAX / 3;
    let d = u128::from_le_bytes(*digest);
    let sum = ((d & LOW).count_ones() + 2 * (d & !LOW).count_ones()) as usize;
    (sum == TARGET_SUM).then(|| std::array::from_fn(|i| ((d >> (W * i)) & (CHAIN_LEN as u128 - 1)) as u8))
}

/// `Ots.sign`: the LEAST admissible counter, and the chain value each chunk
/// opens. Deterministic in its inputs, which is what keeps one key to one
/// codeword: a resumed or randomized search would leak two incomparable
/// codewords.
pub fn wots_sign(pp: &PublicParam, master: &MasterSecret, e: u32, key: &ForestKey) -> Option<(u32, [Digest; V])> {
    let encoder = encoder(pp, e, key);
    let c = crate::grind::least_admissible(
        &encoder,
        ENCODER_LEN,
        MAX_ENCODING_ATTEMPTS,
        |c| [c, 0],
        |digest| codeword(&digest[..N].try_into().unwrap()).is_some(),
    )?;
    let x = encode_from(&encoder, c as u32)?;
    let secrets = wots_secrets(pp, master, e);
    let signature = std::array::from_fn(|i| chain(pp, e, i, 0, x[i] as usize, secrets[i]));
    Some((c as u32, signature))
}

/// `Ots.leaf`: the leaf a claimed signature recovers, or `None` if its counter
/// is not admissible for the key.
pub fn wots_leaf(pp: &PublicParam, e: u32, key: &ForestKey, c: u32, signature: &[Digest; V]) -> Option<Digest> {
    let x = encode(pp, e, key, c)?;
    let ends = std::array::from_fn(|i| {
        let start = x[i] as usize;
        chain(pp, e, i, start, CHAIN_LEN - 1 - start, signature[i])
    });
    Some(wots_leaf_hash(pp, e, &ends))
}

/// The leaf of the one-time key at `e`, from the seed: what key generation
/// spends its hashes on.
pub fn wots_public_leaf(pp: &PublicParam, master: &MasterSecret, e: u32) -> Digest {
    let secrets = wots_secrets(pp, master, e);
    let ends = std::array::from_fn(|i| chain(pp, e, i, 0, CHAIN_LEN - 1, secrets[i]));
    wots_leaf_hash(pp, e, &ends)
}
