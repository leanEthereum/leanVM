//! The one-time signature: `v` hash chains of `2^w - 1` steps, and the
//! target-sum code that replaces the Winternitz checksum (WOTS+C).
//!
//! A codeword is `v` chunks summing to `T`. Two distinct words of equal sum
//! cannot be ordered componentwise, so revealing chain position `x_i` on every
//! chain gives a forger nothing: any other codeword needs a value above one of
//! the revealed ones. The price is that most messages do not encode into the
//! code at all, hence the counter the signer searches for and the signature
//! carries.

use crate::*;

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

/// `Enc(P, e, M, c)`: the codeword, or `None` if this counter's digest is not one.
pub fn encode(pp: &PublicParam, e: u32, m: &Digest, c: u32) -> Option<[u8; V]> {
    let mut payload = [0u8; N + COUNTER_LEN];
    payload[..N].copy_from_slice(m);
    payload[N..].copy_from_slice(&c.to_le_bytes());
    codeword(&th(pp, &tweak(TWEAK_ENC, 0, e), &payload))
}

/// The digest as `v` chunks of `w` bits, little endian; a codeword if they sum
/// to `T`.
fn codeword(digest: &Digest) -> Option<[u8; V]> {
    let d = u128::from_le_bytes(*digest);
    let x: [u8; V] = std::array::from_fn(|i| ((d >> (W * i)) & (CHAIN_LEN as u128 - 1)) as u8);
    (x.iter().map(|&chunk| chunk as usize).sum::<usize>() == TARGET_SUM).then_some(x)
}

/// `Ots.sign`: the LEAST admissible counter, and the chain value each chunk
/// opens. Deterministic in its inputs, which is what keeps one key to one
/// codeword: a resumed or randomized search would leak two incomparable
/// codewords.
pub fn wots_sign(pp: &PublicParam, master: &MasterSecret, e: u32, m: &Digest) -> Option<(u32, [Digest; V])> {
    let (c, x) = (0..MAX_ENCODING_ATTEMPTS).find_map(|c| encode(pp, e, m, c as u32).map(|x| (c as u32, x)))?;
    let secrets = wots_secrets(pp, master, e);
    let signature = std::array::from_fn(|i| chain(pp, e, i, 0, x[i] as usize, secrets[i]));
    Some((c, signature))
}

/// `Ots.leaf`: the leaf a claimed signature recovers, or `None` if its counter
/// is not admissible for `m`.
pub fn wots_leaf(pp: &PublicParam, e: u32, m: &Digest, c: u32, signature: &[Digest; V]) -> Option<Digest> {
    let x = encode(pp, e, m, c)?;
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
