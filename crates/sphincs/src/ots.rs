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

/// One one-time key's position: the layer, the tree within it, the leaf within
/// that tree.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Pos {
    pub lay: usize,
    pub tau: u32,
    pub e: u32,
}

impl Pos {
    pub const fn new(lay: usize, tau: u32, e: u32) -> Self {
        Self { lay, tau, e }
    }
}

/// `sk_{lay,tau,e,i} = Th(P, tw_prf(lay,tau,i,e), S)`.
pub fn ots_secret(pp: &PublicParam, master: &MasterSecret, pos: Pos, i: usize) -> Digest {
    th(pp, &tweak(TWEAK_PRF, pos.lay, pos.tau, i as u32, pos.e), master)
}

/// `Chain_{lay,tau,e,i}(P, start, steps, value)`: the step onto position `s` is
/// hashed under the tweak of the edge into it.
pub fn chain(pp: &PublicParam, pos: Pos, i: usize, start: usize, steps: usize, value: Digest) -> Digest {
    debug_assert!(start + steps < CHAIN_LEN);
    (1..=steps).fold(value, |current, step| {
        let p = (CHAIN_LEN * i + start + step - 1) as u32;
        th(pp, &tweak(TWEAK_CHAIN, pos.lay, pos.tau, p, pos.e), &current)
    })
}

/// The Merkle leaf of a one-time key: `Th` over its `v` chain tips.
pub fn ots_leaf_hash(pp: &PublicParam, pos: Pos, tips: &[Digest; V]) -> Digest {
    th_digests(pp, &tweak(TWEAK_LEAF, pos.lay, pos.tau, 0, pos.e), tips)
}

/// `Enc(P, lay, tau, e, M, c)`: the codeword, or `None` if the digest of that
/// counter is not admissible.
pub fn encode(pp: &PublicParam, pos: Pos, m: &Digest, c: u32) -> Option<[u8; V]> {
    let mut payload = [0u8; N + COUNTER_LEN];
    payload[..N].copy_from_slice(m);
    payload[N..].copy_from_slice(&c.to_le_bytes());
    codeword(&th(pp, &tweak(TWEAK_ENC, pos.lay, pos.tau, 0, pos.e), &payload))
}

/// Each 64-bit half of the digest holds `v/2` chunks of `w` bits and one pinned
/// top bit; pinning it is what makes the codeword determine the digest.
fn codeword(digest: &Digest) -> Option<[u8; V]> {
    let mut x = [0u8; V];
    let mut sum = 0;
    for (q, half) in digest.as_chunks::<{ N / 2 }>().0.iter().enumerate() {
        let d = u64::from_le_bytes(*half);
        if d >> (W * V / 2) != 0 {
            return None;
        }
        for r in 0..V / 2 {
            let chunk = ((d >> (W * r)) & (CHAIN_LEN as u64 - 1)) as u8;
            x[q * (V / 2) + r] = chunk;
            sum += chunk as usize;
        }
    }
    (sum == TARGET_SUM).then_some(x)
}

/// `Ots.sign`: the LEAST admissible counter, and the chain value each chunk
/// opens. Deterministic in its inputs, which is what keeps one key to one
/// codeword: a resumed or randomized search would leak two incomparable
/// codewords and drop forgery to about `2^53`.
pub fn ots_sign(pp: &PublicParam, master: &MasterSecret, pos: Pos, m: &Digest) -> Option<(u32, [Digest; V])> {
    let (c, x) = (0..MAX_ENCODING_ATTEMPTS).find_map(|c| encode(pp, pos, m, c as u32).map(|x| (c as u32, x)))?;
    let signature = std::array::from_fn(|i| chain(pp, pos, i, 0, x[i] as usize, ots_secret(pp, master, pos, i)));
    Some((c, signature))
}

/// `Ots.leaf`: the leaf a claimed signature recovers, or `None` if its counter
/// is not admissible for `m`. Does not touch the secrets, which is why it is the
/// verifier's half.
pub fn ots_leaf(pp: &PublicParam, pos: Pos, m: &Digest, c: u32, signature: &[Digest; V]) -> Option<Digest> {
    let x = encode(pp, pos, m, c)?;
    let tips = std::array::from_fn(|i| {
        let start = x[i] as usize;
        chain(pp, pos, i, start, CHAIN_LEN - 1 - start, signature[i])
    });
    Some(ots_leaf_hash(pp, pos, &tips))
}

/// The leaf of the one-time key at `pos`, from the master secret: what key
/// generation and every tree rebuild spend their hashes on.
pub fn ots_public_leaf(pp: &PublicParam, master: &MasterSecret, pos: Pos) -> Digest {
    let tips = std::array::from_fn(|i| chain(pp, pos, i, 0, CHAIN_LEN - 1, ots_secret(pp, master, pos, i)));
    ots_leaf_hash(pp, pos, &tips)
}
