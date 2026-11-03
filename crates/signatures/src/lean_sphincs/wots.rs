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

/// A one-time key of the hypertree: its layer, counted from the bottom, its tree
/// on that layer, and its leaf in that tree.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct OtsKey {
    pub layer: usize,
    pub tree: u32,
    pub leaf: u32,
}

impl OtsKey {
    /// The key of `layer` on the way from bottom leaf `idx` up: the bits below
    /// the layer dropped, the rest split into a tree and a leaf.
    pub fn of_index(layer: usize, idx: u64) -> Self {
        let height = LAYER_HEIGHTS[layer];
        let e = idx >> LAYER_HEIGHTS[..layer].iter().sum::<usize>();
        Self {
            layer,
            tree: (e >> height) as u32,
            leaf: (e & ((1 << height) - 1)) as u32,
        }
    }

    /// The key's address of type `t`: its leaf in `lo`, its layer and tree.
    pub fn tweak(&self, t: u8, hi: u32) -> Tweak {
        tweak(t, hi, self.leaf).at(self.layer, self.tree)
    }
}

/// The starts of the `v` chains of a one-time key. One hash of the seed gives
/// two of them: chains `2j` and `2j + 1` are its two halves.
pub fn wots_secrets(pp: &PublicParam, seed: &MasterSecret, key: &OtsKey) -> [Digest; V] {
    let mut secrets = [[0u8; N]; V];
    for (j, pair) in secrets.as_chunks_mut::<2>().0.iter_mut().enumerate() {
        *pair = th_pair(pp, &key.tweak(TWEAK_PRF, j as u32), seed);
    }
    secrets
}

/// `steps` steps of chain `i` from position `start`; a step carries the position
/// it leaves.
pub fn chain(pp: &PublicParam, key: &OtsKey, i: usize, start: usize, steps: usize, value: Digest) -> Digest {
    debug_assert!(start + steps < CHAIN_LEN);
    let tw = key.tweak(TWEAK_CHAIN, i as u32);
    (start..start + steps).fold(value, |current, from| th(pp, &tw.step(from), &current))
}

/// The Merkle leaf of a one-time key: `Th` over its `v` chain ends.
pub fn wots_leaf_hash(pp: &PublicParam, key: &OtsKey, ends: &[Digest; V]) -> Digest {
    th_digests(pp, &key.tweak(TWEAK_LEAF, 0), ends)
}

/// The hash of `Enc(P, K, M, .)` before its counter: `P | A | M`. The counter
/// falls in the last block, so a signer grinding it pays one permutation a
/// counter.
fn encoder(pp: &PublicParam, key: &OtsKey, message: &[u8]) -> primitives::hash::Hasher {
    let mut hasher = hasher(pp, &key.tweak(TWEAK_ENC, 0));
    hasher.update(message);
    hasher
}

fn encode_from(encoder: &primitives::hash::Hasher, c: u32) -> Option<[u8; V]> {
    let output = encoder.clone().update(&c.to_le_bytes()).finalize();
    codeword(&output[..N].try_into().unwrap())
}

/// `Enc(P, K, M, c) = Th(P, A_enc(K), M | LE_32(c))` as a codeword, or `None` if
/// this counter's digest is not one.
pub fn encode(pp: &PublicParam, key: &OtsKey, message: &[u8], c: u32) -> Option<[u8; V]> {
    encode_from(&encoder(pp, key, message), c)
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
/// codeword per message: a resumed or randomized search would leak two
/// incomparable codewords.
pub fn wots_sign(pp: &PublicParam, seed: &MasterSecret, key: &OtsKey, message: &[u8]) -> Option<(u32, [Digest; V])> {
    let encoder = encoder(pp, key, message);
    let (c, x) = (0..MAX_ENCODING_ATTEMPTS).find_map(|c| encode_from(&encoder, c as u32).map(|x| (c as u32, x)))?;
    let secrets = wots_secrets(pp, seed, key);
    let signature = std::array::from_fn(|i| chain(pp, key, i, 0, x[i] as usize, secrets[i]));
    Some((c, signature))
}

/// `Ots.leaf`: the leaf a claimed signature recovers, and the codeword it opens
/// at, or `None` if its counter is not admissible for the message.
pub fn wots_leaf(
    pp: &PublicParam,
    key: &OtsKey,
    message: &[u8],
    c: u32,
    signature: &[Digest; V],
) -> Option<([u8; V], Digest)> {
    let x = encode(pp, key, message, c)?;
    let ends = std::array::from_fn(|i| {
        let start = x[i] as usize;
        chain(pp, key, i, start, CHAIN_LEN - 1 - start, signature[i])
    });
    Some((x, wots_leaf_hash(pp, key, &ends)))
}

/// The leaf of a one-time key, from the seed: what building a tree spends its
/// hashes on.
pub fn wots_public_leaf(pp: &PublicParam, seed: &MasterSecret, key: &OtsKey) -> Digest {
    let secrets = wots_secrets(pp, seed, key);
    let ends = std::array::from_fn(|i| chain(pp, key, i, 0, CHAIN_LEN - 1, secrets[i]));
    wots_leaf_hash(pp, key, &ends)
}
