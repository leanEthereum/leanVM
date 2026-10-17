//! The one-time signature, WOTS+C: `v` hash chains of `2^w - 1` steps, and a
//! target-sum code in place of the Winternitz checksum.
//!
//! A layer's message digest is `Th(P, A, M | R)`, read as `DIGITS` digits of `w`
//! bits, little endian. It is a codeword when its last `ZERO_DIGITS` digits are
//! zero, so those have no chain, and the other `v` sum to `T`. The signer grinds the
//! randomizer `R` until it is, one compression a trial.

use crate::lean_xmss::*;

/// The index of `leaf_index`'s one-time key on `layer`: the leaf index itself at
/// the bottom, the bottom tree's index at the top.
pub fn layer_index(leaf_index: LeafIndex, layer: usize) -> u32 {
    (leaf_index as u64 >> (layer * LAYER_HEIGHT)) as u32
}

/// `leaf_index`'s leaf within its bottom tree.
pub fn tree_leaf(leaf_index: LeafIndex) -> u32 {
    leaf_index & ((1 << LAYER_HEIGHT) - 1)
}

/// The starts of the `v` chains of key `e` on `layer`. One hash of the seed gives
/// two of them: chains `2t` and `2t + 1` are its two halves.
pub fn wots_secrets(pp: &PublicParam, seed: &Seed, layer: usize, e: u32) -> [Digest; V] {
    let mut secrets = [[0u8; N]; V];
    for (t, pair) in secrets.as_chunks_mut::<2>().0.iter_mut().enumerate() {
        *pair = th_pair(pp, &tweak(TWEAK_PRF, layer_hi(layer, t as u32), e), seed);
    }
    secrets
}

/// `steps` steps of chain `i` from position `start`. A step's address carries the
/// position it leaves, and the chain index rides after the value, so the address is
/// the same for every chain of a key.
pub fn chain(pp: &PublicParam, layer: usize, e: u32, i: usize, start: usize, steps: usize, value: Digest) -> Digest {
    debug_assert!(start + steps < CHAIN_LEN);
    (start..start + steps).fold(value, |current, from| {
        th_digests(
            pp,
            &tweak(TWEAK_CHAIN, layer_hi(layer, 0), e).step(from),
            &[current, (i as u128).to_le_bytes()],
        )
    })
}

/// The Merkle leaf of a one-time key: `Th` over its `v` chain ends.
pub fn wots_leaf_hash(pp: &PublicParam, layer: usize, e: u32, ends: &[Digest; V]) -> Digest {
    th_digests(pp, &tweak(TWEAK_LEAF, layer_hi(layer, 0), e), ends)
}

/// The digest key `e` on `layer` signs: `Th(P, A, M | R)`, `M` the message at the
/// bottom and the bottom root at the top.
pub fn message_digest(pp: &PublicParam, layer: usize, e: u32, randomizer: &Randomizer, message: &[u8]) -> Digest {
    digest_prefix(pp, layer, e, message).hash(randomizer)[..N]
        .try_into()
        .unwrap()
}

/// `P | A | M`, which fills the bottom digest's first block, so a randomizer trial
/// compresses only the block holding `R`.
fn digest_prefix(pp: &PublicParam, layer: usize, e: u32, message: &[u8]) -> primitives::hash::Prefix {
    let mut prefix = hasher(pp, &tweak(TWEAK_MSG, layer_hi(layer, 0), e));
    prefix.update(message);
    prefix.prefix()
}

/// The digest's first `v` digits, if it is a codeword.
pub fn codeword(digest: &Digest) -> Option<[u8; V]> {
    let d = u128::from_le_bytes(*digest);
    let x: [u8; V] = std::array::from_fn(|i| ((d >> (W * i)) & (CHAIN_LEN as u128 - 1)) as u8);
    let sum: usize = x.iter().map(|&digit| digit as usize).sum();
    (d >> (W * V) == 0 && sum == TARGET_SUM).then_some(x)
}

/// Randomizer trials searched per parallel dispatch: the first hit is expected
/// after about `2^20`, and a batch has to be small for the search to stop near it.
const GRIND_BATCH: u64 = 1 << 14;

/// `Ots.sign`: the randomizer of the LEAST admissible trial `R_0 + c`, `R_0` a hash
/// of the seed and the message, and the chain value each digit opens. Deterministic
/// in its inputs, so signing one message again gives the same signature and a key
/// never opens two codewords.
pub fn wots_sign(
    pp: &PublicParam,
    seed: &Seed,
    layer: usize,
    e: u32,
    message: &[u8],
) -> Option<(Randomizer, [Digest; V])> {
    let base = {
        let mut hasher = hasher(pp, &tweak(TWEAK_RANDOMIZER, layer_hi(layer, 0), e));
        hasher.update(seed).update(message);
        u128::from_le_bytes(hasher.finalize()[..RANDOMIZER_LEN].try_into().unwrap())
    };
    let trial = |c: u64| base.wrapping_add(u128::from(c)).to_le_bytes();
    let prefix = digest_prefix(pp, layer, e, message);
    let admits = |c: u64| {
        let digest = prefix.hash(&trial(c));
        codeword(&digest[..N].try_into().unwrap()).is_some()
    };
    let c = (0..MAX_RANDOMIZER_TRIALS)
        .step_by(GRIND_BATCH as usize)
        .find_map(|start| {
            parallel::find_first(GRIND_BATCH as usize, |i| admits(start + i as u64)).map(|i| start + i as u64)
        })?;
    let randomizer = trial(c);
    let x = codeword(&message_digest(pp, layer, e, &randomizer, message))?;
    let secrets = wots_secrets(pp, seed, layer, e);
    let values = std::array::from_fn(|i| chain(pp, layer, e, i, 0, x[i] as usize, secrets[i]));
    Some((randomizer, values))
}

/// `Ots.leaf`: the leaf a claimed signature recovers, with its codeword, or `None`
/// if the digest is not a codeword.
pub fn wots_leaf(
    pp: &PublicParam,
    layer: usize,
    e: u32,
    message: &[u8],
    randomizer: &Randomizer,
    values: &[Digest; V],
) -> Option<([u8; V], Digest)> {
    let x = codeword(&message_digest(pp, layer, e, randomizer, message))?;
    let ends = std::array::from_fn(|i| {
        let start = x[i] as usize;
        chain(pp, layer, e, i, start, CHAIN_LEN - 1 - start, values[i])
    });
    Some((x, wots_leaf_hash(pp, layer, e, &ends)))
}

/// The leaf of key `e` on `layer`, from the seed: what key generation spends its
/// hashes on.
pub fn wots_public_leaf(pp: &PublicParam, seed: &Seed, layer: usize, e: u32) -> Digest {
    let secrets = wots_secrets(pp, seed, layer, e);
    let ends = std::array::from_fn(|i| chain(pp, layer, e, i, 0, CHAIN_LEN - 1, secrets[i]));
    wots_leaf_hash(pp, layer, e, &ends)
}
