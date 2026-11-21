//! The one-time signature: `v` hash chains of `2^w - 1` steps, and the
//! target-sum code that replaces the Winternitz checksum (WOTS+C), hashed as
//! FIPS 205's WOTS+ is (§5).
//!
//! A codeword is `v` chunks summing to `T`. Two distinct words of equal sum
//! cannot be ordered componentwise, so revealing chain position `x_i` on every
//! chain gives a forger nothing: any other codeword needs a position below one
//! of the revealed ones, a preimage of a chain step. The price is that most
//! messages do not encode into the code at all, hence the counter the signer
//! searches for and the signature carries.

use crate::*;

/// A one-time key of the hypertree: its layer, counted from the bottom, its tree
/// on that layer, and its leaf in that tree.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct OtsKey {
    pub layer: usize,
    pub tree: u64,
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
            tree: e >> height,
            leaf: (e & ((1 << height) - 1)) as u32,
        }
    }

    /// The address of the key's tree, type `WOTS_HASH`.
    pub fn tree_adrs(&self) -> Adrs {
        Adrs::new(self.layer as u32, self.tree)
    }

    /// The key's address of type `t`: its tree's, with its leaf as the key pair.
    pub fn adrs(&self, t: u32) -> Adrs {
        self.tree_adrs().with_type(t).with_key_pair(self.leaf)
    }
}

/// The starts of the `v` chains of a one-time key, one `PRF` each, batched with [`keccak256::hash_many`].
fn wots_secrets(sk: &ExpandedKey, key: &OtsKey) -> [Digest; V] {
    const INPUT_LEN: usize = PREFIX_LEN + SECRET_KEY_LEN;
    let base = key.adrs(WOTS_PRF);
    let mut inputs = [[0u8; INPUT_LEN]; V];
    for (i, input) in inputs.iter_mut().enumerate() {
        input[..N].copy_from_slice(&sk.pk_seed);
        input[N..PREFIX_LEN].copy_from_slice(base.with_chain(i as u32).as_bytes());
        input[PREFIX_LEN..].copy_from_slice(&sk.sk_seed);
    }
    let mut digests = [[0u8; keccak256::OUT_LEN]; V];
    keccak256::hash_many(inputs.as_flattened(), INPUT_LEN, digests.as_flattened_mut());
    std::array::from_fn(|i| keccak256::truncate(digests[i]))
}

/// Advance every chain `i` whose predicate `active(i, from)` holds across steps `0..CHAIN_LEN - 1`,
/// batching active chains at each step with [`keccak256::hash_many`].
fn batch_chains(pk_seed: &PkSeed, key: &OtsKey, values: &mut [Digest; V], active: impl Fn(usize, usize) -> bool) {
    const INPUT_LEN: usize = PREFIX_LEN + N;
    let base = key.adrs(WOTS_HASH);
    let mut inputs = [[0u8; INPUT_LEN]; V];
    let mut digests = [[0u8; keccak256::OUT_LEN]; V];
    let mut indices = [0usize; V];
    for from in 0..CHAIN_LEN - 1 {
        let mut count = 0;
        for i in 0..V {
            if active(i, from) {
                let input = &mut inputs[count];
                input[..N].copy_from_slice(pk_seed);
                input[N..PREFIX_LEN].copy_from_slice(base.with_chain(i as u32).with_hash(from as u32).as_bytes());
                input[PREFIX_LEN..].copy_from_slice(&values[i]);
                indices[count] = i;
                count += 1;
            }
        }
        if count > 0 {
            keccak256::hash_many(
                inputs[..count].as_flattened(),
                INPUT_LEN,
                digests[..count].as_flattened_mut(),
            );
            for (k, &i) in indices[..count].iter().enumerate() {
                values[i] = keccak256::truncate(digests[k]);
            }
        }
    }
}

/// The Merkle leaf of a one-time key, its public key: `T_v` over its chain ends.
fn wots_leaf_hash(pk_seed: &PkSeed, key: &OtsKey, ends: &[Digest; V]) -> Digest {
    th_digests(pk_seed, &key.adrs(WOTS_PK), ends)
}

/// The hash of `Enc(K, M, c)` before its counter: `PK.seed | ADRS_enc(K) | M`.
fn encoder(pk_seed: &PkSeed, key: &OtsKey, message: &Digest) -> keccak256::Hasher {
    let mut hasher = hasher(pk_seed, &key.adrs(WOTS_ENC));
    hasher.update(message);
    hasher
}

/// `Enc(K, M, c)`: `Trunc_n(H(PK.seed | ADRS_enc(K) | M | BE_32(c)))` as a codeword,
/// or `None` if this counter's digest is not one.
fn encode(encoder: &keccak256::Hasher, c: u32) -> Option<[u8; V]> {
    codeword(&keccak256::truncate(
        encoder.clone().update(&c.to_be_bytes()).finalize(),
    ))
}

/// `base_2b(D, w, v)` (FIPS 205 Algorithm 4): the digest as `v` chunks of `w` bits,
/// most significant first; a codeword if they sum to `T`.
fn codeword(digest: &Digest) -> Option<[u8; V]> {
    let d = u128::from_be_bytes(*digest);
    const _: () = assert!(W == 2 && V == 64);
    const LOW: u128 = u128::MAX / 3;
    let sum = (d & LOW).count_ones() + 2 * (d & !LOW).count_ones();
    (sum == TARGET_SUM as u32)
        .then(|| std::array::from_fn(|i| ((d >> (W * (V - 1 - i))) & (CHAIN_LEN as u128 - 1)) as u8))
}

/// Counters tried per batched permutation call.
const GRIND_BATCH: usize = 64;

/// `Wots.sign`: the LEAST admissible counter, and the chain value each chunk
/// opens. Deterministic in its inputs, which is what keeps one key to one
/// codeword per message: a resumed or randomized search would leak two
/// incomparable codewords.
pub(crate) fn wots_sign(sk: &ExpandedKey, key: &OtsKey, message: &Digest) -> Option<(u32, [Digest; V])> {
    let pk_seed = &sk.pk_seed;
    // `PK.seed(16) | ADRS_enc(32) | M(16) | BE_32(c)(4)` = 68 bytes; counter sits in bytes 0..4 of lane 8.
    const ENCODE_LEN: usize = PREFIX_LEN + N + COUNTER_LEN;
    const _: () = assert!(PREFIX_LEN + N == 64 && ENCODE_LEN < keccak256::RATE);
    let mut input = [0u8; ENCODE_LEN];
    input[..N].copy_from_slice(pk_seed);
    input[N..PREFIX_LEN].copy_from_slice(key.adrs(WOTS_ENC).as_bytes());
    input[PREFIX_LEN..PREFIX_LEN + N].copy_from_slice(message);
    let template = keccak256::final_state(&input);
    let (mut values, mut digests) = ([0u128; GRIND_BATCH], [0u128; GRIND_BATCH]);
    let (c, x) = (0..MAX_ENCODING_ATTEMPTS).step_by(GRIND_BATCH).find_map(|first| {
        let n = (MAX_ENCODING_ATTEMPTS - first).min(GRIND_BATCH as u64) as usize;
        for (k, val) in values[..n].iter_mut().enumerate() {
            let c = (first + k as u64) as u32;
            *val = u128::from(u32::from_le_bytes(c.to_be_bytes()));
        }
        keccak256::digest_halves_from(&template, 8, &values[..n], &mut digests[..n]);
        digests[..n]
            .iter()
            .enumerate()
            .find_map(|(k, &d)| codeword(&d.to_le_bytes()).map(|x| ((first + k as u64) as u32, x)))
    })?;
    let mut signature = wots_secrets(sk, key);
    batch_chains(pk_seed, key, &mut signature, |i, from| from < x[i] as usize);
    Some((c, signature))
}

/// `Wots.leaf`: the leaf a claimed signature recovers, and the codeword it opens
/// at, or `None` if its counter is not admissible for the message.
pub fn wots_leaf(
    pk_seed: &PkSeed,
    key: &OtsKey,
    message: &Digest,
    c: u32,
    signature: &[Digest; V],
) -> Option<([u8; V], Digest)> {
    let x = encode(&encoder(pk_seed, key, message), c)?;
    let mut ends = *signature;
    batch_chains(pk_seed, key, &mut ends, |i, from| from >= x[i] as usize);
    Some((x, wots_leaf_hash(pk_seed, key, &ends)))
}

/// `wots_pkGen`: the leaf of a one-time key, from the secret key, what building a
/// tree spends its hashes on.
pub(crate) fn wots_public_leaf(sk: &ExpandedKey, key: &OtsKey) -> Digest {
    let mut ends = wots_secrets(sk, key);
    batch_chains(&sk.pk_seed, key, &mut ends, |_, _| true);
    wots_leaf_hash(&sk.pk_seed, key, &ends)
}
