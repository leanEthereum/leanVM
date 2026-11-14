//! The hypertree, the message digest, and the three algorithms.
//!
//! The message digest picks a bottom leaf `idx`, and so a FORS instance and the
//! one-time key on every layer above it. Nothing is reserved and nothing is
//! spent, which is what makes the scheme stateless. The bottom key signs the
//! FORS public key, the middle key the bottom tree's root, the top key the middle
//! tree's root, and the top tree's root is `PK.root`.

use crate::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LeanSphincsPublicKey {
    pub(crate) pk_seed: PkSeed,
    pub(crate) root: Digest,
}

impl LeanSphincsPublicKey {
    #[doc(hidden)]
    pub fn __pk_seed(&self) -> &PkSeed {
        &self.pk_seed
    }

    #[doc(hidden)]
    pub fn __root(&self) -> &Digest {
        &self.root
    }

    /// `PK.seed | PK.root`.
    pub fn to_bytes(&self) -> [u8; PUB_KEY_SIZE] {
        let mut out = [0; PUB_KEY_SIZE];
        out[..N].copy_from_slice(&self.pk_seed);
        out[N..].copy_from_slice(&self.root);
        out
    }

    pub fn from_bytes(bytes: &[u8; PUB_KEY_SIZE]) -> Self {
        Self {
            pk_seed: bytes[..N].try_into().unwrap(),
            root: bytes[N..].try_into().unwrap(),
        }
    }
}

/// `SK.seed`, the whole secret, with what `slh_keygen_internal` derives from it: `SK.prf` and
/// `PK.seed`.
#[derive(Clone)]
pub struct LeanSphincsSecretKey {
    pub(crate) sk_seed: Seed,
    pub(crate) sk_prf: [u8; 32],
    pub(crate) pk_seed: PkSeed,
}

impl std::fmt::Debug for LeanSphincsSecretKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LeanSphincsSecretKey").finish_non_exhaustive()
    }
}

impl LeanSphincsSecretKey {
    pub fn public_key(&self) -> LeanSphincsPublicKey {
        keygen(self).0
    }

    /// SECRET KEY MATERIAL: `SK.seed`, all of the key.
    pub fn to_bytes(&self) -> Seed {
        self.sk_seed
    }

    /// `PK.seed = Trunc_n(H(tag | SK.seed | 0))` and `SK.prf = H(tag | SK.seed | 1)`, 32 bytes, so the
    /// randomizer is as hard to predict as the key.
    pub fn from_bytes(sk_seed: &Seed) -> Self {
        let derive = |domain: u8| {
            Hasher::new()
                .update(SEED_TAG)
                .update(sk_seed)
                .update(&[domain])
                .finalize()
        };
        Self {
            sk_seed: *sk_seed,
            sk_prf: derive(1),
            pk_seed: crate::truncate(derive(0)),
        }
    }
}

/// What a signature carries for one layer: the one-time signature of what the
/// layer below gives. Its key's path is [`LeanSphincsSignature::__path`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LayerSignature {
    pub(crate) counter: u32,
    pub(crate) wots: [Digest; V],
}

impl LayerSignature {
    pub fn counter(&self) -> u32 {
        self.counter
    }

    pub fn wots(&self) -> &[Digest; V] {
        &self.wots
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeanSphincsSignature {
    pub(crate) randomizer: Digest,
    pub(crate) fors: ForsOpening,
    /// Bottom first.
    pub(crate) layers: [LayerSignature; LAYERS],
    /// The layers' paths one after the other, bottom first ([`Self::__path`]).
    pub(crate) paths: [Digest; H],
}

/// Where layer `layer`'s path sits among a signature's path nodes: after every layer below it.
fn path_range(layer: usize) -> std::ops::Range<usize> {
    let start = LAYER_HEIGHTS[..layer].iter().sum();
    start..start + LAYER_HEIGHTS[layer]
}

impl LeanSphincsSignature {
    /// `R`.
    #[doc(hidden)]
    pub fn __randomizer(&self) -> &Digest {
        &self.randomizer
    }

    #[doc(hidden)]
    pub fn __fors(&self) -> &ForsOpening {
        &self.fors
    }

    /// Bottom first.
    #[doc(hidden)]
    pub fn __layers(&self) -> &[LayerSignature; LAYERS] {
        &self.layers
    }

    /// Layer `layer`'s path in its tree, from the leaf up.
    #[doc(hidden)]
    pub fn __path(&self, layer: usize) -> &[Digest] {
        &self.paths[path_range(layer)]
    }

    /// The specification's serialization, exactly [`SIG_SIZE`] bytes: the
    /// randomizer, the FORS openings, then each layer from the bottom up, its
    /// counter (big endian), chain values and path.
    pub fn to_bytes(&self) -> [u8; SIG_SIZE] {
        let mut out = [0; SIG_SIZE];
        let mut at = 0;
        let mut put = |bytes: &[u8]| {
            out[at..at + bytes.len()].copy_from_slice(bytes);
            at += bytes.len();
        };
        put(&self.randomizer);
        for tree in &self.fors {
            put(&tree.secret);
            put(tree.path.as_flattened());
        }
        for (layer, signed) in self.layers.iter().enumerate() {
            put(&signed.counter.to_be_bytes());
            put(signed.wots.as_flattened());
            put(self.__path(layer).as_flattened());
        }
        debug_assert_eq!(at, SIG_SIZE);
        out
    }

    pub fn from_bytes(bytes: &[u8; SIG_SIZE]) -> Self {
        let mut at = 0;
        let mut take = |len: usize| {
            at += len;
            &bytes[at - len..at]
        };
        let randomizer = take(N).try_into().unwrap();
        let fors = std::array::from_fn(|_| ForsTreeOpening {
            secret: take(N).try_into().unwrap(),
            path: std::array::from_fn(|_| take(N).try_into().unwrap()),
        });
        let mut paths = [[0; N]; H];
        let layers = std::array::from_fn(|layer| {
            let signed = LayerSignature {
                counter: u32::from_be_bytes(take(COUNTER_LEN).try_into().unwrap()),
                wots: std::array::from_fn(|_| take(N).try_into().unwrap()),
            };
            for node in &mut paths[path_range(layer)] {
                *node = take(N).try_into().unwrap();
            }
            signed
        });
        debug_assert_eq!(at, SIG_SIZE);
        Self {
            randomizer,
            fors,
            layers,
            paths,
        }
    }
}

/// The index and the FORS leaves a digest spells (FIPS 205 Algorithm 19): the
/// first [`MD_BYTES`] give each tree's leaf, `a` bits a tree most significant
/// first (`base_2b`), the next [`TREE_INDEX_BYTES`] the tree, and the last
/// [`LEAF_INDEX_BYTES`] its leaf, each a big-endian integer cut to its bits.
/// The index is the tree then the leaf.
pub fn digest_fields(digest: &[u8; 32 * DIGEST_CALLS]) -> (u64, [usize; FORS_TREES]) {
    let bit = |p: usize| usize::from(digest[p / 8] >> (7 - p % 8) & 1);
    let leaves = std::array::from_fn(|c| (0..FORS_HEIGHT).fold(0, |v, j| v << 1 | bit(FORS_HEIGHT * c + j)));
    let int = |bytes: &[u8], bits: usize| bytes.iter().fold(0u64, |v, &b| v << 8 | u64::from(b)) & ((1 << bits) - 1);
    let tree = int(&digest[MD_BYTES..MD_BYTES + TREE_INDEX_BYTES], H - LAYER_HEIGHTS[0]);
    let leaf = int(&digest[MD_BYTES + TREE_INDEX_BYTES..DIGEST_BYTES], LAYER_HEIGHTS[0]);
    (tree << LAYER_HEIGHTS[0] | leaf, leaves)
}

/// The message digest read as the index and the FORS leaves.
fn message_digest(pk: &LeanSphincsPublicKey, r: &Digest, m: &Message) -> (u64, [usize; FORS_TREES]) {
    digest_fields(&h_msg(r, &pk.pk_seed, &pk.root, m))
}

/// The levels of a tree `height` levels over `leaves`, the leaves first,
/// `node(level, j, children)` hashing node `j` on `level`.
pub(crate) fn merkle_levels(
    leaves: Vec<Digest>,
    height: usize,
    node: impl Fn(usize, usize, &[Digest; 2]) -> Digest,
) -> Vec<Vec<Digest>> {
    let mut levels = vec![leaves];
    for level in 1..=height {
        let (pairs, _) = levels[level - 1].as_chunks::<2>();
        let up = pairs.iter().enumerate().map(|(j, pair)| node(level, j, pair)).collect();
        levels.push(up);
    }
    levels
}

/// Node `j` at height `z` of the tree holding `key`, from its two children.
fn node(pk_seed: &PkSeed, key: &OtsKey, z: usize, j: usize, children: &[Digest; 2]) -> Digest {
    let adrs = key
        .tree_adrs()
        .with_type(TREE)
        .with_tree_height(z as u32)
        .with_tree_index(j as u32);
    th_digests(pk_seed, &adrs, children)
}

/// The levels of the tree holding `key`, its leaves first and its root last.
fn tree_levels(sk: &LeanSphincsSecretKey, key: &OtsKey) -> Vec<Vec<Digest>> {
    let height = LAYER_HEIGHTS[key.layer];
    let leaves = (0..1 << height)
        .map(|leaf| wots_public_leaf(sk, &OtsKey { leaf, ..*key }))
        .collect();
    merkle_levels(leaves, height, |z, j, pair| node(&sk.pk_seed, key, z, j, pair))
}

/// `Gen`, deterministic: the seed is `SK.seed`, and the top tree gives `PK.root`.
pub fn key_gen_from_seed(seed: Seed) -> (LeanSphincsSecretKey, LeanSphincsPublicKey) {
    let sk = LeanSphincsSecretKey::from_bytes(&seed);
    let pk = keygen(&sk).0;
    (sk, pk)
}

/// `slh_keygen_internal`: the public key, `PK.seed` and the top tree's root, with
/// the top tree's levels, which signing reuses.
fn keygen(sk: &LeanSphincsSecretKey) -> (LeanSphincsPublicKey, Vec<Vec<Digest>>) {
    let top = tree_levels(sk, &OtsKey::of_index(LAYERS - 1, 0));
    let pk = LeanSphincsPublicKey {
        pk_seed: sk.pk_seed,
        root: top[LAYER_HEIGHTS[LAYERS - 1]][0],
    };
    (pk, top)
}

/// `Gen`, on a fresh seed from the operating system's randomness.
pub fn key_gen() -> (LeanSphincsSecretKey, LeanSphincsPublicKey) {
    key_gen_from_seed(rand::random())
}

/// `Sign`. Deterministic and stateless. A key signs at most `2^30` messages (`doc/lean_sphincs`).
///
/// # Panics
///
/// Where the specification's `Sign` fails: when all `C_max` encoding counters of a layer miss a
/// codeword, which happens with probability below `2^-378193`: impossible in practice.
///
/// `slh_sign_internal`, deterministic (`opt_rand = PK.seed`): it builds the top tree for `PK.root`
/// and the top path, then the FORS instance and the two trees below.
pub fn sign(sk: &LeanSphincsSecretKey, message: &Message) -> LeanSphincsSignature {
    let (pk, mut top) = keygen(sk);
    let r = prf_msg(&sk.sk_prf, &sk.pk_seed, message);
    let (idx, leaves) = message_digest(&pk, &r, message);
    let (mut signed, fors) = fors_open(sk, idx, &leaves);
    let mut layers = [LayerSignature {
        counter: 0,
        wots: [[0; N]; V],
    }; LAYERS];
    let mut paths = [[0; N]; H];
    for (layer, signature) in layers.iter_mut().enumerate() {
        let key = OtsKey::of_index(layer, idx);
        let (counter, wots) = wots_sign(sk, &key, &signed).expect("a codeword within C_max counters (see `sign`)");
        *signature = LayerSignature { counter, wots };
        let levels = if layer == LAYERS - 1 {
            std::mem::take(&mut top)
        } else {
            tree_levels(sk, &key)
        };
        for (z, node) in paths[path_range(layer)].iter_mut().enumerate() {
            *node = levels[z][(key.leaf as usize >> z) ^ 1];
        }
        signed = levels[LAYER_HEIGHTS[layer]][0];
    }
    LeanSphincsSignature {
        randomizer: r,
        fors,
        layers,
        paths,
    }
}

/// `Tree.fold`: the root a key's leaf and its path reach, showing `visit` the two
/// children of every node on the way up.
pub fn tree_fold(
    pk_seed: &PkSeed,
    key: &OtsKey,
    leaf: Digest,
    path: &[Digest],
    visit: impl FnMut(&[Digest; 2]),
) -> Digest {
    crate::path_fold(leaf, key.leaf as usize, path, visit, |z, j, pair| {
        node(pk_seed, key, z, j, pair)
    })
}

/// `Ver`: whether `signature` is `pk`'s on `message`.
pub fn verify(pk: &LeanSphincsPublicKey, message: &Message, signature: &LeanSphincsSignature) -> bool {
    let pk_seed = &pk.pk_seed;
    let (idx, leaves) = message_digest(pk, &signature.randomizer, message);
    let mut signed = fors_recover(pk_seed, idx, &leaves, &signature.fors, |_| ());
    for (layer, layer_sig) in signature.layers.iter().enumerate() {
        let key = OtsKey::of_index(layer, idx);
        let Some((_, leaf)) = wots_leaf(pk_seed, &key, &signed, layer_sig.counter, &layer_sig.wots) else {
            return false;
        };
        signed = tree_fold(pk_seed, &key, leaf, signature.__path(layer), |_| ());
    }
    signed == pk.root
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A known answer, byte for byte: the key whose `SK.seed` is `S[i] = 37 i + 11`
    /// and its signature of `m[i] = 7 i + 3`.
    #[test]
    fn known_answer() {
        let mut lines = include_str!("known_answer.hex").lines();
        let mut unhex = || {
            let s = lines.next().unwrap();
            (0..s.len())
                .step_by(2)
                .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
                .collect::<Vec<_>>()
        };
        let (pk_bytes, sig_bytes) = (unhex(), unhex());
        let sk = LeanSphincsSecretKey::from_bytes(&std::array::from_fn(|i| (37 * i + 11) as u8));
        let pk = keygen(&sk).0;
        let message: Message = std::array::from_fn(|i| (7 * i + 3) as u8);
        assert_eq!(pk.to_bytes()[..], pk_bytes[..]);
        let signature = sign(&sk, &message);
        assert_eq!(signature.to_bytes()[..], sig_bytes[..]);
        assert!(verify(&pk, &message, &signature));
    }
}
