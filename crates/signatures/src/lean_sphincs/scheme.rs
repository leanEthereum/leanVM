//! The hypertree, the message digest, and the three algorithms.
//!
//! The message digest picks a bottom leaf `idx`, and so a FORS instance and the
//! one-time key on every layer above it. Nothing is reserved and nothing is
//! spent, which is what makes the scheme stateless. The bottom key signs the
//! FORS key, the middle key the bottom tree's root, the top key the middle
//! tree's root, and the top tree's root is the public key.

use rand::{CryptoRng, Rng};
use serde::{Deserialize, Serialize};

use crate::lean_sphincs::*;

/// Ordered lexicographically on [`Self::flatten`], which is what an aggregate's
/// signer list is sorted and deduplicated by.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct LeanSphincsPublicKey {
    pub root: Digest,
    pub public_param: PublicParam,
}

impl LeanSphincsPublicKey {
    pub fn flatten(&self) -> [u8; PUB_KEY_SIZE] {
        let mut out = [0; PUB_KEY_SIZE];
        out[..N].copy_from_slice(&self.root);
        out[N..].copy_from_slice(&self.public_param);
        out
    }

    pub fn from_bytes(bytes: &[u8; PUB_KEY_SIZE]) -> Self {
        Self {
            root: bytes[..N].try_into().unwrap(),
            public_param: bytes[N..].try_into().unwrap(),
        }
    }
}

/// The seed, and the top tree key generation built from it, a cache and not
/// state: the signer reads the top key's path off it.
#[derive(Clone)]
pub struct LeanSphincsSecretKey {
    pub public_param: PublicParam,
    /// The key's seed, which the key serializes.
    seed: MasterSecret,
    /// [`scheme_seed`] of it, which every secret derives from.
    master: MasterSecret,
    /// The top tree's levels, its leaves first and its root last.
    top: Vec<Vec<Digest>>,
}

impl std::fmt::Debug for LeanSphincsSecretKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LeanSphincsSecretKey")
            .field("public_key", &self.public_key())
            .finish_non_exhaustive()
    }
}

impl LeanSphincsSecretKey {
    pub fn public_key(&self) -> LeanSphincsPublicKey {
        LeanSphincsPublicKey {
            root: self.top[LAYER_HEIGHTS[LAYERS - 1]][0],
            public_param: self.public_param,
        }
    }

    /// SECRET KEY MATERIAL: the seed, all of the key.
    pub fn to_bytes(&self) -> [u8; SECRET_KEY_SIZE] {
        self.seed
    }

    /// Regenerates the key, as key generation does.
    pub fn from_bytes(bytes: &[u8; SECRET_KEY_SIZE]) -> Self {
        key_gen_from_seed(*bytes).0
    }
}

/// What a signature carries for one layer: the one-time signature of what the
/// layer below gives. Its key's path is in [`LeanSphincsSignature::paths`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LayerSignature {
    pub counter: u32,
    pub wots: [Digest; V],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeanSphincsSignature {
    pub randomizer: Randomizer,
    pub fors: ForsOpening,
    /// Bottom first.
    pub layers: [LayerSignature; LAYERS],
    /// The layers' paths one after the other, bottom first ([`Self::path`]).
    pub paths: [Digest; H],
}

impl LeanSphincsSignature {
    /// Layer `layer`'s path in its tree, from the leaf up.
    pub fn path(&self, layer: usize) -> &[Digest] {
        let start: usize = LAYER_HEIGHTS[..layer].iter().sum();
        &self.paths[start..start + LAYER_HEIGHTS[layer]]
    }

    /// The specification's serialization, exactly [`SIG_SIZE`] bytes: the
    /// randomizer, the FORS openings, then each layer from the bottom up, its
    /// counter, chain values and path.
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
            put(&signed.counter.to_le_bytes());
            put(signed.wots.as_flattened());
            put(self.path(layer).as_flattened());
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
        let randomizer = take(RANDOMIZER_LEN).try_into().unwrap();
        let fors = std::array::from_fn(|_| ForsTreeOpening {
            secret: take(N).try_into().unwrap(),
            path: std::array::from_fn(|_| take(N).try_into().unwrap()),
        });
        let mut paths = [[0; N]; H];
        let mut start = 0;
        let layers = std::array::from_fn(|layer| {
            let signed = LayerSignature {
                counter: u32::from_le_bytes(take(COUNTER_LEN).try_into().unwrap()),
                wots: std::array::from_fn(|_| take(N).try_into().unwrap()),
            };
            for node in &mut paths[start..start + LAYER_HEIGHTS[layer]] {
                *node = take(N).try_into().unwrap();
            }
            start += LAYER_HEIGHTS[layer];
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LeanSphincsSignError {
    /// `C_max` counters in a row failed to encode, on this layer.
    NoAdmissibleEncoding(usize),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LeanSphincsVerifyError {
    /// The counter does not encode what the layer signs.
    InadmissibleEncoding(usize),
    RootMismatch,
}

impl std::fmt::Display for LeanSphincsSignError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoAdmissibleEncoding(layer) => {
                write!(f, "no admissible encoding within C_max attempts on layer {layer}")
            }
        }
    }
}

impl std::error::Error for LeanSphincsSignError {}

impl std::fmt::Display for LeanSphincsVerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InadmissibleEncoding(layer) => {
                write!(f, "the counter of layer {layer} does not encode what it signs")
            }
            Self::RootMismatch => write!(f, "the walk does not reach the key's root"),
        }
    }
}

impl std::error::Error for LeanSphincsVerifyError {}

/// The message digest, `D_0 | D_1` with `D_c = H(P | A_msg(c) | m | R)`, each
/// call one 80-byte block. `P` binds the key, so the root is not hashed.
pub fn message_digest_bytes(pp: &PublicParam, rho: &Randomizer, m: &Message) -> [u8; 32 * DIGEST_CALLS] {
    let mut out = [0; 32 * DIGEST_CALLS];
    for (c, chunk) in out.as_chunks_mut::<32>().0.iter_mut().enumerate() {
        *chunk = hasher(pp, &tweak(TWEAK_MSG, c as u32, 0))
            .update(m)
            .update(rho)
            .finalize();
    }
    out
}

/// The index and the FORS leaves a digest spells: read as one little-endian
/// number, its low `h` bits, then `a` bits per tree.
pub fn digest_fields(digest: &[u8; 32 * DIGEST_CALLS]) -> (u64, [usize; FORS_TREES]) {
    let field = |offset: usize, len: usize| {
        (0..len).fold(0u64, |value, bit| {
            let position = offset + bit;
            value | u64::from(digest[position / 8] >> (position % 8) & 1) << bit
        })
    };
    let leaves = std::array::from_fn(|c| field(H + c * FORS_HEIGHT, FORS_HEIGHT) as usize);
    (field(0, H), leaves)
}

/// The message digest read as the index and the FORS leaves.
pub fn message_digest(pp: &PublicParam, rho: &Randomizer, m: &Message) -> (u64, [usize; FORS_TREES]) {
    digest_fields(&message_digest_bytes(pp, rho, m))
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

/// A node and its sibling in index order: `bit` says the node is the right one.
pub(crate) fn ordered(bit: usize, node: Digest, sibling: Digest) -> [Digest; 2] {
    if bit & 1 == 0 { [node, sibling] } else { [sibling, node] }
}

/// Node `j` on `level` of a tree of the hypertree, from its two children.
fn node(pp: &PublicParam, key: &OtsKey, level: usize, j: usize, children: &[Digest; 2]) -> Digest {
    th_digests(
        pp,
        &tweak(TWEAK_NODE, level as u32, j as u32).at(key.layer, key.tree),
        children,
    )
}

/// The levels of the tree holding `key`, its leaves first and its root last.
fn tree_levels(pp: &PublicParam, seed: &MasterSecret, key: &OtsKey) -> Vec<Vec<Digest>> {
    let height = LAYER_HEIGHTS[key.layer];
    let leaves = parallel::map_collect(1 << height, |leaf| {
        wots_public_leaf(
            pp,
            seed,
            &OtsKey {
                leaf: leaf as u32,
                ..*key
            },
        )
    });
    merkle_levels(leaves, height, |level, j, pair| node(pp, key, level, j, pair))
}

/// `Gen`, deterministic: the seed's [`scheme_seed`] derives the public parameter,
/// and the top tree gives the root.
pub fn key_gen_from_seed(seed: MasterSecret) -> (LeanSphincsSecretKey, LeanSphincsPublicKey) {
    key_from_scheme_seed(seed, scheme_seed(&seed))
}

fn key_from_scheme_seed(seed: MasterSecret, master: MasterSecret) -> (LeanSphincsSecretKey, LeanSphincsPublicKey) {
    let public_param = public_param(&master);
    let top = tree_levels(&public_param, &master, &OtsKey::of_index(LAYERS - 1, 0));
    let sk = LeanSphincsSecretKey {
        public_param,
        seed,
        master,
        top,
    };
    let pk = sk.public_key();
    (sk, pk)
}

/// `Gen`, on a fresh seed from `rng`.
pub fn key_gen(rng: &mut impl CryptoRng) -> (LeanSphincsSecretKey, LeanSphincsPublicKey) {
    key_gen_from_seed(rng.random())
}

/// The randomizer of a message, `R = Th(P, A_rnd, S | m)` for the scheme seed
/// `S`, unpredictable without it. Every index is a leaf of the key, so the first one is kept.
pub fn randomizer(pp: &PublicParam, seed: &MasterSecret, m: &Message) -> Randomizer {
    let mut payload = [0u8; MASTER_SECRET_LEN + MESSAGE_LEN];
    payload[..MASTER_SECRET_LEN].copy_from_slice(seed);
    payload[MASTER_SECRET_LEN..].copy_from_slice(m);
    th(pp, &tweak(TWEAK_RANDOMIZER, 0, 0), &payload)
}

/// The bytes of a FORS key, the bottom one-time key's message.
pub fn fors_key_bytes(key: &ForsKey) -> &[u8] {
    key.as_flattened().as_flattened()
}

/// `Sign`. Deterministic and stateless: the digest picks the FORS instance,
/// which opens the message, and each layer signs what the layer below gives. A
/// key signs at most `2^30` messages (`doc/lean_sphincs`).
pub fn sign(sk: &LeanSphincsSecretKey, message: &Message) -> Result<LeanSphincsSignature, LeanSphincsSignError> {
    let (pp, seed) = (&sk.public_param, &sk.master);
    let rho = randomizer(pp, seed, message);
    let (idx, leaves) = message_digest(pp, &rho, message);
    let (fors_key, fors) = fors_open(pp, seed, idx as u32, &leaves);
    let mut signed = fors_key_bytes(&fors_key).to_vec();
    let mut layers = Vec::with_capacity(LAYERS);
    let (mut paths, mut start) = ([[0; N]; H], 0);
    for layer in 0..LAYERS {
        let key = OtsKey::of_index(layer, idx);
        let (counter, wots) =
            wots_sign(pp, seed, &key, &signed).ok_or(LeanSphincsSignError::NoAdmissibleEncoding(layer))?;
        let built;
        let levels = if layer == LAYERS - 1 {
            &sk.top
        } else {
            built = tree_levels(pp, seed, &key);
            &built
        };
        let height = LAYER_HEIGHTS[layer];
        for (level, node) in paths[start..start + height].iter_mut().enumerate() {
            *node = levels[level][(key.leaf as usize >> level) ^ 1];
        }
        start += height;
        layers.push(LayerSignature { counter, wots });
        signed = levels[height][0].to_vec();
    }
    Ok(LeanSphincsSignature {
        randomizer: rho,
        fors,
        layers: layers.try_into().unwrap(),
        paths,
    })
}

/// `Tree.fold`: the root a key's leaf and its path reach.
pub fn tree_fold(pp: &PublicParam, key: &OtsKey, leaf: Digest, path: &[Digest]) -> Digest {
    tree_fold_with(pp, key, leaf, path, |_| ())
}

/// [`tree_fold`], showing `visit` the two children of every node on the way up.
pub fn tree_fold_with(
    pp: &PublicParam,
    key: &OtsKey,
    leaf: Digest,
    path: &[Digest],
    mut visit: impl FnMut(&[Digest; 2]),
) -> Digest {
    let e = key.leaf as usize;
    path.iter().enumerate().fold(leaf, |current, (level, sibling)| {
        let children = ordered(e >> level, current, *sibling);
        visit(&children);
        node(pp, key, level + 1, e >> (level + 1), &children)
    })
}

/// `Ver`.
pub fn verify(
    pk: &LeanSphincsPublicKey,
    message: &Message,
    signature: &LeanSphincsSignature,
) -> Result<(), LeanSphincsVerifyError> {
    let pp = &pk.public_param;
    let (idx, leaves) = message_digest(pp, &signature.randomizer, message);
    let fors_key = fors_recover(pp, idx as u32, &leaves, &signature.fors);
    let mut signed = fors_key_bytes(&fors_key).to_vec();
    for (layer, layer_sig) in signature.layers.iter().enumerate() {
        let key = OtsKey::of_index(layer, idx);
        let (_, leaf) = wots_leaf(pp, &key, &signed, layer_sig.counter, &layer_sig.wots)
            .ok_or(LeanSphincsVerifyError::InadmissibleEncoding(layer))?;
        signed = tree_fold(pp, &key, leaf, signature.path(layer)).to_vec();
    }
    if signed == pk.root {
        Ok(())
    } else {
        Err(LeanSphincsVerifyError::RootMismatch)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A known answer, byte for byte, of everything below the tag: the key whose
    /// scheme seed is `S[i] = 37 i + 11` and its signature of `m[i] = 7 i + 3`.
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
        let master = std::array::from_fn(|i| (37 * i + 11) as u8);
        let (sk, pk) = key_from_scheme_seed(master, master);
        let message: Message = std::array::from_fn(|i| (7 * i + 3) as u8);
        assert_eq!(pk.flatten()[..], pk_bytes[..]);
        let signature = sign(&sk, &message).unwrap();
        assert_eq!(signature.to_bytes()[..], sig_bytes[..]);
        assert_eq!(verify(&pk, &message, &signature), Ok(()));
    }
}
