//! The hypertree, the message digest, and the three algorithms.
//!
//! The message digest picks a bottom leaf `idx`, and so a FORS instance and the
//! one-time key on every layer above it. Nothing is reserved and nothing is
//! spent, which is what makes the scheme stateless. The bottom key signs the
//! FORS key, the middle key the bottom tree's root, the top key the middle
//! tree's root, and the top tree's root is the public key.

use serde::{Deserialize, Serialize};

use crate::lean_sphincs::*;

/// Ordered lexicographically on [`Self::to_bytes`], which is what an aggregate's
/// signer list is sorted and deduplicated by.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct LeanSphincsPublicKey {
    pub(crate) root: Digest,
    pub(crate) public_param: PublicParam,
}

impl LeanSphincsPublicKey {
    pub fn public_param(&self) -> &PublicParam {
        &self.public_param
    }

    pub fn to_bytes(&self) -> [u8; PUB_KEY_SIZE] {
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

/// The key's seed, all of the key: its [`scheme_seed`] derives every secret.
#[derive(Clone)]
pub struct LeanSphincsSecretKey {
    seed: Seed,
}

impl std::fmt::Debug for LeanSphincsSecretKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LeanSphincsSecretKey").finish_non_exhaustive()
    }
}

impl LeanSphincsSecretKey {
    /// The public key, rebuilt as key generation builds it: the whole top tree.
    pub fn public_key(&self) -> LeanSphincsPublicKey {
        public_key_of(&scheme_seed(&self.seed))
    }

    /// SECRET KEY MATERIAL: the seed, all of the key.
    pub fn to_bytes(&self) -> Seed {
        self.seed
    }

    pub fn from_bytes(bytes: &Seed) -> Self {
        Self { seed: *bytes }
    }
}

/// What a signature carries for one layer: the one-time signature of what the
/// layer below gives. Its key's path is [`LeanSphincsSignature::path`].
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
    pub(crate) randomizer: Randomizer,
    pub(crate) fors: ForsOpening,
    /// Bottom first.
    pub(crate) layers: [LayerSignature; LAYERS],
    /// The layers' paths one after the other, bottom first ([`Self::path`]).
    pub(crate) paths: [Digest; H],
}

impl LeanSphincsSignature {
    pub fn randomizer(&self) -> &Randomizer {
        &self.randomizer
    }

    pub fn fors(&self) -> &ForsOpening {
        &self.fors
    }

    /// Bottom first.
    pub fn layers(&self) -> &[LayerSignature; LAYERS] {
        &self.layers
    }

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
        let mut paths = Vec::with_capacity(H);
        let layers = std::array::from_fn(|layer| {
            let signed = LayerSignature {
                counter: u32::from_le_bytes(take(COUNTER_LEN).try_into().unwrap()),
                wots: std::array::from_fn(|_| take(N).try_into().unwrap()),
            };
            paths.extend((0..LAYER_HEIGHTS[layer]).map(|_| Digest::try_from(take(N)).unwrap()));
            signed
        });
        debug_assert_eq!(at, SIG_SIZE);
        Self {
            randomizer,
            fors,
            layers,
            paths: paths.try_into().unwrap(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LeanSphincsSignError {
    /// `C_max` counters in a row failed to encode.
    NoAdmissibleEncoding,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LeanSphincsVerifyError {
    /// A counter does not encode what its layer signs.
    InadmissibleEncoding,
    RootMismatch,
}

impl std::fmt::Display for LeanSphincsSignError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoAdmissibleEncoding => write!(f, "no admissible encoding within C_max attempts"),
        }
    }
}

impl std::error::Error for LeanSphincsSignError {}

impl std::fmt::Display for LeanSphincsVerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InadmissibleEncoding => write!(f, "a counter does not encode what its layer signs"),
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
pub fn digest_fields(digest: &[u8; 32 * DIGEST_CALLS]) -> (u32, [usize; FORS_TREES]) {
    let field = |offset: usize, len: usize| {
        (0..len).fold(0, |value, bit| {
            let position = offset + bit;
            value | usize::from(digest[position / 8] >> (position % 8) & 1) << bit
        })
    };
    let leaves = std::array::from_fn(|c| field(H + c * FORS_HEIGHT, FORS_HEIGHT));
    (field(0, H) as u32, leaves)
}

/// The message digest read as the index and the FORS leaves.
pub fn message_digest(pp: &PublicParam, rho: &Randomizer, m: &Message) -> (u32, [usize; FORS_TREES]) {
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
fn tree_levels(pp: &PublicParam, seed: &SchemeSeed, key: &OtsKey) -> Vec<Vec<Digest>> {
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
pub fn key_gen_from_seed(seed: Seed) -> (LeanSphincsSecretKey, LeanSphincsPublicKey) {
    (LeanSphincsSecretKey { seed }, public_key_of(&scheme_seed(&seed)))
}

/// The public key of the scheme seed `seed`: its public parameter and the top
/// tree's root.
fn public_key_of(seed: &SchemeSeed) -> LeanSphincsPublicKey {
    let public_param = public_param(seed);
    let top = tree_levels(&public_param, seed, &OtsKey::of_index(LAYERS - 1, 0));
    LeanSphincsPublicKey {
        root: top[LAYER_HEIGHTS[LAYERS - 1]][0],
        public_param,
    }
}

/// `Gen`, on a fresh seed from the operating system's randomness.
pub fn key_gen() -> (LeanSphincsSecretKey, LeanSphincsPublicKey) {
    key_gen_from_seed(rand::random())
}

/// The randomizer of a message, `R = Th(P, A_rnd, S | m)` for the scheme seed
/// `S`, unpredictable without it.
pub fn randomizer(pp: &PublicParam, seed: &SchemeSeed, m: &Message) -> Randomizer {
    th(
        pp,
        &tweak(TWEAK_RANDOMIZER, 0, 0),
        [*seed.as_bytes(), *m].as_flattened(),
    )
}

/// The bytes of a FORS key, the bottom one-time key's message.
pub fn fors_key_bytes(key: &ForsKey) -> &[u8] {
    key.as_flattened().as_flattened()
}

/// `Sign`. Deterministic and stateless: the digest picks the FORS instance,
/// which opens the message, and each layer signs what the layer below gives. A
/// key signs at most `2^30` messages (`doc/lean_sphincs`). It builds its trees on
/// `parallel`, so never sign from inside a `parallel` task.
pub fn sign(sk: &LeanSphincsSecretKey, message: &Message) -> Result<LeanSphincsSignature, LeanSphincsSignError> {
    sign_with(&scheme_seed(&sk.seed), message)
}

/// [`sign`] with the scheme seed `seed`. It builds the FORS instance and the
/// three trees on the way up.
fn sign_with(seed: &SchemeSeed, message: &Message) -> Result<LeanSphincsSignature, LeanSphincsSignError> {
    let pp = &public_param(seed);
    let rho = randomizer(pp, seed, message);
    let (idx, leaves) = message_digest(pp, &rho, message);
    let (fors_key, fors) = fors_open(pp, seed, idx, &leaves);
    let mut signed = fors_key_bytes(&fors_key).to_vec();
    let (mut layers, mut paths) = (Vec::with_capacity(LAYERS), Vec::with_capacity(H));
    for layer in 0..LAYERS {
        let key = OtsKey::of_index(layer, idx);
        let (counter, wots) = wots_sign(pp, seed, &key, &signed).ok_or(LeanSphincsSignError::NoAdmissibleEncoding)?;
        let levels = tree_levels(pp, seed, &key);
        let height = LAYER_HEIGHTS[layer];
        paths.extend((0..height).map(|level| levels[level][(key.leaf as usize >> level) ^ 1]));
        layers.push(LayerSignature { counter, wots });
        signed = levels[height][0].to_vec();
    }
    Ok(LeanSphincsSignature {
        randomizer: rho,
        fors,
        layers: layers.try_into().unwrap(),
        paths: paths.try_into().unwrap(),
    })
}

/// `Tree.fold`: the root a key's leaf and its path reach, showing `visit` the two
/// children of every node on the way up.
pub fn tree_fold(
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
    let fors_key = fors_recover(pp, idx, &leaves, &signature.fors, |_| ());
    let mut signed = fors_key_bytes(&fors_key).to_vec();
    for (layer, layer_sig) in signature.layers.iter().enumerate() {
        let key = OtsKey::of_index(layer, idx);
        let (_, leaf) = wots_leaf(pp, &key, &signed, layer_sig.counter, &layer_sig.wots)
            .ok_or(LeanSphincsVerifyError::InadmissibleEncoding)?;
        signed = tree_fold(pp, &key, leaf, signature.path(layer), |_| ()).to_vec();
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
        let master = SchemeSeed(std::array::from_fn(|i| (37 * i + 11) as u8));
        let pk = public_key_of(&master);
        let message: Message = std::array::from_fn(|i| (7 * i + 3) as u8);
        assert_eq!(pk.to_bytes()[..], pk_bytes[..]);
        let signature = sign_with(&master, &message).unwrap();
        assert_eq!(signature.to_bytes()[..], sig_bytes[..]);
        assert_eq!(verify(&pk, &message, &signature), Ok(()));
    }
}
