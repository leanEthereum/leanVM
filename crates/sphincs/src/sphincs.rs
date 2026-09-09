//! The hypertree and the three algorithms: `d` layers of Merkle trees over
//! one-time leaves, the bottom layer signing few-time keys, layer 0's root being
//! the public key.
//!
//! An index derived from the message digest says which few-time key signs, and
//! with it which tree and which leaf are used on every layer. Nothing is
//! reserved and nothing is spent: a key answers for all `2^h` indices, which is
//! what makes the scheme stateless.

use rand::{CryptoRng, Rng};
use serde::{Deserialize, Serialize};

use crate::*;

/// `SUFFIX[lay] = sum_{j >= lay} h_j`, the height of everything at or below
/// layer `lay`: the divisors of the index decomposition.
const fn suffix_heights() -> [usize; D + 1] {
    let mut suffix = [0; D + 1];
    let mut lay = D;
    while lay > 0 {
        lay -= 1;
        suffix[lay] = suffix[lay + 1] + HEIGHTS[lay];
    }
    suffix
}
pub const SUFFIX: [usize; D + 1] = suffix_heights();
const _: () = assert!(SUFFIX[0] == H);

/// The layer-0 depth whose nodes a signer caches, halfway up so that the subtree
/// to rebuild and the nodes to refold are both `2^(h_0/2)`.
pub const SPLIT_LEVEL: usize = HEIGHTS[0].div_ceil(2);
pub const CACHE_LEN: usize = 1 << (HEIGHTS[0] - SPLIT_LEVEL);
const _: () = assert!(CACHE_LEN * N == 1024);

/// `tau_lay(idx)`: the tree used on layer `lay`.
pub fn tree_of(idx: u64, lay: usize) -> u32 {
    (idx >> SUFFIX[lay]) as u32
}

/// `e_lay(idx)`: the leaf used within that tree.
pub fn leaf_of(idx: u64, lay: usize) -> u32 {
    ((idx >> SUFFIX[lay + 1]) & ((1 << HEIGHTS[lay]) - 1)) as u32
}

/// Where layer `lay`'s siblings sit in a signature's flat path.
pub fn path_range(lay: usize) -> std::ops::Range<usize> {
    let start: usize = HEIGHTS[..lay].iter().sum();
    start..start + HEIGHTS[lay]
}

/// Ordered lexicographically on [`Self::flatten`], which is what an aggregate's
/// signer list is sorted and deduplicated by.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SphincsPublicKey {
    pub root: Digest,
    pub public_param: PublicParam,
}

impl SphincsPublicKey {
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

/// `P`, the root, and the master secret every secret is derived from, plus
/// layer 0's nodes at [`SPLIT_LEVEL`]. Those nodes are a cache and not state: a
/// deterministic function of the master secret, so losing them costs
/// recomputation and nothing else.
#[derive(Clone, Debug)]
pub struct SphincsSecretKey {
    pub public_param: PublicParam,
    pub root: Digest,
    master: Digest,
    cache: [Digest; CACHE_LEN],
}

impl SphincsSecretKey {
    /// SECRET KEY MATERIAL: public parameter and master secret.
    pub fn to_bytes(&self) -> [u8; SECRET_KEY_SIZE] {
        let mut out = [0; SECRET_KEY_SIZE];
        out[..PUBLIC_PARAM_LEN].copy_from_slice(&self.public_param);
        out[PUBLIC_PARAM_LEN..].copy_from_slice(&self.master);
        out
    }

    /// Inverse of [`Self::to_bytes`], costing what [`key_gen_from`] costs: the
    /// layer-0 tree is rebuilt rather than stored.
    pub fn from_bytes(bytes: &[u8; SECRET_KEY_SIZE]) -> Self {
        let (public_param, master) = bytes.split_at(PUBLIC_PARAM_LEN);
        key_gen_from(public_param.try_into().unwrap(), master.try_into().unwrap()).0
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SphincsSignature {
    pub randomizer: Randomizer,
    pub fts: FtsOpening,
    pub counters: [u32; D],
    pub ots: [[Digest; V]; D],
    /// Layer 0's `h_0` siblings, then layer 1's, then layer 2's.
    pub paths: [Digest; H],
}

impl SphincsSignature {
    /// The specification's serialization, exactly [`SIG_SIZE`] bytes.
    pub fn to_bytes(&self) -> [u8; SIG_SIZE] {
        let mut out = [0; SIG_SIZE];
        let mut at = 0;
        let mut put = |bytes: &[u8]| {
            out[at..at + bytes.len()].copy_from_slice(bytes);
            at += bytes.len();
        };
        put(&self.randomizer);
        for kappa in 0..NUM_FTS_TREES {
            put(&self.fts.secrets[kappa]);
            for sibling in &self.fts.paths[kappa] {
                put(sibling);
            }
        }
        for lay in 0..D {
            put(&self.counters[lay].to_le_bytes());
            for value in &self.ots[lay] {
                put(value);
            }
            for sibling in &self.paths[path_range(lay)] {
                put(sibling);
            }
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
        let mut fts = FtsOpening {
            secrets: [[0; N]; NUM_FTS_TREES],
            paths: [[[0; N]; A]; NUM_FTS_TREES],
        };
        for kappa in 0..NUM_FTS_TREES {
            fts.secrets[kappa] = take(N).try_into().unwrap();
            for level in 0..A {
                fts.paths[kappa][level] = take(N).try_into().unwrap();
            }
        }
        let mut counters = [0; D];
        let mut ots = [[[0; N]; V]; D];
        let mut paths = [[0; N]; H];
        for lay in 0..D {
            counters[lay] = u32::from_le_bytes(take(COUNTER_LEN).try_into().unwrap());
            for i in 0..V {
                ots[lay][i] = take(N).try_into().unwrap();
            }
            for level in path_range(lay) {
                paths[level] = take(N).try_into().unwrap();
            }
        }
        debug_assert_eq!(at, SIG_SIZE);
        Self {
            randomizer,
            fts,
            counters,
            ots,
            paths,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SphincsSignError {
    /// `A_max` digests in a row had a nonzero last index.
    NoAdmissibleDigest,
    /// `C_max` counters in a row failed to encode.
    NoAdmissibleEncoding,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SphincsVerifyError {
    /// The digest's last index is not zero.
    InadmissibleDigest,
    /// A layer's counter does not encode the message it signs.
    InadmissibleEncoding,
    RootMismatch,
}

impl std::fmt::Display for SphincsSignError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoAdmissibleDigest => write!(f, "no admissible message digest within A_max attempts"),
            Self::NoAdmissibleEncoding => write!(f, "no admissible encoding within C_max attempts"),
        }
    }
}

impl std::error::Error for SphincsSignError {}

impl std::fmt::Display for SphincsVerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InadmissibleDigest => write!(f, "the digest's last index is not zero"),
            Self::InadmissibleEncoding => write!(f, "a layer's counter does not encode the message it signs"),
            Self::RootMismatch => write!(f, "the hypertree walk does not reach the key's root"),
        }
    }
}

impl std::error::Error for SphincsVerifyError {}

/// The message digest, read as the index and the `k` leaf indices. `h + ka` bits
/// of a random oracle output, so the index and the last leaf index are disjoint
/// and grinding one does not bias the other.
pub fn message_digest(pp: &PublicParam, root: &Digest, rho: &Randomizer, m: &Message) -> (u64, [u32; K]) {
    let mut hasher = primitives::hash::Hasher::new();
    hasher
        .update(&tweak(TWEAK_MSG, 0, 0, 0, 0))
        .update(pp)
        .update(rho)
        .update(root)
        .update(m);
    let digest = &hasher.finalize()[..DIGEST_BYTES];
    let field = |offset: usize, len: usize| {
        (0..len).fold(0u64, |value, bit| {
            let position = offset + bit;
            value | (u64::from(digest[position / 8] >> (position % 8) & 1) << bit)
        })
    };
    (field(0, H), std::array::from_fn(|kappa| field(H + kappa * A, A) as u32))
}

fn node(pp: &PublicParam, lay: usize, tau: u32, level: usize, j: u64, left: &Digest, right: &Digest) -> Digest {
    let tw = tweak(TWEAK_NODE, lay, tau, level as u32, j as u32);
    th_digests(pp, &tw, &[*left, *right])
}

/// Merkle levels `from_level..=to_level` of layer `lay`'s tree `tau`, given
/// `bottom`, the complete band of level-`from_level` nodes starting at index
/// `first`. Level `l` is `layers[l - from_level]`.
fn build_up(
    pp: &PublicParam,
    lay: usize,
    tau: u32,
    bottom: Vec<Digest>,
    from_level: usize,
    to_level: usize,
    first: u64,
) -> Vec<Vec<Digest>> {
    let mut layers = vec![bottom];
    for level in from_level + 1..=to_level {
        let base = first >> (level - from_level);
        let children = layers.last().unwrap();
        layers.push(
            (0..children.len() / 2)
                .map(|j| {
                    node(
                        pp,
                        lay,
                        tau,
                        level,
                        base + j as u64,
                        &children[2 * j],
                        &children[2 * j + 1],
                    )
                })
                .collect(),
        );
    }
    layers
}

/// `Gen`, on given `P` and master secret. Only layer 0 is built; the trees below
/// it are built when a signature needs them.
pub fn key_gen_from(public_param: PublicParam, master: Digest) -> (SphincsSecretKey, SphincsPublicKey) {
    let leaves = parallel::map_collect(1 << HEIGHTS[0], |e| {
        ots_public_leaf(&public_param, &master, Pos::new(0, 0, e as u32))
    });
    let layers = build_up(&public_param, 0, 0, leaves, 0, HEIGHTS[0], 0);
    let root = layers[HEIGHTS[0]][0];
    let cache = std::array::from_fn(|i| layers[SPLIT_LEVEL][i]);
    (
        SphincsSecretKey {
            public_param,
            root,
            master,
            cache,
        },
        SphincsPublicKey { root, public_param },
    )
}

/// The domain string the seed is expanded under, so a seed shared with
/// `xmss::key_gen_from_seed` gives unrelated keys.
const KEY_GEN_DOMAINSEP: &[u8] = b"sphincs/key-gen/v1";

/// `Gen`, on a fresh key: the seed comes from `rng`, so nothing can regenerate
/// the key.
pub fn key_gen(rng: &mut impl CryptoRng) -> (SphincsSecretKey, SphincsPublicKey) {
    key_gen_from_seed(rng.random())
}

/// Deterministic [`key_gen`]: one seed always regenerates the same key pair.
/// `P` and the master secret are the two halves of a keyed hash of it, which is
/// uniform and independent in the random-oracle model the spec's sampling is
/// stated in (`doc/sphincs` Remark "Seed derivation").
pub fn key_gen_from_seed(seed: [u8; 32]) -> (SphincsSecretKey, SphincsPublicKey) {
    const _: () = assert!(PUBLIC_PARAM_LEN + N == primitives::hash::OUT_LEN);
    let expanded = primitives::hash::keyed_hash(&seed, KEY_GEN_DOMAINSEP);
    key_gen_from(
        expanded[..PUBLIC_PARAM_LEN].try_into().unwrap(),
        expanded[PUBLIC_PARAM_LEN..].try_into().unwrap(),
    )
}

impl SphincsSecretKey {
    pub fn public_key(&self) -> SphincsPublicKey {
        SphincsPublicKey {
            root: self.root,
            public_param: self.public_param,
        }
    }

    /// Layer `lay`'s tree `tau` rebuilt whole: the siblings at `e` into `path`,
    /// and the root.
    fn tree_path_and_root(&self, lay: usize, tau: u32, e: u32, path: &mut [Digest]) -> Digest {
        debug_assert_eq!(path.len(), HEIGHTS[lay]);
        let leaves = (0..1 << HEIGHTS[lay])
            .map(|leaf| ots_public_leaf(&self.public_param, &self.master, Pos::new(lay, tau, leaf)))
            .collect();
        let layers = build_up(&self.public_param, lay, tau, leaves, 0, HEIGHTS[lay], 0);
        for (level, sibling) in path.iter_mut().enumerate() {
            *sibling = layers[level][((e >> level) ^ 1) as usize];
        }
        layers[HEIGHTS[lay]][0]
    }

    /// Layer 0's siblings at `e`, from the cache: one `2^SPLIT_LEVEL`-leaf
    /// subtree rebuilt below it, the cached nodes refolded above it. Returns the
    /// root, which the cache reproduces.
    fn cached_path_and_root(&self, e: u32, path: &mut [Digest]) -> Digest {
        debug_assert_eq!(path.len(), HEIGHTS[0]);
        let first = u64::from(e >> SPLIT_LEVEL) << SPLIT_LEVEL;
        let leaves = (first..first + (1 << SPLIT_LEVEL))
            .map(|leaf| ots_public_leaf(&self.public_param, &self.master, Pos::new(0, 0, leaf as u32)))
            .collect();
        let below = build_up(&self.public_param, 0, 0, leaves, 0, SPLIT_LEVEL, first);
        let above = build_up(
            &self.public_param,
            0,
            0,
            self.cache.to_vec(),
            SPLIT_LEVEL,
            HEIGHTS[0],
            0,
        );
        debug_assert_eq!(below[SPLIT_LEVEL][0], self.cache[(first >> SPLIT_LEVEL) as usize]);
        for (level, sibling) in path.iter_mut().enumerate() {
            let index = u64::from(e >> level) ^ 1;
            *sibling = if level < SPLIT_LEVEL {
                below[level][(index - (first >> level)) as usize]
            } else {
                above[level - SPLIT_LEVEL][index as usize]
            };
        }
        above[HEIGHTS[0] - SPLIT_LEVEL][0]
    }
}

/// `Sig`. Stateless: it may be called on any message any number of times, but
/// security degrades with that number, the specification's claim being stated at
/// `2^24` signatures per key pair.
pub fn sign(
    rng: &mut impl CryptoRng,
    sk: &SphincsSecretKey,
    message: &Message,
) -> Result<SphincsSignature, SphincsSignError> {
    // The digest is admissible when its last leaf index is zero, which is what
    // drops that tree from the forest; it takes 2^a attempts on average.
    let (randomizer, idx, u) = (0..MAX_DIGEST_ATTEMPTS)
        .find_map(|_| {
            let randomizer: Randomizer = rng.random();
            let (idx, u) = message_digest(&sk.public_param, &sk.root, &randomizer, message);
            (u[K - 1] == 0).then_some((randomizer, idx, u))
        })
        .ok_or(SphincsSignError::NoAdmissibleDigest)?;

    let (fts_key, fts) = fts_open(&sk.public_param, &sk.master, idx, &u);

    let mut message_of_layer = fts_key;
    let mut counters = [0; D];
    let mut ots = [[[0; N]; V]; D];
    let mut paths = [[0; N]; H];
    for lay in (0..D).rev() {
        let (tau, e) = (tree_of(idx, lay), leaf_of(idx, lay));
        let pos = Pos::new(lay, tau, e);
        let (c, signature) = ots_sign(&sk.public_param, &sk.master, pos, &message_of_layer)
            .ok_or(SphincsSignError::NoAdmissibleEncoding)?;
        counters[lay] = c;
        ots[lay] = signature;
        let path = &mut paths[path_range(lay)];
        message_of_layer = if lay == 0 {
            sk.cached_path_and_root(e, path)
        } else {
            sk.tree_path_and_root(lay, tau, e, path)
        };
    }
    // Layer 0's root is discarded: it is the public key's whenever the signer is
    // honest, which is also the only check the cache gets.
    debug_assert_eq!(message_of_layer, sk.root);

    Ok(SphincsSignature {
        randomizer,
        fts,
        counters,
        ots,
        paths,
    })
}

/// `Tree.fold`: the other half of a Merkle opening.
pub fn tree_fold(pp: &PublicParam, pos: Pos, leaf: Digest, path: &[Digest]) -> Digest {
    path.iter().enumerate().fold(leaf, |current, (level, sibling)| {
        let (left, right) = if (pos.e >> level) & 1 == 0 {
            (current, *sibling)
        } else {
            (*sibling, current)
        };
        node(
            pp,
            pos.lay,
            pos.tau,
            level + 1,
            u64::from(pos.e >> (level + 1)),
            &left,
            &right,
        )
    })
}

/// `Ver`.
pub fn verify(
    pk: &SphincsPublicKey,
    message: &Message,
    signature: &SphincsSignature,
) -> Result<(), SphincsVerifyError> {
    let (idx, u) = message_digest(&pk.public_param, &pk.root, &signature.randomizer, message);
    if u[K - 1] != 0 {
        return Err(SphincsVerifyError::InadmissibleDigest);
    }
    let mut message_of_layer = fts_recover(&pk.public_param, idx, &u, &signature.fts);
    for lay in (0..D).rev() {
        let pos = Pos::new(lay, tree_of(idx, lay), leaf_of(idx, lay));
        let leaf = ots_leaf(
            &pk.public_param,
            pos,
            &message_of_layer,
            signature.counters[lay],
            &signature.ots[lay],
        )
        .ok_or(SphincsVerifyError::InadmissibleEncoding)?;
        message_of_layer = tree_fold(&pk.public_param, pos, leaf, &signature.paths[path_range(lay)]);
    }
    if message_of_layer == pk.root {
        Ok(())
    } else {
        Err(SphincsVerifyError::RootMismatch)
    }
}
