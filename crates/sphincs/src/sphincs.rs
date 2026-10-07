//! The tree, the message digest, and the three algorithms.
//!
//! An index derived from the message digest says which few-time key signs, and
//! with it which one-time key signs that few-time key. Nothing is reserved and
//! nothing is spent, which is what makes the scheme stateless.
//!
//! A pruned key keeps one subtree of height `b` and replaces the `h - b`
//! siblings above it by pseudorandom surrogate nodes; its signer grinds the
//! randomizer until the index lands in the kept subtree. A full key is the
//! pruned key with `b = h`. A verifier cannot tell them apart.

use rand::{CryptoRng, Rng};
use serde::{Deserialize, Serialize};

use crate::*;

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

/// The seed, and what key generation computed from it: the kept subtree and the
/// surrogates above it. Those are a cache and not state, a deterministic
/// function of the seed and of `b`.
#[derive(Clone, Debug)]
pub struct SphincsSecretKey {
    pub public_param: PublicParam,
    pub root: Digest,
    master: MasterSecret,
    /// `b`: the height of the kept subtree.
    b: usize,
    /// The kept subtree holds leaves `s 2^b .. (s + 1) 2^b`.
    s: u64,
    /// The kept subtree, level 0 being its `2^b` leaves.
    levels: Vec<Vec<Digest>>,
    /// The siblings of the path at levels `b..h`.
    surrogates: Vec<Digest>,
}

impl SphincsSecretKey {
    pub fn public_key(&self) -> SphincsPublicKey {
        SphincsPublicKey {
            root: self.root,
            public_param: self.public_param,
        }
    }

    /// SECRET KEY MATERIAL: with [`Self::kept_height`], all of the key.
    pub fn seed(&self) -> &MasterSecret {
        &self.master
    }

    pub fn kept_height(&self) -> usize {
        self.b
    }

    fn keeps(&self, idx: u64) -> bool {
        idx >> self.b == self.s
    }

    /// The authentication path of leaf `idx`, which the key keeps.
    fn path(&self, idx: u64) -> [Digest; H] {
        let local = (idx - (self.s << self.b)) as usize;
        std::array::from_fn(|level| {
            if level < self.b {
                self.levels[level][(local >> level) ^ 1]
            } else {
                self.surrogates[level - self.b]
            }
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SphincsSignature {
    pub randomizer: Randomizer,
    pub forest: ForestOpening,
    pub counter: u32,
    pub wots: [Digest; V],
    pub path: [Digest; H],
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
        for tree in &self.forest {
            for subtree in &tree.subtrees {
                put(subtree.values.as_flattened());
                put(subtree.path.as_flattened());
            }
            put(tree.path.as_flattened());
        }
        put(&self.counter.to_le_bytes());
        put(self.wots.as_flattened());
        put(self.path.as_flattened());
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
        let forest = std::array::from_fn(|_| TreeOpening {
            subtrees: std::array::from_fn(|_| SubtreeOpening {
                values: std::array::from_fn(|_| take(N).try_into().unwrap()),
                path: std::array::from_fn(|_| take(N).try_into().unwrap()),
            }),
            path: std::array::from_fn(|_| take(N).try_into().unwrap()),
        });
        let counter = u32::from_le_bytes(take(COUNTER_LEN).try_into().unwrap());
        let wots = std::array::from_fn(|_| take(N).try_into().unwrap());
        let path = std::array::from_fn(|_| take(N).try_into().unwrap());
        debug_assert_eq!(at, SIG_SIZE);
        Self {
            randomizer,
            forest,
            counter,
            wots,
            path,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SphincsSignError {
    /// `A_max` randomizers in a row missed the kept subtree.
    NoAdmissibleDigest,
    /// `C_max` counters in a row failed to encode.
    NoAdmissibleEncoding,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SphincsVerifyError {
    /// The counter does not encode the few-time key.
    InadmissibleEncoding,
    RootMismatch,
}

impl std::fmt::Display for SphincsSignError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoAdmissibleDigest => write!(f, "no message digest in the kept subtree within A_max attempts"),
            Self::NoAdmissibleEncoding => write!(f, "no admissible encoding within C_max attempts"),
        }
    }
}

impl std::error::Error for SphincsSignError {}

impl std::fmt::Display for SphincsVerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InadmissibleEncoding => write!(f, "the counter does not encode the few-time key"),
            Self::RootMismatch => write!(f, "the walk does not reach the key's root"),
        }
    }
}

impl std::error::Error for SphincsVerifyError {}

/// The index and the trees' marks a digest spells. Its fields are grouped by
/// kind, so that none lies across two 64-bit words: first one byte per subtree,
/// its codeword, then little-endian bit fields, the `h` bits of index, each
/// tree's leaf, and each subtree's WOTS key.
fn marks_of(digest: &[u8; 32]) -> (u64, [Mark; FOREST_TREES]) {
    let field = |offset: usize, len: usize| {
        (0..len).fold(0usize, |value, bit| {
            let position = 8 * DIGEST_WORD_BYTES + offset + bit;
            value | (usize::from(digest[position / 8] >> (position % 8) & 1) << bit)
        })
    };
    let keys = H + FOREST_TREES * TREE_HEIGHT;
    let marks = std::array::from_fn(|c| Mark {
        leaf: field(H + c * TREE_HEIGHT, TREE_HEIGHT),
        keys: std::array::from_fn(|j| field(keys + (SUBTREES * c + j) * SUBTREE_HEIGHT, SUBTREE_HEIGHT)),
        words: std::array::from_fn(|j| usize::from(digest[SUBTREES * c + j])),
    });
    (field(0, H) as u64, marks)
}

/// The message digest, `BLAKE2s(P | A | m | rho)`, read as the index and the
/// trees' marks. `P` binds the key, so the root is not hashed, and the message
/// ends the first block: a signer grinding `rho` hashes it once.
pub fn message_digest(pp: &PublicParam, rho: &Randomizer, m: &Message) -> (u64, [Mark; FOREST_TREES]) {
    marks_of(&digest_prefix(pp, m).update(rho).finalize())
}

fn digest_prefix(pp: &PublicParam, m: &Message) -> primitives::hash::Hasher {
    let mut prefix = hasher(pp, &tweak(TWEAK_MSG, 0, 0));
    prefix.update(m);
    prefix
}

fn node(pp: &PublicParam, level: usize, j: u64, children: &[Digest; 2]) -> Digest {
    th_digests(pp, &tweak(TWEAK_NODE, level as u32, j as u32), children)
}

/// `Gen`, deterministic: the seed derives the public parameter, whose low bits
/// place the kept subtree of height `b <= h`, and the surrogates above it.
pub fn key_gen_from_seed(seed: MasterSecret, b: usize) -> (SphincsSecretKey, SphincsPublicKey) {
    assert!(b <= H, "a key keeps at most the whole tree");
    let public_param = th(&[0; PUBLIC_PARAM_LEN], &tweak(TWEAK_PARAMETER, 0, 0), &seed);
    let s = u64::from_le_bytes(public_param[..8].try_into().unwrap()) & ((1 << (H - b)) - 1);
    let leaves = parallel::map_collect(1 << b, |j| {
        wots_public_leaf(&public_param, &seed, ((s << b) + j as u64) as u32)
    });
    let mut levels = vec![leaves];
    for level in 1..=b {
        let first = s << (b - level);
        let (pairs, _) = levels[level - 1].as_chunks::<2>();
        let up = pairs
            .iter()
            .enumerate()
            .map(|(j, pair)| node(&public_param, level, first + j as u64, pair))
            .collect();
        levels.push(up);
    }
    let surrogates: Vec<Digest> = (b..H)
        .map(|level| th(&public_param, &tweak(TWEAK_SURROGATE, level as u32, 0), &seed))
        .collect();
    let root = surrogates
        .iter()
        .enumerate()
        .fold(levels[b][0], |current, (t, sibling)| {
            let j = s >> t;
            let children = if j & 1 == 0 {
                [current, *sibling]
            } else {
                [*sibling, current]
            };
            node(&public_param, b + t + 1, j >> 1, &children)
        });
    let sk = SphincsSecretKey {
        public_param,
        root,
        master: seed,
        b,
        s,
        levels,
        surrogates,
    };
    let pk = sk.public_key();
    (sk, pk)
}

/// `Gen`, on a fresh key keeping a subtree of height `b`: the seed comes from
/// `rng`, so nothing can regenerate the key.
pub fn key_gen(rng: &mut impl CryptoRng, b: usize) -> (SphincsSecretKey, SphincsPublicKey) {
    key_gen_from_seed(rng.random(), b)
}

/// `Sign`. Deterministic and stateless: the randomizer is the first of
/// `R_0 + i`, `R_0` a hash of the seed and the message, whose index lands in the
/// kept subtree. How many messages a key may sign depends on `b` (`doc/sphincs`).
pub fn sign(sk: &SphincsSecretKey, message: &Message) -> Result<SphincsSignature, SphincsSignError> {
    let pp = &sk.public_param;
    let mut payload = [0u8; MASTER_SECRET_LEN + MESSAGE_LEN];
    payload[..MASTER_SECRET_LEN].copy_from_slice(&sk.master);
    payload[MASTER_SECRET_LEN..].copy_from_slice(message);
    let base = u128::from_le_bytes(th(pp, &tweak(TWEAK_RANDOMIZER, 0, 0), &payload));
    let prefix = digest_prefix(pp, message);
    let (randomizer, idx, marks) = (0..MAX_DIGEST_ATTEMPTS)
        .find_map(|i| {
            let randomizer = base.wrapping_add(u128::from(i)).to_le_bytes();
            let (idx, marks) = marks_of(&prefix.clone().update(&randomizer).finalize());
            sk.keeps(idx).then_some((randomizer, idx, marks))
        })
        .ok_or(SphincsSignError::NoAdmissibleDigest)?;

    let (forest_key, forest) = forest_open(pp, &sk.master, idx as u32, &marks);
    let (counter, wots) =
        wots_sign(pp, &sk.master, idx as u32, &forest_key).ok_or(SphincsSignError::NoAdmissibleEncoding)?;
    Ok(SphincsSignature {
        randomizer,
        forest,
        counter,
        wots,
        path: sk.path(idx),
    })
}

/// `Tree.fold`: the root a leaf and its path reach.
pub fn tree_fold(pp: &PublicParam, idx: u64, leaf: Digest, path: &[Digest; H]) -> Digest {
    tree_fold_with(pp, idx, leaf, path, |_| ())
}

/// [`tree_fold`], showing `visit` the two children of every node on the way up.
pub fn tree_fold_with(
    pp: &PublicParam,
    idx: u64,
    leaf: Digest,
    path: &[Digest; H],
    mut visit: impl FnMut(&[Digest; 2]),
) -> Digest {
    path.iter().enumerate().fold(leaf, |current, (level, sibling)| {
        let children = if (idx >> level) & 1 == 0 {
            [current, *sibling]
        } else {
            [*sibling, current]
        };
        visit(&children);
        node(pp, level + 1, idx >> (level + 1), &children)
    })
}

/// `Ver`.
pub fn verify(
    pk: &SphincsPublicKey,
    message: &Message,
    signature: &SphincsSignature,
) -> Result<(), SphincsVerifyError> {
    let pp = &pk.public_param;
    let (idx, marks) = message_digest(pp, &signature.randomizer, message);
    let forest_key = forest_recover(pp, idx as u32, &marks, &signature.forest);
    let leaf = wots_leaf(pp, idx as u32, &forest_key, signature.counter, &signature.wots)
        .ok_or(SphincsVerifyError::InadmissibleEncoding)?;
    if tree_fold(pp, idx, leaf, &signature.path) == pk.root {
        Ok(())
    } else {
        Err(SphincsVerifyError::RootMismatch)
    }
}
