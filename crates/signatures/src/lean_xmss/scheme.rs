//! Keys, signing and verification. The secret key holds the top tree and builds
//! a bottom tree, with the top layer's signature of its root, the first time it
//! signs in it, keeping the last one.

use std::ops::RangeInclusive;
use std::sync::{Arc, Mutex};

use rand::{CryptoRng, Rng};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::lean_xmss::*;

/// Ordered lexicographically on `flatten()`, which is what an aggregate's claims are
/// sorted by.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LeanXmssPublicKey {
    pub merkle_root: Digest,
    pub public_param: PublicParam,
}

impl LeanXmssPublicKey {
    pub fn flatten(&self) -> [u8; PUB_KEY_SIZE] {
        let mut out = [0u8; PUB_KEY_SIZE];
        out[..N].copy_from_slice(&self.merkle_root);
        out[N..].copy_from_slice(&self.public_param);
        out
    }
}

/// One layer's signature: the randomizer, the value each digit opens, and the
/// authentication path.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct LayerSignature {
    pub randomizer: Randomizer,
    #[serde(with = "crate::lean_xmss::array_serialization")]
    pub chain_values: [Digest; V],
    pub path: [Digest; LAYER_HEIGHT],
}

/// Carries the leaf index it was made at, so a verifier needs only the key and the
/// message. The top layer's signature is the same for every leaf of a bottom tree.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct LeanXmssSignature {
    pub leaf_index: LeafIndex,
    pub bottom: LayerSignature,
    pub top: LayerSignature,
}

pub struct LeanXmssSecretKey {
    /// The key's seed, which the key serializes.
    key_seed: Seed,
    /// [`scheme_seed`] of it, which every secret derives from.
    seed: Seed,
    public_param: PublicParam,
    top: LayerTree,
    /// The bottom tree the key last signed in.
    bottom: Mutex<Option<Arc<BottomTree>>>,
}

impl std::fmt::Debug for LeanXmssSecretKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LeanXmssSecretKey")
            .field("public_key", &self.public_key())
            .finish_non_exhaustive()
    }
}

/// SECRET KEY MATERIAL: the key's seed, all of it; decoding regenerates the key.
impl Serialize for LeanXmssSecretKey {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.key_seed.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for LeanXmssSecretKey {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Seed::deserialize(deserializer).map(|seed| key_gen_from_seed(seed).0)
    }
}

struct BottomTree {
    index: u32,
    tree: LayerTree,
    top_signature: LayerSignature,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum LeanXmssSignError {
    NoAdmissibleEncoding,
}

impl std::fmt::Display for LeanXmssSignError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoAdmissibleEncoding => write!(f, "no admissible encoding within the randomizer trial limit"),
        }
    }
}

impl std::error::Error for LeanXmssSignError {}

/// Every leaf index: what a key signs at, but for a mock key.
pub(crate) const ALL_LEAVES: RangeInclusive<LeafIndex> = 0..=LeafIndex::MAX;

/// A fresh key pair, its seed sampled from `rng`. Generates the whole top tree.
pub fn key_gen(rng: &mut impl CryptoRng) -> (LeanXmssSecretKey, LeanXmssPublicKey) {
    key_gen_from_seed(rng.random())
}

/// Deterministic [`key_gen`]: the seed is the key's entire secret material. Never
/// derive another key from it, a mock key included: the two would share one-time
/// keys (see `mock`).
pub fn key_gen_from_seed(seed: Seed) -> (LeanXmssSecretKey, LeanXmssPublicKey) {
    generate(seed, ALL_LEAVES)
}

/// The key over the leaf indices `leaves`; nodes over no leaf in it are fillers.
pub(crate) fn generate(key_seed: Seed, leaves: RangeInclusive<LeafIndex>) -> (LeanXmssSecretKey, LeanXmssPublicKey) {
    let seed = scheme_seed(&key_seed);
    let public_param = public_param(&seed);
    let (first, last) = (layer_index(*leaves.start(), 1), layer_index(*leaves.end(), 1));
    let top = LayerTree::build(&public_param, &seed, 1, 0, first, last);
    let sk = LeanXmssSecretKey {
        key_seed,
        seed,
        public_param,
        top,
        bottom: Mutex::new(None),
    };
    let pk = sk.public_key();
    (sk, pk)
}

/// Never use the same key and leaf index to sign two different messages.
/// Signing is deterministic. The first signature in a bottom tree builds it with
/// `parallel`, so never sign from inside a `parallel` task.
pub fn sign(
    sk: &LeanXmssSecretKey,
    message: &Message,
    leaf_index: LeafIndex,
) -> Result<LeanXmssSignature, LeanXmssSignError> {
    sk.sign_over(message, leaf_index, ALL_LEAVES)
}

impl LeanXmssSecretKey {
    pub fn public_key(&self) -> LeanXmssPublicKey {
        LeanXmssPublicKey {
            merkle_root: self.top.root(),
            public_param: self.public_param,
        }
    }

    /// Builds the bottom tree `leaf_index` is in, and signs its root, ahead of
    /// [`sign`]: the first signature in a bottom tree pays for both.
    pub fn prepare(&self, leaf_index: LeafIndex) -> Result<(), LeanXmssSignError> {
        self.bottom_tree(leaf_index, ALL_LEAVES).map(drop)
    }

    /// [`sign`], for a key whose trees hold only the leaf indices `leaves`.
    pub(crate) fn sign_over(
        &self,
        message: &Message,
        leaf_index: LeafIndex,
        leaves: RangeInclusive<LeafIndex>,
    ) -> Result<LeanXmssSignature, LeanXmssSignError> {
        let bottom = self.bottom_tree(leaf_index, leaves)?;
        let (randomizer, chain_values) = wots_sign(&self.public_param, &self.seed, 0, leaf_index, message)
            .ok_or(LeanXmssSignError::NoAdmissibleEncoding)?;
        Ok(LeanXmssSignature {
            leaf_index,
            bottom: LayerSignature {
                randomizer,
                chain_values,
                path: bottom.tree.path(&self.public_param, &self.seed, tree_leaf(leaf_index)),
            },
            top: bottom.top_signature.clone(),
        })
    }

    /// The bottom tree `leaf_index` is in, with the top layer's signature of its root:
    /// the cached one, or built and cached. Built outside the lock, which is only ever
    /// held to read or replace the cache.
    fn bottom_tree(
        &self,
        leaf_index: LeafIndex,
        leaves: RangeInclusive<LeafIndex>,
    ) -> Result<Arc<BottomTree>, LeanXmssSignError> {
        let index = layer_index(leaf_index, 1);
        if let Some(bottom) = self.bottom.lock().unwrap().as_ref().filter(|b| b.index == index) {
            return Ok(Arc::clone(bottom));
        }
        let (pp, seed) = (&self.public_param, &self.seed);
        let base = index << LAYER_HEIGHT;
        let first = (*leaves.start()).max(base) - base;
        let last = (*leaves.end()).min(base | tree_leaf(LeafIndex::MAX)) - base;
        let tree = LayerTree::build(pp, seed, 0, base, first, last);
        let (randomizer, chain_values) =
            wots_sign(pp, seed, 1, index, &tree.root()).ok_or(LeanXmssSignError::NoAdmissibleEncoding)?;
        let bottom = Arc::new(BottomTree {
            index,
            top_signature: LayerSignature {
                randomizer,
                chain_values,
                path: self.top.path(pp, seed, index),
            },
            tree,
        });
        *self.bottom.lock().unwrap() = Some(Arc::clone(&bottom));
        Ok(bottom)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum LeanXmssVerifyError {
    /// A layer's message digest is not a codeword.
    InvalidEncoding,
    /// The top layer does not reach the key's root.
    InvalidMerklePath,
}

impl std::fmt::Display for LeanXmssVerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidEncoding => write!(f, "a layer's message digest is not a codeword"),
            Self::InvalidMerklePath => write!(f, "the signature does not reach the key's root"),
        }
    }
}

impl std::error::Error for LeanXmssVerifyError {}

pub fn verify(
    pk: &LeanXmssPublicKey,
    message: &Message,
    signature: &LeanXmssSignature,
) -> Result<(), LeanXmssVerifyError> {
    let pp = &pk.public_param;
    let leaf_index = signature.leaf_index;
    let (_, bottom_root) = layer_root(pp, 0, layer_index(leaf_index, 0), message, &signature.bottom, |_| {})
        .ok_or(LeanXmssVerifyError::InvalidEncoding)?;
    let (_, root) = layer_root(pp, 1, layer_index(leaf_index, 1), &bottom_root, &signature.top, |_| {})
        .ok_or(LeanXmssVerifyError::InvalidEncoding)?;
    if root == pk.merkle_root {
        Ok(())
    } else {
        Err(LeanXmssVerifyError::InvalidMerklePath)
    }
}

/// The codeword of a layer's signature by key `e` and the root it reaches, or `None`
/// if its digest is not a codeword. `on_children` sees the two children of each node
/// on the path, in order.
pub fn layer_root(
    pp: &PublicParam,
    layer: usize,
    e: u32,
    message: &[u8],
    signature: &LayerSignature,
    mut on_children: impl FnMut(&[Digest; 2]),
) -> Option<([u8; V], Digest)> {
    let (codeword, leaf) = wots_leaf(pp, layer, e, message, &signature.randomizer, &signature.chain_values)?;
    let root = signature
        .path
        .iter()
        .enumerate()
        .fold(leaf, |current, (level, sibling)| {
            let children = if (e >> level) & 1 == 0 {
                [current, *sibling]
            } else {
                [*sibling, current]
            };
            on_children(&children);
            node(pp, layer, level + 1, e >> (level + 1), &children)
        });
    Some((codeword, root))
}
