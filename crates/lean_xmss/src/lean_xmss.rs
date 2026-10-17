//! Keys, signing and verification. The secret key holds the top tree and builds
//! a bottom tree, with the top layer's signature of its root, the first time it
//! signs in it, keeping the last one.

use std::sync::{Mutex, MutexGuard};

use rand::{CryptoRng, Rng};
use serde::{Deserialize, Serialize};

use crate::*;

/// Ordered lexicographically on `flatten()`, which is what an aggregate's claims are
/// sorted by.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
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
    #[serde(with = "crate::array_serialization")]
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

/// The encoding is SECRET KEY MATERIAL: it carries the seed.
#[derive(Debug, Serialize, Deserialize)]
pub struct LeanXmssSecretKey {
    seed: Seed,
    public_param: PublicParam,
    /// The leaf indices the key signs at: all of them, but for a mock key.
    first: LeafIndex,
    last: LeafIndex,
    top: LayerTree,
    #[serde(skip)]
    bottom: Mutex<Option<BottomTree>>,
}

#[derive(Debug)]
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

/// A fresh key pair, its seed sampled from `rng`. Generates the whole top tree.
pub fn key_gen(rng: &mut impl CryptoRng) -> (LeanXmssSecretKey, LeanXmssPublicKey) {
    key_gen_from_seed(rng.random())
}

/// Deterministic [`key_gen`]: the seed is the key's entire secret material. Never
/// derive another key from it, a mock key included: the two would share one-time
/// keys (see `mock`).
pub fn key_gen_from_seed(seed: Seed) -> (LeanXmssSecretKey, LeanXmssPublicKey) {
    generate(seed, 0, LeafIndex::MAX)
}

/// The key signing at `first..=last`; nodes over no leaf in that range are fillers.
pub(crate) fn generate(seed: Seed, first: LeafIndex, last: LeafIndex) -> (LeanXmssSecretKey, LeanXmssPublicKey) {
    let public_param = th(&[0; PUBLIC_PARAM_LEN], &tweak(TWEAK_PARAMETER, 0, 0), &seed);
    let top = LayerTree::build(&public_param, &seed, 1, 0, layer_index(first, 1), layer_index(last, 1));
    let sk = LeanXmssSecretKey {
        seed,
        public_param,
        first,
        last,
        top,
        bottom: Mutex::new(None),
    };
    let pk = sk.public_key();
    (sk, pk)
}

/// Never use the same key and leaf index to sign two different messages.
/// Signing is deterministic.
pub fn sign(
    sk: &LeanXmssSecretKey,
    message: &Message,
    leaf_index: LeafIndex,
) -> Result<LeanXmssSignature, LeanXmssSignError> {
    let bottom = sk.bottom_tree(leaf_index)?;
    let tree = &bottom.as_ref().unwrap();
    let (randomizer, chain_values) =
        wots_sign(&sk.public_param, &sk.seed, 0, leaf_index, message).ok_or(LeanXmssSignError::NoAdmissibleEncoding)?;
    let leaf = leaf_index & ((1 << LAYER_HEIGHT) - 1);
    Ok(LeanXmssSignature {
        leaf_index,
        bottom: LayerSignature {
            randomizer,
            chain_values,
            path: tree.tree.path(&sk.public_param, &sk.seed, leaf),
        },
        top: tree.top_signature.clone(),
    })
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
        self.bottom_tree(leaf_index).map(drop)
    }

    fn bottom_tree(&self, leaf_index: LeafIndex) -> Result<MutexGuard<'_, Option<BottomTree>>, LeanXmssSignError> {
        assert!(
            (self.first..=self.last).contains(&leaf_index),
            "a mock key signs only in its range"
        );
        let index = layer_index(leaf_index, 1);
        let mut cache = self.bottom.lock().unwrap();
        if cache.as_ref().is_none_or(|bottom| bottom.index != index) {
            let (pp, seed) = (&self.public_param, &self.seed);
            let in_tree = |leaf: LeafIndex| leaf & ((1 << LAYER_HEIGHT) - 1);
            let first = if layer_index(self.first, 1) == index {
                in_tree(self.first)
            } else {
                0
            };
            let last = if layer_index(self.last, 1) == index {
                in_tree(self.last)
            } else {
                in_tree(LeafIndex::MAX)
            };
            let tree = LayerTree::build(pp, seed, 0, index << LAYER_HEIGHT, first, last);
            let (randomizer, chain_values) =
                wots_sign(pp, seed, 1, index, &tree.root()).ok_or(LeanXmssSignError::NoAdmissibleEncoding)?;
            let top_signature = LayerSignature {
                randomizer,
                chain_values,
                path: self.top.path(pp, seed, index),
            };
            *cache = Some(BottomTree {
                index,
                tree,
                top_signature,
            });
        }
        Ok(cache)
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
    let bottom_root = layer_root(pp, 0, layer_index(leaf_index, 0), message, &signature.bottom, |_| {})
        .ok_or(LeanXmssVerifyError::InvalidEncoding)?;
    let root = layer_root(pp, 1, layer_index(leaf_index, 1), &bottom_root, &signature.top, |_| {})
        .ok_or(LeanXmssVerifyError::InvalidEncoding)?;
    if root == pk.merkle_root {
        Ok(())
    } else {
        Err(LeanXmssVerifyError::InvalidMerklePath)
    }
}

/// The root a layer's signature by key `e` reaches, or `None` if its digest is not a
/// codeword. `on_children` sees the two children of each node on the path, in order.
pub fn layer_root(
    pp: &PublicParam,
    layer: usize,
    e: u32,
    message: &[u8],
    signature: &LayerSignature,
    mut on_children: impl FnMut(&[Digest; 2]),
) -> Option<Digest> {
    let (_, leaf) = wots_leaf(pp, layer, e, message, &signature.randomizer, &signature.chain_values)?;
    Some(
        signature
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
            }),
    )
}
