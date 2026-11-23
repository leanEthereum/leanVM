//! Keys, signing and verification. The secret key holds the top tree and builds
//! a bottom tree, with the top layer's signature of its root, the first time it
//! signs in it or prepares it, keeping the [`MAX_CACHED_BOTTOM_TREES`] it used last.
//! It stores one level of each tree and recomputes the rest per path.

#[cfg(feature = "std")]
use std::{
    collections::VecDeque,
    sync::{Arc, Mutex},
};

use crate::*;

/// A leanXMSS public key: a Merkle root and a public parameter.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LeanXmssPublicKey {
    pub(crate) merkle_root: Digest,
    pub(crate) public_param: PublicParam,
}

impl LeanXmssPublicKey {
    pub fn to_bytes(&self) -> [u8; PUB_KEY_SIZE] {
        let mut out = [0u8; PUB_KEY_SIZE];
        out[..N].copy_from_slice(&self.merkle_root);
        out[N..].copy_from_slice(&self.public_param);
        out
    }

    pub fn from_bytes(bytes: &[u8; PUB_KEY_SIZE]) -> Self {
        Self {
            merkle_root: bytes[..N].try_into().unwrap(),
            public_param: bytes[N..].try_into().unwrap(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LayerSignature {
    pub(crate) randomizer: Randomizer,
    pub(crate) chain_values: [Digest; V],
    pub(crate) path: [Digest; LAYER_HEIGHT],
}

impl LayerSignature {
    pub fn randomizer(&self) -> &Randomizer {
        &self.randomizer
    }

    pub fn chain_values(&self) -> &[Digest; V] {
        &self.chain_values
    }

    /// Its encoding, in order.
    fn parts(&self) -> [&[u8]; 3] {
        [
            &self.randomizer,
            self.chain_values.as_flattened(),
            self.path.as_flattened(),
        ]
    }

    /// Decodes from the front of `rest`.
    fn read(rest: &mut &[u8]) -> Self {
        Self {
            randomizer: take(rest),
            chain_values: core::array::from_fn(|_| take(rest)),
            path: core::array::from_fn(|_| take(rest)),
        }
    }
}

/// Pops the first `L` bytes of `rest`.
fn take<const L: usize>(rest: &mut &[u8]) -> [u8; L] {
    let (first, tail) = rest.split_first_chunk().unwrap();
    *rest = tail;
    *first
}

/// A leanXMSS signature, at one leaf index.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LeanXmssSignature {
    pub(crate) leaf_index: LeafIndex,
    pub(crate) bottom: LayerSignature,
    pub(crate) top: LayerSignature,
}

impl LeanXmssSignature {
    pub fn leaf_index(&self) -> LeafIndex {
        self.leaf_index
    }

    pub fn to_bytes(&self) -> [u8; SIG_SIZE] {
        let mut out = [0; SIG_SIZE];
        let mut at = 0;
        let mut put = |bytes: &[u8]| {
            out[at..at + bytes.len()].copy_from_slice(bytes);
            at += bytes.len();
        };
        put(&self.leaf_index.to_le_bytes());
        for part in [&self.bottom, &self.top].into_iter().flat_map(LayerSignature::parts) {
            put(part);
        }
        debug_assert_eq!(at, SIG_SIZE);
        out
    }

    pub fn from_bytes(bytes: &[u8; SIG_SIZE]) -> Self {
        let mut rest = &bytes[..];
        let leaf_index = LeafIndex::from_le_bytes(take(&mut rest));
        let (bottom, top) = (LayerSignature::read(&mut rest), LayerSignature::read(&mut rest));
        debug_assert!(rest.is_empty());
        Self {
            leaf_index,
            bottom,
            top,
        }
    }
}

/// A [`SecretKey`] with some cached values to make signing faster.
#[cfg(feature = "std")]
pub struct LeanXmssExpandedSecretKey {
    key_seed: SecretKey,
    public_key: LeanXmssPublicKey,
    top: LayerTree,
    /// The bottom trees the key used last, least recently used first.
    bottoms: Mutex<VecDeque<Arc<BottomTree>>>,
}

/// How many recently used bottom trees a [`LeanXmssExpandedSecretKey`] caches.
#[cfg(feature = "std")]
pub const MAX_CACHED_BOTTOM_TREES: usize = 4;

#[cfg(feature = "std")]
impl core::fmt::Debug for LeanXmssExpandedSecretKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("LeanXmssExpandedSecretKey")
            .field("public_key", &self.public_key())
            .finish_non_exhaustive()
    }
}

#[cfg(feature = "std")]
struct BottomTree {
    tree: LayerTree,
    top_signature: LayerSignature,
}

/// A tree's nodes, in bytes.
const CACHED_TREE_SIZE: usize = CACHED_NODES * N;
/// A cached bottom tree, in bytes.
const CACHED_BOTTOM_SIZE: usize = size_of::<u32>() + LAYER_SIG_SIZE + CACHED_TREE_SIZE;
const _: () = assert!(CACHED_TREE_SIZE == 4096 && CACHED_BOTTOM_SIZE == 5300);

/// computes the expanded secret key (for fast signing), and the public key, from a given secret key
#[cfg(feature = "std")]
pub fn key_gen(key_seed: &SecretKey) -> (LeanXmssExpandedSecretKey, LeanXmssPublicKey) {
    let seed = scheme_seed(key_seed);
    let public_param = public_param(&seed);
    let sk = LeanXmssExpandedSecretKey::new(key_seed, LayerTree::build(&public_param, &seed, 1, 0));
    let pk = sk.public_key;
    (sk, pk)
}

/// Never use the same key and leaf index to sign two different messages.
/// Signing is deterministic. The first signature in a bottom tree builds that tree.
///
/// # Panics
///
/// When none of a layer's `2^32` randomizer trials gives a codeword, with probability below
/// `2^-2954` (`doc/lean_xmss`): impossible in practice.
#[cfg(feature = "std")]
pub fn sign(sk: &LeanXmssExpandedSecretKey, message: &Message, leaf_index: LeafIndex) -> LeanXmssSignature {
    let bottom = sk.bottom_tree(leaf_index);
    let (pp, seed) = (&sk.public_key.public_param, scheme_seed(&sk.key_seed));
    let (randomizer, chain_values) = wots_sign(pp, &seed, 0, leaf_index, message).expect("an admissible encoding");
    LeanXmssSignature {
        leaf_index,
        bottom: LayerSignature {
            randomizer,
            chain_values,
            path: bottom.tree.path(pp, &seed, leaf_index),
        },
        top: bottom.top_signature.clone(),
    }
}

#[cfg(feature = "std")]
impl LeanXmssExpandedSecretKey {
    fn new(key_seed: &SecretKey, top: LayerTree) -> Self {
        let public_param = public_param(&scheme_seed(key_seed));
        Self {
            key_seed: *key_seed,
            public_key: LeanXmssPublicKey {
                merkle_root: top.root(&public_param),
                public_param,
            },
            top,
            bottoms: Mutex::new(VecDeque::with_capacity(MAX_CACHED_BOTTOM_TREES + 1)),
        }
    }

    /// The cached trees, which hold no secret.
    pub fn cache_to_bytes(&self) -> Vec<u8> {
        let mut out = self.top.nodes.as_flattened().to_vec();
        for bottom in self.bottoms.lock().unwrap().iter() {
            out.extend(bottom.tree.index.to_le_bytes());
            out.extend(bottom.top_signature.parts().concat());
            out.extend(bottom.tree.nodes.as_flattened());
        }
        out
    }

    /// Loads a key from its seed, its public key and the bytes of [`Self::cache_to_bytes`].
    /// `None` if the length is wrong or the bytes do not match the key.
    ///
    /// Each tree's stored level is checked: the top tree's must hash to the public key's root, and
    /// each bottom tree's to a root its top-layer signature signs under the public key. The levels
    /// below are recomputed from the seed, so a loaded key signs as a built one.
    pub fn from_cache_bytes(key_seed: &SecretKey, public_key: &LeanXmssPublicKey, bytes: &[u8]) -> Option<Self> {
        let (top, bottoms) = bytes.split_at_checked(CACHED_TREE_SIZE)?;
        let (bottoms, []) = bottoms.as_chunks::<CACHED_BOTTOM_SIZE>() else {
            return None;
        };
        let sk = Self::new(key_seed, LayerTree::from_bytes(1, 0, top));
        if sk.public_key != *public_key {
            return None;
        }
        let pp = &public_key.public_param;
        for bottom in bottoms {
            let mut rest = &bottom[..];
            let index = u32::from_le_bytes(take(&mut rest));
            let top_signature = LayerSignature::read(&mut rest);
            let tree = LayerTree::from_bytes(0, index, rest);
            let signed = index >> LAYER_HEIGHT == 0
                && layer_root(pp, 1, index, &tree.root(pp), &top_signature, |_| {})
                    .is_some_and(|(_, root)| root == public_key.merkle_root);
            if !signed {
                return None;
            }
            sk.cache(Arc::new(BottomTree { tree, top_signature }));
        }
        Some(sk)
    }

    pub fn public_key(&self) -> LeanXmssPublicKey {
        self.public_key
    }

    /// Makes the future signing at `leaf_index` faster (by precomputing and caching the bottom tree).
    /// The cache size is [`MAX_CACHED_BOTTOM_TREES`] bottom trees.
    pub fn prepare(&self, leaf_index: LeafIndex) {
        self.bottom_tree(leaf_index);
    }

    /// The bottom tree `leaf_index` is in, with the top layer's signature of its root:
    /// the cached one, or built and cached. Built outside the lock, which is only ever
    /// held to read or update the cache.
    fn bottom_tree(&self, leaf_index: LeafIndex) -> Arc<BottomTree> {
        let index = layer_index(leaf_index, 1);
        if let Some(bottom) = use_cached(&mut self.bottoms.lock().unwrap(), index) {
            return bottom;
        }
        let (pp, seed) = (&self.public_key.public_param, &scheme_seed(&self.key_seed));
        let tree = LayerTree::build(pp, seed, 0, index);
        let (randomizer, chain_values) = wots_sign(pp, seed, 1, index, &tree.root(pp)).expect("an admissible encoding");
        let bottom = Arc::new(BottomTree {
            top_signature: LayerSignature {
                randomizer,
                chain_values,
                path: self.top.path(pp, seed, index),
            },
            tree,
        });
        self.cache(bottom)
    }

    /// Caches `bottom`, or returns the one another thread cached first.
    fn cache(&self, bottom: Arc<BottomTree>) -> Arc<BottomTree> {
        let mut bottoms = self.bottoms.lock().unwrap();
        if let Some(cached) = use_cached(&mut bottoms, bottom.tree.index) {
            return cached;
        }
        bottoms.push_back(Arc::clone(&bottom));
        if bottoms.len() > MAX_CACHED_BOTTOM_TREES {
            bottoms.pop_front();
        }
        bottom
    }
}

/// Bottom tree `index` if cached, moved to the most recently used end.
#[cfg(feature = "std")]
fn use_cached(bottoms: &mut VecDeque<Arc<BottomTree>>, index: u32) -> Option<Arc<BottomTree>> {
    let at = bottoms.iter().position(|b| b.tree.index == index)?;
    let bottom = bottoms.remove(at)?;
    bottoms.push_back(Arc::clone(&bottom));
    Some(bottom)
}

/// verifies a signature for a given message and public key
pub fn verify(pk: &LeanXmssPublicKey, message: &Message, signature: &LeanXmssSignature) -> bool {
    let pp = &pk.public_param;
    let leaf_index = signature.leaf_index;
    layer_root(pp, 0, layer_index(leaf_index, 0), message, &signature.bottom, |_| {})
        .and_then(|(_, bottom_root)| {
            layer_root(pp, 1, layer_index(leaf_index, 1), &bottom_root, &signature.top, |_| {})
        })
        .is_some_and(|(_, root)| root == pk.merkle_root)
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
    on_children: impl FnMut(&[Digest; 2]),
) -> Option<([u8; V], Digest)> {
    let (codeword, leaf) = wots_leaf(pp, layer, e, message, &signature.randomizer, &signature.chain_values)?;
    let root = keccak256::path_fold(leaf, e as usize, &signature.path, on_children, |level, j, children| {
        node(pp, layer, level, j as u32, children)
    });
    Some((codeword, root))
}
