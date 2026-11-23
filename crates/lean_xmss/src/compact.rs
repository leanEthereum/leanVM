//! A compact key state: what signing at one leaf needs besides the seed, so a
//! signer holds no tree. It is the leaf's path in its bottom tree, that tree's root
//! and the top layer's signature of the root, all of which every signature made
//! from it publishes.

use crate::*;

/// How many bytes in a [`LeanXmssCompactState`].
pub const COMPACT_STATE_SIZE: usize = LEAF_INDEX_SIZE + LAYER_HEIGHT * N + N + LAYER_SIG_SIZE;

/// The state to sign at one leaf index from the [`SecretKey`] alone.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LeanXmssCompactState {
    pub(crate) leaf_index: LeafIndex,
    pub(crate) path: [Digest; LAYER_HEIGHT],
    pub(crate) root: Digest,
    pub(crate) top: LayerSignature,
}

impl LeanXmssCompactState {
    pub fn leaf_index(&self) -> LeafIndex {
        self.leaf_index
    }

    /// The leaf index, then the bottom path, the bottom root and the top layer's signature.
    pub fn to_bytes(&self) -> [u8; COMPACT_STATE_SIZE] {
        let mut out = [0; COMPACT_STATE_SIZE];
        let mut at = 0;
        let mut put = |bytes: &[u8]| {
            out[at..at + bytes.len()].copy_from_slice(bytes);
            at += bytes.len();
        };
        put(&self.leaf_index.to_le_bytes());
        put(self.path.as_flattened());
        put(&self.root);
        put(&self.top.randomizer);
        put(self.top.chain_values.as_flattened());
        put(self.top.path.as_flattened());
        debug_assert_eq!(at, COMPACT_STATE_SIZE);
        out
    }

    /// Check the state against the expected public key with [`Self::public_key`] before signing.
    pub fn from_bytes(bytes: &[u8; COMPACT_STATE_SIZE]) -> Self {
        let mut at = 0;
        let mut take = |len: usize| {
            at += len;
            &bytes[at - len..at]
        };
        let leaf_index = LeafIndex::from_le_bytes(take(LEAF_INDEX_SIZE).try_into().unwrap());
        let path = std::array::from_fn(|_| take(N).try_into().unwrap());
        let root = take(N).try_into().unwrap();
        let top = LayerSignature {
            randomizer: take(RANDOMIZER_LEN).try_into().unwrap(),
            chain_values: std::array::from_fn(|_| take(N).try_into().unwrap()),
            path: std::array::from_fn(|_| take(N).try_into().unwrap()),
        };
        debug_assert_eq!(at, COMPACT_STATE_SIZE);
        Self {
            leaf_index,
            path,
            root,
            top,
        }
    }

    /// The public key the state leads to under `key_seed`, or `None` if the top layer's
    /// signature is not of a codeword.
    pub fn public_key(&self, key_seed: &SecretKey) -> Option<LeanXmssPublicKey> {
        let public_param = public_param(&scheme_seed(key_seed));
        let e = layer_index(self.leaf_index, 1);
        let (_, merkle_root) = layer_root(&public_param, 1, e, &self.root, &self.top, |_| {})?;
        Some(LeanXmssPublicKey {
            merkle_root,
            public_param,
        })
    }

    /// The state at `leaf_index`, a later leaf of the same bottom tree, or `None` for an
    /// earlier leaf or another tree: a state never signs two messages at one leaf. It
    /// recomputes the leaves of the subtree below the level where the two paths part, at
    /// most half the tree.
    pub fn advance(&self, key_seed: &SecretKey, leaf_index: LeafIndex) -> Option<Self> {
        if layer_index(leaf_index, 1) != layer_index(self.leaf_index, 1) || leaf_index < self.leaf_index {
            return None;
        }
        let mut next = self.clone();
        next.leaf_index = leaf_index;
        if leaf_index == self.leaf_index {
            return Some(next);
        }
        let seed = scheme_seed(key_seed);
        let pp = &public_param(&seed);
        let split = (leaf_index ^ self.leaf_index).ilog2() as usize;
        let leaf = wots_public_leaf(pp, &seed, 0, self.leaf_index);
        next.path[split] = keccak256::path_fold(
            leaf,
            self.leaf_index as usize,
            &self.path[..split],
            |_| {},
            |level, j, children| node(pp, 0, level, j as u32, children),
        );
        let first = (leaf_index >> split) << split;
        let mut nodes: Vec<Digest> = (first..=first | ((1 << split) - 1))
            .map(|j| wots_public_leaf(pp, &seed, 0, j))
            .collect();
        for level in 0..split {
            next.path[level] = nodes[(((leaf_index - first) >> level) ^ 1) as usize];
            let up = nodes.as_chunks().0.iter().zip(first >> (level + 1)..);
            nodes = up.map(|(children, j)| node(pp, 0, level + 1, j, children)).collect();
        }
        Some(next)
    }
}

/// [`sign`] at the state's leaf index, from the seed and the state alone: the same signature.
///
/// Never use the same key and state to sign two different messages.
///
/// # Panics
///
/// As [`sign`] does.
pub fn sign_compact(key_seed: &SecretKey, state: &LeanXmssCompactState, message: &Message) -> LeanXmssSignature {
    let seed = scheme_seed(key_seed);
    let leaf_index = state.leaf_index;
    let (randomizer, chain_values) =
        wots_sign(&public_param(&seed), &seed, 0, leaf_index, message).expect("an admissible encoding");
    LeanXmssSignature {
        leaf_index,
        bottom: LayerSignature {
            randomizer,
            chain_values,
            path: state.path,
        },
        top: state.top.clone(),
    }
}
