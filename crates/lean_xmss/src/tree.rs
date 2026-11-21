//! One layer's Merkle tree over `2^16` leaves. Nodes are indexed on the layer, as
//! their addresses are: a bottom tree's leaves by their leaf indices.

use crate::*;

/// The level a [`LayerTree`] stores: `2^8` nodes.
pub(crate) const CACHED_LEVEL: usize = LAYER_HEIGHT - 8;
pub(crate) const CACHED_NODES: usize = 1 << (LAYER_HEIGHT - CACHED_LEVEL);

/// The Merkle parent at `level` and index `j` of `layer`.
pub fn node(pp: &PublicParam, layer: usize, level: usize, j: u32, children: &[Digest; 2]) -> Digest {
    th_digests(pp, &tweak(TWEAK_NODE, layer_hi(layer, level as u32), j), children)
}

/// Levels `from..=to` over `base`, level `from` from leaf `first` on.
fn levels(pp: &PublicParam, layer: usize, first: u32, from: usize, to: usize, base: Vec<Digest>) -> Vec<Vec<Digest>> {
    const INPUT_LEN: usize = PUBLIC_PARAM_LEN + ADDRESS_LEN + 2 * N;
    let mut levels = vec![base];
    let mut inputs = Vec::new();
    let mut digests = Vec::new();
    for level in from + 1..=to {
        let pairs = levels.last().unwrap().as_chunks::<2>().0;
        let width = pairs.len();
        inputs.resize(width * INPUT_LEN, 0);
        digests.resize(width * keccak256::OUT_LEN, 0);
        let hi = layer_hi(layer, level as u32);
        let j0 = first >> level;
        for (k, (children, input)) in pairs.iter().zip(inputs.as_chunks_mut::<INPUT_LEN>().0).enumerate() {
            input[..PUBLIC_PARAM_LEN].copy_from_slice(pp);
            input[PUBLIC_PARAM_LEN..PUBLIC_PARAM_LEN + ADDRESS_LEN].copy_from_slice(&address(&tweak(
                TWEAK_NODE,
                hi,
                j0 + k as u32,
            )));
            input[PUBLIC_PARAM_LEN + ADDRESS_LEN..].copy_from_slice(children.as_flattened());
        }
        keccak256::hash_many(&inputs, INPUT_LEN, &mut digests);
        levels.push(
            digests
                .as_chunks::<{ keccak256::OUT_LEN }>()
                .0
                .iter()
                .map(|&d| keccak256::truncate(d))
                .collect(),
        );
    }
    levels
}

/// Levels `0..=CACHED_LEVEL` under node `j` of [`CACHED_LEVEL`].
fn subtree(pp: &PublicParam, seed: &SchemeSeed, layer: usize, j: u32) -> Vec<Vec<Digest>> {
    let first = j << CACHED_LEVEL;
    let leaves = (first..=first | ((1 << CACHED_LEVEL) - 1))
        .map(|e| wots_public_leaf(pp, seed, layer, e))
        .collect();
    levels(pp, layer, first, 0, CACHED_LEVEL, leaves)
}

/// Tree `index` of `layer`: its nodes at [`CACHED_LEVEL`].
pub(crate) struct LayerTree {
    layer: usize,
    pub(crate) index: u32,
    pub(crate) nodes: Vec<Digest>,
}

impl LayerTree {
    pub(crate) fn build(pp: &PublicParam, seed: &SchemeSeed, layer: usize, index: u32) -> Self {
        let first = index << (LAYER_HEIGHT - CACHED_LEVEL);
        let nodes = (first..first + CACHED_NODES as u32)
            .map(|j| subtree(pp, seed, layer, j)[CACHED_LEVEL][0])
            .collect();
        Self { layer, index, nodes }
    }

    pub(crate) fn from_bytes(layer: usize, index: u32, nodes: &[u8]) -> Self {
        let nodes = nodes.as_chunks().0.to_vec();
        Self { layer, index, nodes }
    }

    /// Levels `CACHED_LEVEL..=LAYER_HEIGHT`.
    fn upper(&self, pp: &PublicParam) -> Vec<Vec<Digest>> {
        let first = self.index << LAYER_HEIGHT;
        levels(pp, self.layer, first, CACHED_LEVEL, LAYER_HEIGHT, self.nodes.clone())
    }

    pub(crate) fn root(&self, pp: &PublicParam) -> Digest {
        self.upper(pp)[LAYER_HEIGHT - CACHED_LEVEL][0]
    }

    /// The path of `leaf`, a leaf of this tree.
    pub(crate) fn path(&self, pp: &PublicParam, seed: &SchemeSeed, leaf: u32) -> [Digest; LAYER_HEIGHT] {
        // A level starts at a multiple of its length, hence the modulo.
        let mut levels = subtree(pp, seed, self.layer, leaf >> CACHED_LEVEL);
        levels.truncate(CACHED_LEVEL);
        levels.extend(self.upper(pp));
        std::array::from_fn(|level| levels[level][((leaf as usize >> level) ^ 1) % levels[level].len()])
    }
}
