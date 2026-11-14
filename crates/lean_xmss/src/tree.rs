//! One layer's Merkle tree over `2^16` leaves. Nodes are indexed on the layer, as
//! their addresses are: a bottom tree's leaves by their leaf indices.

use crate::*;

/// The Merkle parent at `level` and index `j` of `layer`.
pub fn node(pp: &PublicParam, layer: usize, level: usize, j: u32, children: &[Digest; 2]) -> Digest {
    th_digests(pp, &tweak(TWEAK_NODE, layer_hi(layer, level as u32), j), children)
}

pub(crate) struct LayerTree {
    /// The first leaf.
    first: u32,
    /// Level `l` holds the nodes from `first >> l` on.
    levels: Vec<Vec<Digest>>,
}

impl LayerTree {
    /// Tree `index` of `layer`.
    pub(crate) fn build(pp: &PublicParam, seed: &SchemeSeed, layer: usize, index: u32) -> Self {
        let first = index << LAYER_HEIGHT;
        let leaves = (first..=first | ((1 << LAYER_HEIGHT) - 1))
            .map(|j| wots_public_leaf(pp, seed, layer, j))
            .collect();
        let mut levels: Vec<Vec<Digest>> = vec![leaves];
        for level in 1..=LAYER_HEIGHT {
            let up = levels[level - 1].as_chunks().0.iter().zip(first >> level..);
            let up = up.map(|(children, j)| node(pp, layer, level, j, children)).collect();
            levels.push(up);
        }
        Self { first, levels }
    }

    pub(crate) fn root(&self) -> Digest {
        self.levels[LAYER_HEIGHT][0]
    }

    pub(crate) fn path(&self, leaf: u32) -> [Digest; LAYER_HEIGHT] {
        let k = leaf - self.first;
        debug_assert!(k >> LAYER_HEIGHT == 0);
        std::array::from_fn(|level| self.levels[level][((k >> level) ^ 1) as usize])
    }
}
