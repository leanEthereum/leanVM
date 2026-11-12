//! One layer's Merkle tree, over a range of its `2^16` leaves. A full key's trees
//! hold every leaf; a mock key's hold a range, every node outside it a pseudorandom
//! filler. Nodes are indexed on the layer, as their addresses are: a bottom tree's
//! leaves by their leaf indices.

use crate::lean_xmss::*;

/// The Merkle parent at `level` and index `j` of `layer`.
pub fn node(pp: &PublicParam, layer: usize, level: usize, j: u32, children: &[Digest; 2]) -> Digest {
    th_digests(pp, &tweak(TWEAK_NODE, layer_hi(layer, level as u32), j), children)
}

fn filler(pp: &PublicParam, seed: &SchemeSeed, layer: usize, level: usize, j: u32) -> Digest {
    th(
        pp,
        &tweak(TWEAK_FILLER, layer_hi(layer, level as u32), j),
        seed.as_bytes(),
    )
}

pub(crate) struct LayerTree {
    layer: usize,
    /// The first leaf held.
    first: u32,
    /// Level `l` holds the nodes from `first >> l` on.
    levels: Vec<Vec<Digest>>,
}

impl LayerTree {
    /// The tree over the leaves `first..=last`, all in one tree.
    pub(crate) fn build(pp: &PublicParam, seed: &SchemeSeed, layer: usize, first: u32, last: u32) -> Self {
        debug_assert!(first <= last && first >> LAYER_HEIGHT == last >> LAYER_HEIGHT);
        let leaves = (first..=last).map(|j| wots_public_leaf(pp, seed, layer, j)).collect();
        let mut tree = Self {
            layer,
            first,
            levels: vec![leaves],
        };
        for level in 1..=LAYER_HEIGHT {
            let up = (first >> level..=last >> level)
                .map(|j| {
                    let children = [
                        tree.at(pp, seed, level - 1, 2 * j),
                        tree.at(pp, seed, level - 1, 2 * j + 1),
                    ];
                    node(pp, layer, level, j, &children)
                })
                .collect();
            tree.levels.push(up);
        }
        tree
    }

    /// Node `j` of `level`, stored if it is over a leaf held, else a filler.
    fn at(&self, pp: &PublicParam, seed: &SchemeSeed, level: usize, j: u32) -> Digest {
        match j
            .checked_sub(self.first >> level)
            .and_then(|k| self.levels[level].get(k as usize))
        {
            Some(&node) => node,
            None => filler(pp, seed, self.layer, level, j),
        }
    }

    pub(crate) fn root(&self) -> Digest {
        self.levels[LAYER_HEIGHT][0]
    }

    pub(crate) fn path(&self, pp: &PublicParam, seed: &SchemeSeed, leaf: u32) -> [Digest; LAYER_HEIGHT] {
        debug_assert!(
            leaf.checked_sub(self.first)
                .is_some_and(|k| (k as usize) < self.levels[0].len())
        );
        std::array::from_fn(|level| self.at(pp, seed, level, (leaf >> level) ^ 1))
    }
}
