//! The few-time signature: FORS (FIPS 205 §8) without its root hash.
//!
//! Bottom leaf `idx` has its own instance of `FORS_TREES` trees of height
//! `FORS_HEIGHT`, whose leaves hash secrets derived from the seed. The message
//! digest picks a leaf in every tree, and the signature reveals its secret and
//! its path. No tree has a root hash: what stands for one is the two nodes below
//! it, so the last element of a path is the other top node, and the FORS key is
//! the two top nodes of every tree, which the bottom one-time key signs as they
//! are.

use crate::lean_sphincs::*;

/// One FORS tree's opening: the picked leaf's secret, and its path from the
/// leaf up, the last node being the other top node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ForsTreeOpening {
    pub secret: Digest,
    pub path: [Digest; FORS_HEIGHT],
}

pub type ForsOpening = [ForsTreeOpening; FORS_TREES];

/// The FORS key: the two top nodes of every tree, left first.
pub type ForsKey = [[Digest; 2]; FORS_TREES];

/// The secrets of leaves `2p` and `2p + 1` of tree `c`: the two halves of one
/// hash of the seed.
fn secret_pair(pp: &PublicParam, seed: &MasterSecret, idx: u32, c: usize, p: usize) -> [Digest; 2] {
    th_pair(pp, &tweak(TWEAK_FORS_PRF, fors_hi(c, p), idx), seed)
}

/// Leaf `l` of tree `c`: the hash of its secret.
fn fors_leaf(pp: &PublicParam, idx: u32, c: usize, l: usize, secret: &Digest) -> Digest {
    th(pp, &tweak(TWEAK_FORS_LEAF, fors_hi(c, l), idx), secret)
}

/// Node `j` on `level` of tree `c`, from its two children.
fn fors_node(pp: &PublicParam, idx: u32, c: usize, level: usize, j: usize, children: &[Digest; 2]) -> Digest {
    th_digests(pp, &tweak(TWEAK_FORS_NODE, fors_hi(c, level + (j << 4)), idx), children)
}

/// `Fts.key` and `Fts.sign` together, each tree being built once: the key of
/// instance `idx`, and its opening at `leaves`.
pub(crate) fn fors_open(
    pp: &PublicParam,
    seed: &MasterSecret,
    idx: u32,
    leaves: &[usize; FORS_TREES],
) -> (ForsKey, ForsOpening) {
    let trees = parallel::map_collect(FORS_TREES, |c| {
        let secrets: Vec<Digest> = (0..1 << (FORS_HEIGHT - 1))
            .flat_map(|p| secret_pair(pp, seed, idx, c, p))
            .collect();
        let leaf_hashes = secrets
            .iter()
            .enumerate()
            .map(|(l, secret)| fors_leaf(pp, idx, c, l, secret))
            .collect();
        let levels = merkle_levels(leaf_hashes, FORS_HEIGHT - 1, |level, j, pair| {
            fors_node(pp, idx, c, level, j, pair)
        });
        let l = leaves[c];
        let opening = ForsTreeOpening {
            secret: secrets[l],
            path: std::array::from_fn(|level| levels[level][(l >> level) ^ 1]),
        };
        ([levels[FORS_HEIGHT - 1][0], levels[FORS_HEIGHT - 1][1]], opening)
    });
    (std::array::from_fn(|c| trees[c].0), std::array::from_fn(|c| trees[c].1))
}

/// `Fts.recover`: the FORS key an opening reaches at `leaves`.
pub fn fors_recover(pp: &PublicParam, idx: u32, leaves: &[usize; FORS_TREES], opening: &ForsOpening) -> ForsKey {
    fors_recover_with(pp, idx, leaves, opening, |_| ())
}

/// [`fors_recover`], showing `visit` the two children of every node on the way
/// up, then each tree's two top nodes.
pub fn fors_recover_with(
    pp: &PublicParam,
    idx: u32,
    leaves: &[usize; FORS_TREES],
    opening: &ForsOpening,
    mut visit: impl FnMut(&[Digest; 2]),
) -> ForsKey {
    std::array::from_fn(|c| {
        let (l, tree) = (leaves[c], &opening[c]);
        let leaf = fors_leaf(pp, idx, c, l, &tree.secret);
        let (last, below) = tree.path.split_last().unwrap();
        let top = below.iter().enumerate().fold(leaf, |current, (level, sibling)| {
            let children = ordered(l >> level, current, *sibling);
            visit(&children);
            fors_node(pp, idx, c, level + 1, l >> (level + 1), &children)
        });
        let tops = ordered(l >> (FORS_HEIGHT - 1), top, *last);
        visit(&tops);
        tops
    })
}
