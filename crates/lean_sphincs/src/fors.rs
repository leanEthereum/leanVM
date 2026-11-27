//! The few-time signature: FORS (FIPS 205 §8).
//!
//! The instance of bottom leaf `idx` has `FORS_TREES` trees of height
//! `FORS_HEIGHT`, whose leaves hash secrets derived from `SK.seed`. The message
//! digest picks a leaf in every tree, and the signature reveals its secret and
//! its path. The FORS public key is `T_k` over the trees' roots, which the bottom
//! one-time key signs.

use crate::*;

/// One FORS tree's opening: the picked leaf's secret, and its path from the
/// leaf up.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ForsTreeOpening {
    pub(crate) secret: Digest,
    pub(crate) path: [Digest; FORS_HEIGHT],
}

impl ForsTreeOpening {
    pub fn secret(&self) -> &Digest {
        &self.secret
    }
}

pub(crate) type ForsOpening = [ForsTreeOpening; FORS_TREES];

/// Instance `idx`'s address of type `t`: the bottom key's tree, and its leaf as
/// the key pair.
fn fors_adrs(idx: u64, t: u32) -> Adrs {
    OtsKey::of_index(0, idx).adrs(t)
}

/// Node `j` at height `z` of tree `c`: its tree index counts across the trees.
fn fors_node_adrs(idx: u64, c: usize, z: usize, j: usize) -> Adrs {
    fors_adrs(idx, FORS_TREE)
        .with_tree_height(z as u32)
        .with_tree_index(((c << (FORS_HEIGHT - z)) + j) as u32)
}

/// `fors_skGen`: the secret of leaf `s` of tree `c`.
fn fors_secret(sk: &ExpandedKey, idx: u64, c: usize, s: usize) -> Digest {
    let adrs = fors_adrs(idx, FORS_PRF).with_tree_index(((c << FORS_HEIGHT) + s) as u32);
    prf(&sk.pk_seed, &sk.sk_seed, &adrs)
}

/// Leaf `s` of tree `c`: `F` of its secret.
fn fors_leaf(pk_seed: &PkSeed, idx: u64, c: usize, s: usize, secret: &Digest) -> Digest {
    th(pk_seed, &fors_node_adrs(idx, c, 0, s), secret)
}

/// Node `j` at height `z` of tree `c`, from its two children.
fn fors_node(pk_seed: &PkSeed, idx: u64, c: usize, z: usize, j: usize, children: &[Digest; 2]) -> Digest {
    th_digests(pk_seed, &fors_node_adrs(idx, c, z, j), children)
}

/// `T_k` over the roots: the FORS public key.
fn fors_key(pk_seed: &PkSeed, idx: u64, roots: &[Digest; FORS_TREES]) -> Digest {
    th_digests(pk_seed, &fors_adrs(idx, FORS_ROOTS), roots)
}

/// `fors_sign` and the public key it opens, each tree being built once: the key
/// of instance `idx`, and its opening at `leaves`.
#[cfg(feature = "std")]
pub(crate) fn fors_open(sk: &ExpandedKey, idx: u64, leaves: &[usize; FORS_TREES]) -> (Digest, ForsOpening) {
    let pk_seed = &sk.pk_seed;
    let trees: Vec<_> = (0..FORS_TREES)
        .map(|c| {
            let secrets: Vec<Digest> = (0..1 << FORS_HEIGHT).map(|s| fors_secret(sk, idx, c, s)).collect();
            let leaf_hashes = secrets
                .iter()
                .enumerate()
                .map(|(s, secret)| fors_leaf(pk_seed, idx, c, s, secret))
                .collect();
            let levels = merkle_levels(leaf_hashes, FORS_HEIGHT, |z, j, pair| {
                fors_node(pk_seed, idx, c, z, j, pair)
            });
            let s = leaves[c];
            let opening = ForsTreeOpening {
                secret: secrets[s],
                path: core::array::from_fn(|z| levels[z][(s >> z) ^ 1]),
            };
            (levels[FORS_HEIGHT][0], opening)
        })
        .collect();
    let roots = core::array::from_fn(|c| trees[c].0);
    (fors_key(pk_seed, idx, &roots), core::array::from_fn(|c| trees[c].1))
}

/// `fors_pkFromSig`: the FORS public key an opening reaches at `leaves`, showing
/// `visit` the two children of every node on the way up.
pub fn fors_recover(
    pk_seed: &PkSeed,
    idx: u64,
    leaves: &[usize; FORS_TREES],
    opening: &ForsOpening,
    mut visit: impl FnMut(&[Digest; 2]),
) -> Digest {
    let roots = core::array::from_fn(|c| {
        let (s, tree) = (leaves[c], &opening[c]);
        let leaf = fors_leaf(pk_seed, idx, c, s, &tree.secret);
        keccak256::path_fold(leaf, s, &tree.path, &mut visit, |z, j, pair| {
            fors_node(pk_seed, idx, c, z, j, pair)
        })
    });
    fors_key(pk_seed, idx, &roots)
}

pub(crate) fn fors_recover_batched(
    pk_seed: &PkSeed,
    idx: u64,
    leaves: &[usize; FORS_TREES],
    opening: &ForsOpening,
) -> Digest {
    if keccak256::LANES == 1 {
        return fors_recover(pk_seed, idx, leaves, opening, |_| ());
    }
    fors_key(pk_seed, idx, &fors_roots_batched(pk_seed, idx, leaves, opening))
}

fn fors_roots_batched(
    pk_seed: &PkSeed,
    idx: u64,
    leaves: &[usize; FORS_TREES],
    opening: &ForsOpening,
) -> [Digest; FORS_TREES] {
    let mut roots = [[0; N]; FORS_TREES];
    let mut batch = ThBatch::<{ PREFIX_LEN + N }>::new(pk_seed);
    for (group, roots) in roots.chunks_mut(keccak256::LANES).enumerate() {
        for lane in 0..roots.len() {
            let c = group * keccak256::LANES + lane;
            batch.set(lane, &fors_node_adrs(idx, c, 0, leaves[c]), &opening[c].secret);
        }
        let count = roots.len();
        for (root, digest) in roots.iter_mut().zip(batch.hash(count)) {
            *root = digest;
        }
    }
    let mut batch = ThBatch::<{ PREFIX_LEN + 2 * N }>::new(pk_seed);
    for z in 0..FORS_HEIGHT {
        for (group, roots) in roots.chunks_mut(keccak256::LANES).enumerate() {
            for (lane, &current) in roots.iter().enumerate() {
                let c = group * keccak256::LANES + lane;
                let s = leaves[c];
                let sibling = opening[c].path[z];
                let children = if (s >> z) & 1 == 0 {
                    [current, sibling]
                } else {
                    [sibling, current]
                };
                batch.set(
                    lane,
                    &fors_node_adrs(idx, c, z + 1, s >> (z + 1)),
                    children.as_flattened(),
                );
            }
            let count = roots.len();
            for (root, digest) in roots.iter_mut().zip(batch.hash(count)) {
                *root = digest;
            }
        }
    }
    roots
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn batched_roots_match_tree_major_recovery() {
        let pk_seed = std::array::from_fn(|i| (7 * i + 3) as u8);
        let opening = std::array::from_fn(|c| ForsTreeOpening {
            secret: std::array::from_fn(|i| (c * 11 + i) as u8),
            path: std::array::from_fn(|z| std::array::from_fn(|i| (c * 17 + z * 7 + i) as u8)),
        });
        let mask = (1 << FORS_HEIGHT) - 1;
        let leaves = std::array::from_fn(|c| match c % 4 {
            0 => 0,
            1 => mask,
            2 => 0x155 & mask,
            _ => 0x2aa & mask,
        });
        for idx in [0, 1, (1 << H) - 1] {
            let roots = fors_roots_batched(&pk_seed, idx, &leaves, &opening);
            for c in 0..FORS_TREES {
                let leaf = fors_leaf(&pk_seed, idx, c, leaves[c], &opening[c].secret);
                let root = keccak256::path_fold(
                    leaf,
                    leaves[c],
                    &opening[c].path,
                    |_| (),
                    |z, j, pair| fors_node(&pk_seed, idx, c, z, j, pair),
                );
                assert_eq!(roots[c], root, "tree {c}, index {idx}");
            }
            assert_eq!(
                fors_recover_batched(&pk_seed, idx, &leaves, &opening),
                fors_recover(&pk_seed, idx, &leaves, &opening, |_| ())
            );
            let same = [opening[0]; FORS_TREES];
            let roots = fors_roots_batched(&pk_seed, idx, &[0; FORS_TREES], &same);
            for c in 0..FORS_TREES {
                assert!(
                    !roots[..c].contains(&roots[c]),
                    "tree addresses must separate identical openings"
                );
            }
        }
    }
}
