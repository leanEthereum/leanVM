//! The few-time signature (FORS+C): `k - 1` Merkle trees of `2^a` secret leaves.
//!
//! A signature opens one leaf per tree, at the index the message digest picks.

use crate::*;

/// `s_{idx,kappa,j}`: leaf `j`'s secret in tree `kappa` of forest `idx`.
fn secret(pp: &PublicParam, master: &[u64; 4], idx: u64, kappa: usize, j: usize) -> Digest {
    th(pp, &tweak(TWEAK_FTS_PRF, kappa, idx as u32, 0, j as u32), master)
}

/// A tree's leaf: the hash of its secret.
fn leaf(pp: &PublicParam, idx: u64, kappa: usize, j: usize, secret: &Digest) -> Digest {
    th(pp, &tweak(TWEAK_FTS_LEAF, kappa, idx as u32, 0, j as u32), secret)
}

/// A tree's node: a level and an index within it.
///
/// Inlined, since the forest's folds call it 140 times a verification.
#[inline(always)]
fn node(pp: &PublicParam, idx: u64, kappa: usize, level: usize, j: usize, left: &Digest, right: &Digest) -> Digest {
    th(
        pp,
        &tweak(TWEAK_FTS_NODE, kappa, idx as u32, level as u32, j as u32),
        &concat(left, right),
    )
}

/// `Fts.key`: the few-time public key, `Th` over the roots.
fn key(pp: &PublicParam, idx: u64, roots: &[Digest; FTS_TREES]) -> Digest {
    th::<{ 2 * FTS_TREES }>(
        pp,
        &tweak(TWEAK_FTS_ROOTS, 0, idx as u32, 0, 0),
        roots.as_flattened().try_into().unwrap(),
    )
}

/// `Fts.recover`: the few-time key an opening of the leaves `u` reaches.
pub(crate) fn recover(pp: &PublicParam, idx: u64, u: &[u32; K], opening: &[FtsOpening; FTS_TREES]) -> Digest {
    // Each tree's root: its opened leaf folded up its path.
    let roots = core::array::from_fn(|kappa| {
        let opened = u[kappa] as usize;
        let start = leaf(pp, idx, kappa, opened, &opening[kappa].secret);
        opening[kappa]
            .path
            .iter()
            .enumerate()
            .fold(start, |current, (level, sibling)| {
                let (left, right) = if (opened >> level) & 1 == 0 {
                    (&current, sibling)
                } else {
                    (sibling, &current)
                };
                node(pp, idx, kappa, level + 1, opened >> (level + 1), left, right)
            })
    });
    key(pp, idx, &roots)
}

/// `Fts.key` and `Fts.open` at once, each tree being built whole.
///
/// The last index is ignored: its tree is the dropped one.
pub(crate) fn open(pp: &PublicParam, master: &[u64; 4], idx: u64, u: &[u32; K]) -> (Digest, [FtsOpening; FTS_TREES]) {
    let mut roots = [[0; 2]; FTS_TREES];
    let opening = core::array::from_fn(|kappa| {
        let opened = u[kappa] as usize;
        let secret_of = |j| secret(pp, master, idx, kappa, j);
        let mut nodes: [Digest; 1 << A] = core::array::from_fn(|j| leaf(pp, idx, kappa, j, &secret_of(j)));
        let mut path = [[0; 2]; A];
        // Level by level in place: node `j` of the next level only reads nodes `2j` and `2j + 1`.
        for (level, sibling) in path.iter_mut().enumerate() {
            *sibling = nodes[(opened >> level) ^ 1];
            for j in 0..(1 << A) >> (level + 1) {
                nodes[j] = node(pp, idx, kappa, level + 1, j, &nodes[2 * j], &nodes[2 * j + 1]);
            }
        }
        roots[kappa] = nodes[0];
        FtsOpening {
            secret: secret_of(opened),
            path,
        }
    });
    (key(pp, idx, &roots), opening)
}
