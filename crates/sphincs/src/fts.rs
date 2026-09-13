//! The few-time signature: a forest of `k-1` Merkle trees of `2^a` secret
//! leaves, one leaf opened per tree at an index the message digest picks
//! (FORS+C).
//!
//! Reuse leaks rather than breaks: after `r` signatures on one instance an
//! adversary holds `r` leaves per tree, and can sign a message only if it lands
//! on that instance, has last index zero, and has every other index on a leaf it
//! already holds.

use crate::*;

/// What a signature carries for the few-time key: the opened secret and the
/// Merkle path of each of the `k-1` trees.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FtsOpening {
    pub secrets: [Digest; NUM_FTS_TREES],
    pub paths: [[Digest; A]; NUM_FTS_TREES],
}

/// `s_{idx,kappa,j} = Th(P, tw_ftsprf(idx,kappa,j), S)`.
fn fts_secret(pp: &PublicParam, master: &MasterSecret, idx: u64, kappa: usize, j: usize) -> Digest {
    th(pp, &tweak(TWEAK_FTS_PRF, kappa, idx as u32, 0, j as u32), master)
}

fn fts_leaf(pp: &PublicParam, idx: u64, kappa: usize, j: usize, secret: &Digest) -> Digest {
    th(pp, &tweak(TWEAK_FTS_LEAF, kappa, idx as u32, 0, j as u32), secret)
}

fn fts_node(pp: &PublicParam, idx: u64, kappa: usize, level: usize, j: usize, left: &Digest, right: &Digest) -> Digest {
    let tw = tweak(TWEAK_FTS_NODE, kappa, idx as u32, level as u32, j as u32);
    th_digests(pp, &tw, &[*left, *right])
}

/// `Fts.key`: the few-time public key, `Th` over the `k-1` roots.
fn fts_key_of_roots(pp: &PublicParam, idx: u64, roots: &[Digest; NUM_FTS_TREES]) -> Digest {
    th_digests(pp, &tweak(TWEAK_FTS_ROOTS, 0, idx as u32, 0, 0), roots)
}

/// `Fts.key` and `Fts.open` together, the forest being built once. `u[k-1]` is
/// ignored: its tree is the dropped one.
pub fn fts_open(pp: &PublicParam, master: &MasterSecret, idx: u64, u: &[u32; K]) -> (Digest, FtsOpening) {
    let mut opening = FtsOpening {
        secrets: [[0; N]; NUM_FTS_TREES],
        paths: [[[0; N]; A]; NUM_FTS_TREES],
    };
    let mut roots = [[0; N]; NUM_FTS_TREES];
    for kappa in 0..NUM_FTS_TREES {
        let opened = u[kappa] as usize;
        let mut nodes = Vec::with_capacity(1 << A);
        for j in 0..1 << A {
            let secret = fts_secret(pp, master, idx, kappa, j);
            if j == opened {
                opening.secrets[kappa] = secret;
            }
            nodes.push(fts_leaf(pp, idx, kappa, j, &secret));
        }
        for level in 0..A {
            opening.paths[kappa][level] = nodes[(opened >> level) ^ 1];
            nodes = (0..nodes.len() / 2)
                .map(|j| fts_node(pp, idx, kappa, level + 1, j, &nodes[2 * j], &nodes[2 * j + 1]))
                .collect();
        }
        roots[kappa] = nodes[0];
    }
    (fts_key_of_roots(pp, idx, &roots), opening)
}

/// `Fts.recover`: the few-time key an opening reaches, which is `Fts.key` on an
/// opening of the leaves `u` of that instance and nothing else short of a
/// collision.
pub fn fts_recover(pp: &PublicParam, idx: u64, u: &[u32; K], opening: &FtsOpening) -> Digest {
    let roots = std::array::from_fn(|kappa| {
        let opened = u[kappa] as usize;
        let leaf = fts_leaf(pp, idx, kappa, opened, &opening.secrets[kappa]);
        (0..A).fold(leaf, |node, level| {
            let sibling = &opening.paths[kappa][level];
            let (left, right) = if (opened >> level) & 1 == 0 {
                (node, *sibling)
            } else {
                (*sibling, node)
            };
            fts_node(pp, idx, kappa, level + 1, opened >> (level + 1), &left, &right)
        })
    });
    fts_key_of_roots(pp, idx, &roots)
}
