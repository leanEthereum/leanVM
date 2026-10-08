//! The few-time signature (FORS+C): `k - 1` Merkle trees of `2^a` secret leaves.
//!
//! A signature opens one leaf per tree, at the index the message digest picks.

use crate::*;

/// `s_{idx,kappa,j}`: leaf `j`'s secret in tree `kappa` of forest `idx`.
fn secret(pp: &PublicParam, master: &[u64; 4], idx: u64, kappa: usize, j: usize) -> Digest {
    th(pp, &tweak(TWEAK_FTS_PRF, kappa, idx as u32, 0, j as u32), master)
}

/// A tree's leaves, `Th` of a secret, `tw | P | secret`, in one block kept across leaves: a leaf writes only its
/// tweak and its secret.
struct LeafHash(Template<6>);

impl LeafHash {
    fn new(pp: &PublicParam) -> Self {
        Self(Template::new([0, 0, pp[0], pp[1], 0, 0]))
    }

    /// Leaf `j` of tree `kappa`: the hash of its secret.
    #[inline(always)]
    fn leaf(&mut self, idx: u64, kappa: usize, j: usize, secret: &Digest) -> Digest {
        self.0.set(0, tweak(TWEAK_FTS_LEAF, kappa, idx as u32, 0, j as u32));
        self.0.set(PAYLOAD, *secret);
        digest(self.0.digest())
    }
}

/// A tree's node: a level and an index within it.
#[inline(always)]
fn node(hash: &mut NodeHash, idx: u64, kappa: usize, level: usize, j: usize, left: &Digest, right: &Digest) -> Digest {
    hash.hash(
        tweak(TWEAK_FTS_NODE, kappa, idx as u32, level as u32, j as u32),
        left,
        right,
    )
}

/// `Fts.key`: the few-time public key, `Th` over the roots, tree `kappa`'s being `root(kappa)`, each written into
/// the hash as it is reached.
#[inline(always)]
fn key(pp: &PublicParam, idx: u64, root: impl FnMut(usize) -> Digest) -> Digest {
    digest(hash_with(|m| {
        m.write(tweak(TWEAK_FTS_ROOTS, 0, idx as u32, 0, 0))
            .write(*pp)
            .write_each(FTS_TREES, root);
    }))
}

/// `Fts.recover`: the few-time key an opening of the leaves `u` reaches.
pub(crate) fn recover(
    pp: &PublicParam,
    nodes: &mut NodeHash,
    idx: u64,
    u: &[usize; K],
    opening: &[FtsOpening; FTS_TREES],
) -> Digest {
    let mut leaves = LeafHash::new(pp);
    // Each tree's root: its opened leaf folded up its path.
    key(pp, idx, |kappa| {
        let (opened, opening) = (u[kappa], &opening[kappa]);
        let leaf = leaves.leaf(idx, kappa, opened, &opening.secret);
        let tw = tweak(TWEAK_FTS_NODE, kappa, idx as u32, 0, 0);
        fold(nodes, tw, opened as u64, leaf, &opening.path)
    })
}

/// `Fts.key` and `Fts.open` at once, each tree being built whole.
///
/// The last index is ignored: its tree is the dropped one.
pub(crate) fn open(pp: &PublicParam, master: &[u64; 4], idx: u64, u: &[usize; K]) -> (Digest, [FtsOpening; FTS_TREES]) {
    let mut roots = [[0; 2]; FTS_TREES];
    let mut leaves = LeafHash::new(pp);
    let mut hash = NodeHash::new(pp);
    let opening = core::array::from_fn(|kappa| {
        let opened = u[kappa];
        let secret_of = |j| secret(pp, master, idx, kappa, j);
        let mut nodes: [Digest; 1 << A] = core::array::from_fn(|j| leaves.leaf(idx, kappa, j, &secret_of(j)));
        let mut path = [[0; 2]; A];
        // Level by level in place: node `j` of the next level only reads nodes `2j` and `2j + 1`.
        for (level, sibling) in path.iter_mut().enumerate() {
            *sibling = nodes[(opened >> level) ^ 1];
            for j in 0..(1 << A) >> (level + 1) {
                nodes[j] = node(&mut hash, idx, kappa, level + 1, j, &nodes[2 * j], &nodes[2 * j + 1]);
            }
        }
        roots[kappa] = nodes[0];
        FtsOpening {
            secret: secret_of(opened),
            path,
        }
    });
    (key(pp, idx, |kappa| roots[kappa]), opening)
}
