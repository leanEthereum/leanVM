// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Digest encoding and Merkle openings carried by proofs.

use primitives::field::{F64, F192};

pub type Hash = [u8; 32];

/// Encode a Merkle hash as the two field words transcripts carry it in: two
/// 128-bit halves, each a K pair with a spare top lane. Every digest in the
/// protocol uses this one split (the commitment root, the public input, the
/// guest's MD state), so the VM sees one shape everywhere.
#[inline]
pub fn hash_to_scalars(hash: &Hash) -> [F192; 2] {
    let word_at = |offset: usize| u64::from_le_bytes(hash[offset..offset + 8].try_into().unwrap());
    [
        F192::new(word_at(0), word_at(8), 0),
        F192::new(word_at(16), word_at(24), 0),
    ]
}

/// Hash one leaf ([`primitives::hash::hash`]).
#[inline]
pub fn hash_leaf(data: &[u8]) -> Hash {
    primitives::hash::hash(data)
}

/// Hash two children into their parent.
#[inline]
pub fn hash_pair(left: &Hash, right: &Hash) -> Hash {
    let mut buf = [0u8; 64];
    buf[..32].copy_from_slice(left);
    buf[32..].copy_from_slice(right);
    primitives::hash::hash(&buf)
}

/// Query positions with duplicates removed, ascending: the order a phase stores
/// its rows in, and the order the octopus is built and checked against.
fn sorted_unique(queries: &[usize]) -> Vec<usize> {
    let mut unique = queries.to_vec();
    unique.sort_unstable();
    unique.dedup();
    unique
}

/// One opening phase's Merkle data: the rows opened at each distinct queried
/// position (sorted), and one octopus authenticating all of them.
///
/// Leaf data is `F64` because that is what a Merkle preimage is; an `E`-valued
/// row of width `w` is `3w` words, packed by the opener. The phase never says how
/// wide a row is: the caller announces that, which is what pins the leaf image the
/// octopus is checked against. A row may be NARROWER than the image it hashes to,
/// the missing words being a zero prefix the caller also announces,
/// which is what keeps a padding-free L0 commitment's absent lanes out of the
/// proof.
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct PrunedMerklePaths {
    pub leaf_data: Vec<Vec<F64>>,
    pub sibling_hashes: Vec<Hash>,
}

impl PrunedMerklePaths {
    /// Prover side: open `positions` of `tree`, storing one row per distinct
    /// position plus a single octopus over them. `row(q)` is the leaf at `q`.
    ///
    /// For `q` queries in a tree of depth `d` the octopus is at most `q · d`
    /// hashes (what `q` independent paths would cost) and typically much
    /// smaller, since a sibling shared by several paths is emitted once.
    pub fn prune<'a>(tree: &[Hash], num_leaves: usize, positions: &[usize], row: impl Fn(usize) -> &'a [F64]) -> Self {
        assert!(num_leaves.is_power_of_two() && num_leaves > 0);
        assert_eq!(tree.len(), 2 * num_leaves - 1);
        let level_start = |level: usize| 2 * num_leaves - ((2 * num_leaves) >> level);
        Self::prune_with(num_leaves, positions, |level, i| tree[level_start(level) + i], row)
    }

    /// Like [`Self::prune`], for a tree held in pieces: `node(level, i)` is node `i` of `level`, leaves at level 0.
    pub fn prune_with<'a>(
        num_leaves: usize,
        positions: &[usize],
        node: impl Fn(usize, usize) -> Hash,
        row: impl Fn(usize) -> &'a [F64],
    ) -> Self {
        assert!(num_leaves.is_power_of_two() && num_leaves > 0);
        let sorted = sorted_unique(positions);
        debug_assert!(sorted.iter().all(|&p| p < num_leaves));

        let mut sibling_hashes = Vec::new();
        let mut active = sorted.clone();
        let (mut level, mut level_len) = (0usize, num_leaves);
        while level_len > 1 {
            let mut next = Vec::with_capacity(active.len());
            let mut i = 0;
            while i < active.len() {
                let p = active[i];
                // Both children active: they fold into the same parent, so no
                // sibling is needed. Otherwise the sibling has to be sent.
                if i + 1 < active.len() && active[i + 1] == (p ^ 1) {
                    i += 2;
                } else {
                    sibling_hashes.push(node(level, p ^ 1));
                    i += 1;
                }
                next.push(p >> 1);
            }
            // `next` stays sorted-unique: sibling pairs collapse to one parent,
            // and `p >> 1` is otherwise strictly increasing.
            active = next;
            level += 1;
            level_len >>= 1;
        }

        Self {
            leaf_data: sorted.iter().map(|&q| row(q).to_vec()).collect(),
            sibling_hashes,
        }
    }
}
