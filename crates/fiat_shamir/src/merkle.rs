// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Digest encoding and Merkle openings carried by proofs.

use crate::transcript::Error;
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

/// Decode [`hash_to_scalars`]. Fallible because both halves come off the proof
/// stream, where a malicious prover picks the third limb: a digest half is
/// 128-bit, so a nonzero one is not a digest at all.
#[inline]
pub fn scalars_to_hash(scalars: &[F192; 2]) -> Result<Hash, Error> {
    if scalars.iter().any(|s| s.c2 != 0) {
        return Err(Error::NonCanonicalEncoding);
    }
    let mut hash = [0u8; 32];
    for (i, s) in scalars.iter().enumerate() {
        hash[16 * i..16 * i + 8].copy_from_slice(&s.c0.to_le_bytes());
        hash[16 * i + 8..16 * i + 16].copy_from_slice(&s.c1.to_le_bytes());
    }
    Ok(hash)
}

/// Hash one leaf with standard BLAKE2s-256.
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

/// Restore a stored row's omitted zero prefix.
fn leaf_image(row: &[F64], leaf_words: usize) -> Vec<F64> {
    let mut image = vec![F64::ZERO; leaf_words];
    image[leaf_words - row.len()..].copy_from_slice(row);
    image
}

/// The committer's leaf preimage: the image's words, little-endian.
fn hash_words(image: &[F64]) -> Hash {
    let mut bytes = vec![0u8; 8 * image.len()];
    for (dst, word) in bytes.as_chunks_mut::<8>().0.iter_mut().zip(image) {
        *dst = word.0.to_le_bytes();
    }
    hash_leaf(&bytes)
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
    pub fn prune(tree: &[Hash], num_leaves: usize, positions: &[usize], row: impl Fn(usize) -> Vec<F64>) -> Self {
        assert!(num_leaves.is_power_of_two() && num_leaves > 0);
        assert_eq!(tree.len(), 2 * num_leaves - 1);
        let sorted = sorted_unique(positions);
        debug_assert!(sorted.iter().all(|&p| p < num_leaves));

        let mut sibling_hashes = Vec::new();
        let mut active = sorted.clone();
        let (mut level_start, mut level_len) = (0usize, num_leaves);
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
                    sibling_hashes.push(tree[level_start + (p ^ 1)]);
                    i += 1;
                }
                next.push(p >> 1);
            }
            // `next` stays sorted-unique: sibling pairs collapse to one parent,
            // and `p >> 1` is otherwise strictly increasing.
            active = next;
            level_start += level_len;
            level_len >>= 1;
        }

        Self {
            leaf_data: sorted.iter().map(|&q| row(q)).collect(),
            sibling_hashes,
        }
    }

    /// The stored rows' leaf hashes, or `None` if any row is not `row_words` wide.
    fn leaf_hashes(&self, queries: &[usize], row_words: usize, leaf_words: usize) -> Option<(Vec<usize>, Vec<Hash>)> {
        let sorted = sorted_unique(queries);
        if sorted.len() != self.leaf_data.len() || row_words > leaf_words {
            return None;
        }
        let hashes = self
            .leaf_data
            .iter()
            .map(|row| (row.len() == row_words).then(|| hash_words(&leaf_image(row, leaf_words))))
            .collect::<Option<Vec<_>>>()?;
        Some((sorted, hashes))
    }

    /// Verifier side: authenticate this phase against `root` and expand it into
    /// one opening per query, in `queries` order (duplicates included).
    ///
    /// The single way to consume a phase, so rows can never be read without the
    /// Merkle check having run. Rebuilding every node on the queried paths both
    /// recomputes the root AND yields each query's full sibling path, so the
    /// pruned form is checked and the unpruned form produced in one walk.
    ///
    /// `None` on any mismatch: a wrong row count or width, an out-of-range
    /// query, an octopus with too few or too many siblings, or a root that does
    /// not match.
    pub fn open(
        &self,
        root: &Hash,
        num_leaves: usize,
        queries: &[usize],
        row_words: usize,
        leaf_words: usize,
    ) -> Option<Vec<RawMerklePath>> {
        if !num_leaves.is_power_of_two() || num_leaves == 0 || queries.is_empty() {
            return None;
        }
        let height = num_leaves.trailing_zeros() as usize;
        let (sorted, leaf_hashes) = self.leaf_hashes(queries, row_words, leaf_words)?;
        if sorted.last().is_some_and(|&p| p >= num_leaves) {
            return None;
        }

        // Rebuild every node on the queried paths bottom-up, pulling a stored
        // sibling only where that sibling is not itself a queried subtree.
        let mut supplied = self.sibling_hashes.iter();
        let mut known: Vec<Vec<(usize, Hash)>> = Vec::with_capacity(height);
        let mut nodes: Vec<(usize, Hash)> = sorted.iter().copied().zip(leaf_hashes).collect();
        for _ in 0..height {
            let mut level = Vec::with_capacity(2 * nodes.len());
            let mut parents = Vec::with_capacity(nodes.len());
            let mut i = 0;
            while i < nodes.len() {
                let idx = nodes[i].0;
                let paired = idx & 1 == 0 && nodes.get(i + 1).is_some_and(|&(j, _)| j == (idx | 1));
                let (left, right) = if paired {
                    (nodes[i].1, nodes[i + 1].1)
                } else if idx & 1 == 0 {
                    (nodes[i].1, *supplied.next()?)
                } else {
                    (*supplied.next()?, nodes[i].1)
                };
                parents.push((idx >> 1, hash_pair(&left, &right)));
                level.push((idx & !1, left));
                level.push((idx | 1, right));
                i += if paired { 2 } else { 1 };
            }
            known.push(level);
            nodes = parents;
        }
        // The last fold leaves exactly the root, and nothing may be left over.
        if supplied.next().is_some() || nodes[0].1 != *root {
            return None;
        }

        let per_distinct: Vec<Vec<Hash>> = sorted
            .iter()
            .map(|&leaf| {
                (0..height)
                    .map(|lvl| {
                        let level = &known[lvl];
                        let pos = level.binary_search_by_key(&((leaf >> lvl) ^ 1), |&(j, _)| j).ok()?;
                        Some(level[pos].1)
                    })
                    .collect::<Option<Vec<_>>>()
            })
            .collect::<Option<Vec<_>>>()?;

        queries
            .iter()
            .map(|q| {
                let slot = sorted.binary_search(q).ok()?;
                Some(RawMerklePath {
                    leaf_index: *q,
                    leaf_data: leaf_image(&self.leaf_data[slot], leaf_words),
                    path: per_distinct[slot].clone(),
                })
            })
            .collect()
    }
}

/// One query's opening, unpruned: the leaf's FULL image (zero prefix included) and
/// the full sibling path from that leaf up to the root.
///
/// The redundant form. Several queries of one phase repeat whatever siblings
/// they share, which is exactly what makes it simple to consume: recomputing
/// the root is a walk up one path, with no dedup bookkeeping. Recursive witness
/// construction and the Python verifier consume this; the wire format
/// ([`PrunedMerklePaths`]) sends each shared sibling once.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct RawMerklePath {
    /// Transcript-derived position, retained for recursive witness construction.
    pub leaf_index: usize,
    pub leaf_data: Vec<F64>,
    pub path: Vec<Hash>,
}

impl RawMerklePath {
    /// Recompute the root this opening claims, from its leaf and path.
    pub fn root(&self, leaf_index: usize) -> Hash {
        let mut acc = hash_words(&self.leaf_data);
        let mut idx = leaf_index;
        for sibling in &self.path {
            let (left, right) = if idx & 1 == 0 { (acc, *sibling) } else { (*sibling, acc) };
            acc = hash_pair(&left, &right);
            idx >>= 1;
        }
        acc
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tree_of(rows: &[Vec<F64>]) -> Vec<Hash> {
        let mut tree: Vec<Hash> = rows.iter().map(|r| hash_words(r)).collect();
        let (mut start, mut len) = (0usize, rows.len());
        while len > 1 {
            for i in 0..len / 2 {
                tree.push(hash_pair(&tree[start + 2 * i], &tree[start + 2 * i + 1]));
            }
            start += len;
            len /= 2;
        }
        tree
    }

    #[test]
    fn prune_open_roundtrip() {
        let (num_leaves, width, height) = (8usize, 4usize, 3usize);
        let rows: Vec<Vec<F64>> = (0..num_leaves)
            .map(|q| (0..width).map(|j| F64((q * width + j) as u64)).collect())
            .collect();
        let tree = tree_of(&rows);
        let root = tree[tree.len() - 1];
        let queries = [5usize, 1, 5, 3, 1];

        let paths = PrunedMerklePaths::prune(&tree, num_leaves, &queries, |q| rows[q].clone());
        assert_eq!(paths.leaf_data.len(), 3, "one row per distinct query");

        let openings = paths.open(&root, num_leaves, &queries, width, width).expect("open");
        assert_eq!(openings.len(), queries.len());
        for (opening, &q) in openings.iter().zip(&queries) {
            assert_eq!(opening.leaf_data, rows[q], "row must follow query order");
            assert_eq!(opening.path.len(), height);
            assert_eq!(opening.root(q), root, "each unpruned path must reach the root");
        }
    }

    #[test]
    fn malformed_phases_are_rejected() {
        let (num_leaves, width) = (8usize, 4usize);
        let rows: Vec<Vec<F64>> = (0..num_leaves)
            .map(|q| (0..width).map(|j| F64((q * width + j) as u64)).collect())
            .collect();
        let tree = tree_of(&rows);
        let root = tree[tree.len() - 1];
        let queries = [5usize, 1, 3];
        let good = PrunedMerklePaths::prune(&tree, num_leaves, &queries, |q| rows[q].clone());
        let open = |p: &PrunedMerklePaths, qs: &[usize], w: usize, n: usize| p.open(&root, n, qs, w, w);
        assert!(open(&good, &queries, width, num_leaves).is_some(), "honest phase");

        let mut extra = good.clone();
        extra.sibling_hashes.push([0u8; 32]);
        assert!(open(&extra, &queries, width, num_leaves).is_none(), "trailing sibling");

        let mut short = good.clone();
        short.sibling_hashes.pop();
        assert!(open(&short, &queries, width, num_leaves).is_none(), "missing sibling");

        let mut flipped = good.clone();
        flipped.sibling_hashes[0][0] ^= 1;
        assert!(
            open(&flipped, &queries, width, num_leaves).is_none(),
            "tampered sibling"
        );

        let mut bad_row = good.clone();
        bad_row.leaf_data[0][0] = F64(bad_row.leaf_data[0][0].0 ^ 1);
        assert!(open(&bad_row, &queries, width, num_leaves).is_none(), "tampered row");

        let mut wide = good.clone();
        wide.leaf_data[0].push(F64(0));
        assert!(open(&wide, &queries, width, num_leaves).is_none(), "wrong row width");

        assert!(
            open(&good, &queries, width + 1, num_leaves).is_none(),
            "wrong announced width"
        );
        assert!(open(&good, &[5, 1], width, num_leaves).is_none(), "wrong query count");
        assert!(
            open(&good, &[9, 1, 3], width, num_leaves).is_none(),
            "out-of-range query"
        );
        assert!(open(&good, &queries, width, 7).is_none(), "non-power-of-two tree");
    }

    #[test]
    fn non_canonical_digest_halves_are_rejected() {
        let hash: Hash = std::array::from_fn(|i| (i * 7 + 1) as u8);
        let scalars = hash_to_scalars(&hash);
        assert_eq!(scalars_to_hash(&scalars), Ok(hash));
        assert_eq!(
            scalars_to_hash(&[F192::new(scalars[0].c0, scalars[0].c1, 1), scalars[1]]),
            Err(Error::NonCanonicalEncoding)
        );
    }
}
