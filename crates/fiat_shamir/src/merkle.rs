// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Digest encoding and Merkle openings carried by proofs.

use crate::Hashing;
use crate::transcript::TranscriptError;
use primitives::field::{F64, F192};
use primitives::hash::{BATCH, BLOCK_LEN, OUT_LEN, hash_many_dyn_from_state, portable, zero_prefix_state};
use serde::{Deserialize, Serialize};
use std::mem::MaybeUninit;

pub type Hash = [u8; 32];

/// Encode a Merkle hash as the two field words transcripts carry it in: two
/// 128-bit halves, each a K pair with a spare top lane. Every digest in the
/// protocol uses this one split (the commitment root, the public input), so the
/// VM sees one shape everywhere.
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
pub fn scalars_to_hash(scalars: &[F192; 2]) -> Result<Hash, TranscriptError> {
    if scalars.iter().any(|s| s.c2 != 0) {
        return Err(TranscriptError::NonCanonicalEncoding);
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

/// Bytes of the staging tile for leaves whose zero padding does not end on a hash block boundary.
const STAGE_TILE_BYTES: usize = 16 << 10;

/// How rows become leaf digests: each leaf image is `zeros(leaf_bytes - row_bytes) || row`.
///
/// The image's whole hash blocks of leading zeros are one chaining value, computed once for every leaf.
///
/// The committer and a prover's replay hash leaves through it; the native verifier takes the same digests one at a
/// time (the [`Hashing`] of [`crate::arith::Portable`]).
pub struct LeafHasher(LeafShape);

/// The hashing plan for one leaf shape, chosen once.
enum LeafShape {
    /// The padding is whole blocks, so past the shared prefix each row is its own image, hashed where it lies.
    Direct {
        /// Bytes of a row.
        row_bytes: usize,
        /// The chaining value after the zero blocks.
        state: [u32; 8],
        /// Bytes the zero blocks account for, the hash counter's start.
        t_offset: u64,
    },
    /// Some padding remains past the zero blocks, so rows are zero-extended in a tile first.
    ///
    /// The copy also aligns each image to whole cache lines, which the hasher's loads want.
    Staged {
        /// Bytes of a row.
        row_bytes: usize,
        /// Bytes of the image past the zero blocks: the remaining padding, then the row.
        image: usize,
        /// The chaining value after the zero blocks.
        state: [u32; 8],
        /// Bytes the zero blocks account for, the hash counter's start.
        t_offset: u64,
    },
    /// Leaves of no whole number of blocks: one at a time, zero-extended to `leaf_bytes`.
    Single {
        /// Bytes of a row.
        row_bytes: usize,
        /// Bytes of a leaf image.
        leaf_bytes: usize,
    },
}

impl LeafHasher {
    /// The hasher for rows of `row_bytes` in leaf images of `leaf_bytes`.
    ///
    /// # Panics
    ///
    /// Panics unless `0 < row_bytes <= leaf_bytes`, and a staged image fits the tile.
    pub fn new(row_bytes: usize, leaf_bytes: usize) -> Self {
        assert!(0 < row_bytes && row_bytes <= leaf_bytes, "a leaf holds its row");
        if !leaf_bytes.is_multiple_of(BLOCK_LEN) {
            assert!(
                row_bytes == leaf_bytes || leaf_bytes <= STAGE_TILE_BYTES,
                "a padded leaf fits the tile"
            );
            return Self(LeafShape::Single { row_bytes, leaf_bytes });
        }
        let zero_blocks = (leaf_bytes - row_bytes) / BLOCK_LEN;
        let (state, t_offset) = (zero_prefix_state(zero_blocks), (zero_blocks * BLOCK_LEN) as u64);
        let image = leaf_bytes - zero_blocks * BLOCK_LEN;
        if image == row_bytes {
            Self(LeafShape::Direct {
                row_bytes,
                state,
                t_offset,
            })
        } else {
            assert!(image <= STAGE_TILE_BYTES, "a padded leaf fits the tile");
            Self(LeafShape::Staged {
                row_bytes,
                image,
                state,
                t_offset,
            })
        }
    }

    /// Bytes of a row.
    pub const fn row_bytes(&self) -> usize {
        match self.0 {
            LeafShape::Direct { row_bytes, .. }
            | LeafShape::Staged { row_bytes, .. }
            | LeafShape::Single { row_bytes, .. } => row_bytes,
        }
    }

    /// Hash one leaf per row into `out`.
    pub fn hash(&self, rows: &[u8], out: &mut [MaybeUninit<Hash>]) {
        match self.0 {
            LeafShape::Direct {
                row_bytes,
                state,
                t_offset,
            } => {
                hash_many_dyn_from_state(rows, row_bytes, &state, t_offset, digests_as_bytes(out));
            }
            LeafShape::Staged {
                row_bytes,
                image,
                state,
                t_offset,
            } => {
                // Images per tile: whole hash batches where the tile holds at least one batch.
                let per_tile = STAGE_TILE_BYTES / image;
                let per_tile = if per_tile >= BATCH {
                    per_tile - per_tile % BATCH
                } else {
                    per_tile
                };
                let mut tile = Tile::new();
                for (out, rows) in out.chunks_mut(per_tile).zip(rows.chunks(per_tile * row_bytes)) {
                    let images = tile.extend(rows, row_bytes, image);
                    hash_many_dyn_from_state(images, image, &state, t_offset, digests_as_bytes(out));
                }
            }
            LeafShape::Single { row_bytes, leaf_bytes } if row_bytes == leaf_bytes => {
                for (slot, row) in out.iter_mut().zip(rows.chunks_exact(row_bytes)) {
                    slot.write(hash_leaf(row));
                }
            }
            LeafShape::Single { row_bytes, leaf_bytes } => {
                let mut tile = Tile::new();
                for (slot, row) in out.iter_mut().zip(rows.chunks_exact(row_bytes)) {
                    slot.write(hash_leaf(tile.extend(row, row_bytes, leaf_bytes)));
                }
            }
        }
    }
}

/// A zeroed staging buffer of `STAGE_TILE_BYTES`.
struct Tile([u64; STAGE_TILE_BYTES / 8]);

impl Tile {
    const fn new() -> Self {
        Self([0; STAGE_TILE_BYTES / 8])
    }

    /// Lay each `row_bytes` row at the end of its own `image`-byte slot, and return the slots.
    ///
    /// - Invariant: one tile serves one `(row_bytes, image)` shape.
    /// - So the bytes before each row are never written, and stay zero.
    fn extend(&mut self, rows: &[u8], row_bytes: usize, image: usize) -> &[u8] {
        // SAFETY: the view covers exactly the tile's bytes, and any bytes written form valid u64 words.
        let tile: &mut [u8] = unsafe { std::slice::from_raw_parts_mut(self.0.as_mut_ptr().cast(), STAGE_TILE_BYTES) };
        let n = rows.len() / row_bytes;
        for (slot, row) in tile.chunks_exact_mut(image).zip(rows.chunks_exact(row_bytes)) {
            slot[image - row_bytes..].copy_from_slice(row);
        }
        &tile[..n * image]
    }
}

/// The digest slots as the bytes a hasher writes.
const fn digests_as_bytes(out: &mut [MaybeUninit<Hash>]) -> &mut [u8] {
    // SAFETY: a digest is 32 bytes with no padding, and the hasher only writes.
    unsafe { std::slice::from_raw_parts_mut(out.as_mut_ptr().cast(), out.len() * OUT_LEN) }
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

/// The native verifier's leaf digests of `row_bytes` rows in `leaf_bytes` images, one at a time by the portable
/// compression.
///
/// The digests [`LeafHasher`] gives, the image's whole zero blocks again one chaining value.
pub(crate) fn hash_leaves_portable(rows: &[u8], row_bytes: usize, leaf_bytes: usize) -> Vec<Hash> {
    if !leaf_bytes.is_multiple_of(BLOCK_LEN) {
        let mut image = vec![0u8; leaf_bytes];
        return (rows.chunks_exact(row_bytes))
            .map(|row| {
                image[leaf_bytes - row_bytes..].copy_from_slice(row);
                portable::hash(&image)
            })
            .collect();
    }
    let zero_blocks = (leaf_bytes - row_bytes) / BLOCK_LEN;
    let (state, t_offset) = (
        portable::zero_prefix_state(zero_blocks),
        (zero_blocks * BLOCK_LEN) as u64,
    );
    let mut image = vec![0u8; leaf_bytes - zero_blocks * BLOCK_LEN];
    let at = image.len() - row_bytes;
    (rows.chunks_exact(row_bytes))
        .map(|row| {
            image[at..].copy_from_slice(row);
            portable::hash_from_state(&image, &state, t_offset)
        })
        .collect()
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
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
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
    fn leaf_hashes<H: Hashing>(
        &self,
        queries: &[usize],
        row_words: usize,
        leaf_words: usize,
    ) -> Option<(Vec<usize>, Vec<Hash>)> {
        let sorted = sorted_unique(queries);
        if sorted.len() != self.leaf_data.len() || row_words > leaf_words {
            return None;
        }
        if self.leaf_data.iter().any(|row| row.len() != row_words) {
            return None;
        }
        // The rows, one after another, hashed as the committer hashed them.
        let bytes: Vec<u8> = (self.leaf_data.iter().flatten())
            .flat_map(|word| word.0.to_le_bytes())
            .collect();
        Some((sorted, H::hash_leaves(&bytes, 8 * row_words, 8 * leaf_words)))
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
    ///
    /// `H` hashes: the native verifier's [`crate::arith::Portable`], or a prover's replay's [`crate::arith::Native`].
    pub fn open<H: Hashing>(
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
        let (sorted, leaf_hashes) = self.leaf_hashes::<H>(queries, row_words, leaf_words)?;
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
            let mut pairs = Vec::with_capacity(nodes.len());
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
                parents.push(idx >> 1);
                pairs.push([left, right]);
                level.push((idx & !1, left));
                level.push((idx | 1, right));
                i += if paired { 2 } else { 1 };
            }
            known.push(level);
            nodes = parents.into_iter().zip(H::hash_pairs(&pairs)).collect();
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
/// the root is a walk up one path, with no dedup bookkeeping.
///
/// Recursion consumes this form. The wire format ([`PrunedMerklePaths`]) sends each shared sibling once.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RawMerklePath {
    /// Transcript-derived position.
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
    use crate::arith::{Native, Portable};

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

        let openings = paths
            .open::<Portable>(&root, num_leaves, &queries, width, width)
            .expect("open");
        let native = paths.open::<Native>(&root, num_leaves, &queries, width, width);
        assert_eq!(native.as_ref(), Some(&openings), "both backends open alike");
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
        let open = |p: &PrunedMerklePaths, qs: &[usize], w: usize, n: usize| p.open::<Portable>(&root, n, qs, w, w);
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
            Err(TranscriptError::NonCanonicalEncoding)
        );
    }
}
