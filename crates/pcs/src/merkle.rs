// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Binary Merkle tree with BLAKE2s, built in cache-resident subtree blocks.
//!
//! The committer builds the tree; a proof carries pruned opening paths, which the verifier checks against the root.
//!
//! # Layout
//!
//! For `n = 2^k` leaves, level `j` counted from the leaves:
//!
//! ```text
//!     tree[0 .. n]                  level 0, the leaf digests
//!     tree[n .. 3n/2]               level 1
//!     ...
//!     tree[2n - 2]                  the root
//!
//!     level j starts at 2n - 2n / 2^j
//! ```
//!
//! # Why blocks
//!
//! - A node depends only on the aligned run of leaves below it.
//! - So one task hashes a block of leaves and climbs its subtree while the digests are in L1.
//! - The encoder hands blocks over as it finishes them, so leaves are hashed while the rows are in L2.
//! - Above the blocks, the last block to finish a unit of nodes climbs it, so no pass waits on a barrier.

use parallel::SendPtr;
use primitives::field::F64;
use primitives::hash::{BATCH, BLOCK_LEN, OUT_LEN, hash_many, hash_many_dyn_from_state, zero_prefix_state};
use std::mem::MaybeUninit;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

pub type Hash = [u8; 32];

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
/// The committer and the native verifier hash leaves through it alike.
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

/// Nodes of one level that a unit gathers above the blocks: 32 KiB of digests, which stay in L1.
///
/// The last block to finish its part of a unit climbs the whole unit.
const UNIT: usize = 1 << 10;

/// A Merkle tree filled one aligned block of leaves at a time, from any thread.
///
/// - Leaf `i` hashes the image `zeros(leaf_words - row_words) || row_i`.
/// - Blocks must all have the same power-of-two size, and together cover every leaf once.
pub(crate) struct MerkleBuilder {
    /// The flat tree being written.
    nodes: Nodes,
    /// How a row becomes its leaf digest.
    leaves: LeafHasher,
    /// Which blocks have arrived, and which units above them are complete.
    progress: Progress,
}

impl MerkleBuilder {
    /// An empty tree of `num_leaves` leaves, each a `leaf_words`-word image committing a `row_words`-word row.
    ///
    /// # Panics
    ///
    /// Panics unless `num_leaves` is a power of two and `0 < row_words <= leaf_words`.
    /// Also panics if a leaf with padding needs staging and its image exceeds the 16 KiB tile.
    pub(crate) fn new(num_leaves: usize, row_words: usize, leaf_words: usize) -> Self {
        Self::with_bytes(num_leaves, 8 * row_words, 8 * leaf_words)
    }

    /// An empty tree as above, its rows and leaf images sized in bytes.
    fn with_bytes(num_leaves: usize, row_bytes: usize, leaf_bytes: usize) -> Self {
        assert!(num_leaves.is_power_of_two(), "num_leaves must be power of 2");
        Self {
            nodes: Nodes::new(num_leaves),
            leaves: LeafHasher::new(row_bytes, leaf_bytes),
            progress: Progress::new(num_leaves),
        }
    }

    /// Hash the rows in `rows` as the leaves from `first_leaf` on, and climb their subtree.
    ///
    /// # Panics
    ///
    /// Panics unless the block is a power of two of whole rows, aligned and inside the tree.
    /// Also panics unless it is sized like every other block, and new.
    pub(crate) fn absorb(&self, first_leaf: usize, rows: &[F64]) {
        self.absorb_bytes(first_leaf, words_as_bytes(rows));
    }

    /// Absorb a block of rows given as bytes.
    fn absorb_bytes(&self, first_leaf: usize, rows: &[u8]) {
        let n = rows.len() / self.leaves.row_bytes();
        assert_eq!(rows.len(), n * self.leaves.row_bytes(), "whole rows");
        self.progress.claim(first_leaf, n);
        // SAFETY: the claim makes these leaves ours alone, and with them their subtree up to where it joins a unit.
        unsafe {
            self.leaves.hash(rows, self.nodes.level_mut(0, first_leaf, n));
            self.complete(0, first_leaf, n);
        }
    }

    /// Climb `n` finished nodes of `level` from node `first`, then hand the result to its unit.
    ///
    /// - A whole level climbs straight to the root.
    /// - Otherwise the climb stops at the last level whose hashing still fills a whole batch.
    /// - The unit's last arrival climbs the unit in turn, and so on up to the root.
    ///
    /// # Safety
    ///
    /// The nodes are initialized, and no other caller holds them or their subtree.
    unsafe fn complete(&self, level: usize, first: usize, n: usize) {
        if n == self.nodes.width(level) {
            // SAFETY: forwarded, and the whole level climbs to the root.
            return unsafe { self.nodes.climb(level, 0, n, n.ilog2() as usize) };
        }
        // Climb while each level's parents still fill a whole hash batch.
        let height = (n / BATCH).max(1).ilog2() as usize;
        // SAFETY: forwarded.
        unsafe { self.nodes.climb(level, first, n, height) };
        let (level, first, n) = (level + height, first >> height, n >> height);

        let unit = UNIT.min(self.nodes.width(level));
        if self.progress.arrive(level, first / unit, n, unit) {
            // SAFETY: every node of the unit is written, and only its last arrival gets here, after seeing every write.
            unsafe { self.complete(level, first - first % unit, unit) };
        }
    }

    /// The finished tree.
    ///
    /// # Panics
    ///
    /// Panics unless every leaf was absorbed.
    pub(crate) fn finish(self) -> Vec<Hash> {
        assert!(self.progress.all_claimed(), "every leaf absorbed");
        // SAFETY: every block was absorbed once, and the last arrivals climbed every level above the blocks.
        unsafe { self.nodes.assume_init() }
    }
}

/// The flat tree, written at disjoint nodes by concurrent climbs.
struct Nodes {
    /// The `2n - 1` nodes, level after level from the leaves.
    tree: Vec<MaybeUninit<Hash>>,
    /// The tree's first node, through which concurrent climbs write.
    base: SendPtr<MaybeUninit<Hash>>,
    /// Leaves `n`, a power of two.
    num_leaves: usize,
}

impl Nodes {
    /// An uninitialized tree over `num_leaves` leaves.
    fn new(num_leaves: usize) -> Self {
        let mut tree = Box::new_uninit_slice(2 * num_leaves - 1).into_vec();
        let base = SendPtr(tree.as_mut_ptr());
        Self { tree, base, num_leaves }
    }

    /// Nodes on `level`.
    const fn width(&self, level: usize) -> usize {
        self.num_leaves >> level
    }

    /// Index of `level`'s first node.
    const fn start(&self, level: usize) -> usize {
        2 * self.num_leaves - ((2 * self.num_leaves) >> level)
    }

    /// Nodes `first .. first + n` of `level`.
    ///
    /// # Safety
    ///
    /// No other live slice overlaps them.
    #[allow(clippy::mut_from_ref)]
    unsafe fn level_mut(&self, level: usize, first: usize, n: usize) -> &mut [MaybeUninit<Hash>] {
        debug_assert!(first + n <= self.width(level));
        // SAFETY: in bounds, and exclusive by the caller.
        unsafe { self.base.slice(self.start(level) + first, n) }
    }

    /// Hash `n` nodes of `level`, from node `first`, `height` levels up.
    ///
    /// # Safety
    ///
    /// The nodes are initialized, and nothing else touches their subtree up to `height` levels above.
    unsafe fn climb(&self, level: usize, first: usize, n: usize, height: usize) {
        let (mut first, mut n) = (first, n);
        for j in level..level + height {
            // SAFETY: level `j` of the subtree is initialized, and level `j + 1` is ours to write.
            let (children, parents) = unsafe { (self.level_mut(j, first, n), self.level_mut(j + 1, first / 2, n / 2)) };
            hash_many::<{ 2 * OUT_LEN }>(digests_as_bytes(children), digests_as_bytes(parents));
            (first, n) = (first / 2, n / 2);
        }
    }

    /// The finished tree.
    ///
    /// # Safety
    ///
    /// Every node is written.
    unsafe fn assume_init(self) -> Vec<Hash> {
        // SAFETY: forwarded.
        unsafe { self.tree.into_boxed_slice().assume_init() }.into_vec()
    }
}

/// Which blocks arrived, and how many nodes of each unit above them are finished.
struct Progress {
    /// One flag per block, sized by the first block to arrive.
    blocks: OnceLock<Box<[AtomicBool]>>,
    /// Per level, one counter of finished nodes per unit.
    units: Box<[Box<[AtomicUsize]>]>,
    /// Leaves in the tree.
    num_leaves: usize,
}

impl Progress {
    /// No block arrived, and every counter at zero.
    fn new(num_leaves: usize) -> Self {
        let counters = |width: usize| (0..width.div_ceil(UNIT)).map(|_| AtomicUsize::new(0)).collect();
        Self {
            blocks: OnceLock::new(),
            units: (0..=num_leaves.ilog2()).map(|j| counters(num_leaves >> j)).collect(),
            num_leaves,
        }
    }

    /// Claim the block of `n` leaves at `first`.
    ///
    /// # Panics
    ///
    /// Panics unless the block is of power-of-two size, aligned, inside the tree, sized like every other, and new.
    fn claim(&self, first: usize, n: usize) {
        assert!(
            n.is_power_of_two() && first.is_multiple_of(n),
            "an aligned power-of-two block"
        );
        assert!(first + n <= self.num_leaves, "the block is inside the tree");
        let count = self.num_leaves / n;
        let blocks = self
            .blocks
            .get_or_init(|| (0..count).map(|_| AtomicBool::new(false)).collect());
        assert_eq!(blocks.len(), count, "blocks of one size");
        assert!(
            !blocks[first / n].swap(true, Ordering::AcqRel),
            "a block absorbed twice"
        );
    }

    /// Count `n` more finished nodes of unit `u` on `level`, true for the unit's last arrival.
    ///
    /// Why AcqRel: the last arrival sees every node the others wrote.
    fn arrive(&self, level: usize, u: usize, n: usize, unit: usize) -> bool {
        self.units[level][u].fetch_add(n, Ordering::AcqRel) + n == unit
    }

    /// Whether every block has arrived.
    fn all_claimed(&self) -> bool {
        self.blocks
            .get()
            .is_some_and(|b| b.iter().all(|f| f.load(Ordering::Acquire)))
    }
}

/// The words' little-endian byte image, which is how a leaf hashes them.
const fn words_as_bytes(words: &[F64]) -> &[u8] {
    const _: () = assert!(cfg!(target_endian = "little"), "a leaf hashes its words little-endian");
    // SAFETY: `F64` is `repr(transparent)` over `u64`, and the target is little-endian, so the bytes are the image.
    unsafe { std::slice::from_raw_parts(words.as_ptr().cast(), std::mem::size_of_val(words)) }
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

/// Hash each pair of children into its parent, all pairs together.
fn hash_pairs(pairs: &[[Hash; 2]]) -> Vec<Hash> {
    let mut parents = vec![[0u8; 32]; pairs.len()];
    hash_many::<{ 2 * OUT_LEN }>(pairs.as_flattened().as_flattened(), parents.as_flattened_mut());
    parents
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
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PrunedMerklePaths {
    pub leaf_data: Vec<Vec<F64>>,
    pub sibling_hashes: Vec<Hash>,
}

impl PrunedMerklePaths {
    /// The paths as a transcript hint: every row's words, then every sibling, all little-endian.
    ///
    /// No length is written: the verifier knows how many rows and how wide.
    #[must_use]
    pub fn to_hint(&self) -> Vec<u8> {
        let words = self.leaf_data.iter().flatten().flat_map(|w| w.0.to_le_bytes());
        words.chain(self.sibling_hashes.iter().flatten().copied()).collect()
    }

    /// The paths a hint holds, given its number of rows and their width in words.
    ///
    /// The siblings are the rest, whole digests.
    ///
    /// Returns nothing when the bytes do not split that way, so each paths value has one hint.
    #[must_use]
    pub fn from_hint(hint: &[u8], n_rows: usize, row_words: usize) -> Option<Self> {
        let (rows, siblings) = hint.split_at_checked(n_rows.checked_mul(row_words)?.checked_mul(8)?)?;
        let (words, []) = rows.as_chunks::<8>() else {
            unreachable!("the rows span whole words")
        };
        let (siblings, []) = siblings.as_chunks::<32>() else {
            return None;
        };
        let words: Vec<F64> = words.iter().map(|w| F64(u64::from_le_bytes(*w))).collect();
        Some(Self {
            leaf_data: words.chunks(row_words.max(1)).map(<[F64]>::to_vec).collect(),
            sibling_hashes: siblings.to_vec(),
        })
    }

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
        if self.leaf_data.iter().any(|row| row.len() != row_words) {
            return None;
        }
        // The rows, one after another, hashed as the committer hashed them: zero prefix shared, leaves batched.
        let bytes: Vec<u8> = (self.leaf_data.iter().flatten())
            .flat_map(|word| word.0.to_le_bytes())
            .collect();
        let mut hashes = Box::new_uninit_slice(self.leaf_data.len());
        LeafHasher::new(8 * row_words, 8 * leaf_words).hash(&bytes, &mut hashes);
        // SAFETY: the hasher wrote one digest per row.
        Some((sorted, unsafe { hashes.assume_init() }.into_vec()))
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
            nodes = parents.into_iter().zip(hash_pairs(&pairs)).collect();
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
#[derive(Clone, Debug, PartialEq, Eq)]
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

    impl MerkleBuilder {
        /// Absorb all rows, in parallel blocks.
        fn absorb_all(&self, data: &[u8]) {
            let num_leaves = self.nodes.width(0);
            assert_eq!(data.len(), num_leaves * self.leaves.row_bytes(), "one row per leaf");
            // Enough blocks for every worker, each at most one unit.
            let log_tasks = (4 * parallel::num_threads()).next_power_of_two().ilog2();
            let log_block = num_leaves.ilog2().saturating_sub(log_tasks).min(UNIT.ilog2());
            let block_bytes = self.leaves.row_bytes() << log_block;
            parallel::for_each(num_leaves >> log_block, |b| {
                self.absorb_bytes(b << log_block, &data[b * block_bytes..][..block_bytes]);
            });
        }
    }

    /// The tree over `num_leaves` rows of `row_words`, each hashed as `zeros(leaf_words - row_words) || row`.
    fn merkle_tree_padded_rows(data: &[F64], num_leaves: usize, row_words: usize, leaf_words: usize) -> Vec<Hash> {
        assert_eq!(data.len(), row_words * num_leaves);
        let builder = MerkleBuilder::new(num_leaves, row_words, leaf_words);
        builder.absorb_all(words_as_bytes(data));
        builder.finish()
    }

    /// The tree over `num_leaves` equal byte leaves, each hashed as plain BLAKE2s-256 of its bytes.
    fn merkle_tree(data: &[u8], num_leaves: usize) -> Vec<Hash> {
        let leaf_bytes = data.len() / num_leaves;
        let builder = MerkleBuilder::with_bytes(num_leaves, leaf_bytes, leaf_bytes);
        builder.absorb_all(data);
        builder.finish()
    }

    /// Per-leaf reference for the tree.
    fn merkle_tree_sequential(leaves: impl Iterator<Item = Hash>, num_leaves: usize) -> Vec<Hash> {
        let mut tree: Vec<Hash> = leaves.collect();
        assert_eq!(tree.len(), num_leaves);
        let (mut start, mut len) = (0, num_leaves);
        while len > 1 {
            for i in 0..len / 2 {
                tree.push(hash_pair(&tree[start + 2 * i], &tree[start + 2 * i + 1]));
            }
            (start, len) = (start + len, len / 2);
        }
        tree
    }

    #[test]
    fn byte_tree_matches_sequential() {
        // Leaf sizes cover every batched width in use, and ones with no whole block.
        //
        // Leaf counts cross the batch, the block, and the parallel top.
        for (num_leaves, leaf_size) in [
            (1usize, 32usize),
            (2, 48),
            (8, 32),
            (32, 64),
            (64, 128),
            (256, 192),
            (64, 256),
            (4096, 384),
            (4096, 512),
            (64, 1024),
            (8192, 16),
            (1 << 17, 64),
        ] {
            let data: Vec<u8> = (0..num_leaves * leaf_size)
                .map(|i| (i.wrapping_mul(131) ^ 0x5a) as u8)
                .collect();
            let want = merkle_tree_sequential(data.chunks(leaf_size).map(hash_leaf), num_leaves);
            assert_eq!(
                &merkle_tree(&data, num_leaves)[..],
                &want[..],
                "num_leaves={num_leaves} leaf_size={leaf_size}"
            );
        }
    }

    #[test]
    fn padded_rows_tree_matches_full_width() {
        // Invariant: each leaf hashes as its zero-extended row, however the prefix splits.
        for (num_leaves, row_words, leaf_words) in [
            // Nothing to pad.
            (8usize, 64usize, 64usize),
            (1024, 8, 8),
            // A shared prefix plus a partial block, staged.
            (2048, 37, 64),
            (256, 27, 64),
            (64, 1, 64),
            // A prefix of whole blocks: the rows are hashed where they lie.
            (256, 32, 64),
            (1 << 14, 56, 64),
            // A prefix shorter than one block: nothing shared, still staged.
            (32, 5, 8),
            (256, 61, 64),
            // 40-byte leaves: not whole blocks, hashed one at a time.
            (16, 3, 5),
        ] {
            let data: Vec<F64> = (0..row_words * num_leaves)
                .map(|i| F64(i.wrapping_mul(0x9E37_79B9_7F4A_7C15) as u64 | 1))
                .collect();
            let want = merkle_tree_sequential(
                data.chunks(row_words).map(|row| {
                    let mut image = vec![0u8; 8 * (leaf_words - row_words)];
                    image.extend_from_slice(words_as_bytes(row));
                    hash_leaf(&image)
                }),
                num_leaves,
            );
            assert_eq!(
                &merkle_tree_padded_rows(&data, num_leaves, row_words, leaf_words)[..],
                &want[..],
                "num_leaves={num_leaves} row_words={row_words} leaf_words={leaf_words}"
            );
        }
    }

    #[test]
    fn blocks_of_any_size_build_one_tree() {
        // Invariant: the tree does not depend on the block size the encoder picks.
        let (num_leaves, row_words) = (1usize << 12, 6usize);
        let data: Vec<F64> = (0..row_words * num_leaves).map(|i| F64(i as u64 * 7 + 1)).collect();
        let want = merkle_tree_padded_rows(&data, num_leaves, row_words, row_words);
        for log_block in [0usize, 3, 5, 6, 9, 12] {
            let builder = MerkleBuilder::new(num_leaves, row_words, row_words);
            // Blocks arrive out of order, as the encoder's tasks finish.
            for b in (0..num_leaves >> log_block).rev() {
                let rows = row_words << log_block;
                builder.absorb(b << log_block, &data[b * rows..][..rows]);
            }
            assert_eq!(&builder.finish()[..], &want[..], "log_block={log_block}");
        }
    }

    #[test]
    #[should_panic(expected = "every leaf absorbed")]
    fn a_missing_block_is_rejected() {
        let data = vec![F64::ZERO; 8 * 16];
        let builder = MerkleBuilder::new(16, 8, 8);
        builder.absorb(0, &data[..64]);
        let _ = builder.finish();
    }

    #[test]
    #[should_panic(expected = "a block absorbed twice")]
    fn a_repeated_block_is_rejected() {
        let data = vec![F64::ZERO; 8 * 16];
        let builder = MerkleBuilder::new(16, 8, 8);
        builder.absorb(8, &data[..64]);
        builder.absorb(8, &data[..64]);
    }

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
    fn a_hint_holds_exactly_one_paths_value() {
        // Fixture: three distinct rows of four words in a tree of eight leaves.
        let rows: Vec<Vec<F64>> = (0..8).map(|q| (0..4).map(|j| F64(q * 4 + j)).collect()).collect();
        let tree = tree_of(&rows);
        let paths = PrunedMerklePaths::prune(&tree, 8, &[5, 1, 3], |q| rows[q].clone());

        // The hint is the 3 * 4 words, then the siblings, nothing else.
        let hint = paths.to_hint();
        assert_eq!(hint.len(), 3 * 4 * 8 + 32 * paths.sibling_hashes.len());
        assert_eq!(PrunedMerklePaths::from_hint(&hint, 3, 4), Some(paths));

        // A byte short or over leaves a partial digest: no paths value.
        assert_eq!(PrunedMerklePaths::from_hint(&hint[1..], 3, 4), None);
        assert_eq!(
            PrunedMerklePaths::from_hint(&[hint.as_slice(), &[0]].concat(), 3, 4),
            None
        );
    }
}
