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
use primitives::hash::{BATCH, BLOCK_LEN, ChainingValue, OUT_LEN, hash_many};
use std::mem::MaybeUninit;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

/// A node of the tree: one BLAKE2s-256 digest.
pub type Hash = [u8; OUT_LEN];

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
pub(crate) struct LeafHasher(LeafShape);

/// The hashing plan for one leaf shape, chosen once.
enum LeafShape {
    /// The padding is whole blocks, so past the shared prefix each row is its own image, hashed where it lies.
    Direct {
        /// Bytes of a row.
        row_bytes: usize,
        /// The hash after the zero blocks.
        start: ChainingValue,
    },
    /// Some padding remains past the zero blocks, so rows are zero-extended in a tile first.
    ///
    /// The copy also aligns each image to whole cache lines, which the hasher's loads want.
    Staged {
        /// Bytes of a row.
        row_bytes: usize,
        /// Bytes of the image past the zero blocks: the remaining padding, then the row.
        image: usize,
        /// The hash after the zero blocks.
        start: ChainingValue,
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
    pub(crate) fn new(row_bytes: usize, leaf_bytes: usize) -> Self {
        assert!(0 < row_bytes && row_bytes <= leaf_bytes, "a leaf holds its row");
        if !leaf_bytes.is_multiple_of(BLOCK_LEN) {
            assert!(
                row_bytes == leaf_bytes || leaf_bytes <= STAGE_TILE_BYTES,
                "a padded leaf fits the tile"
            );
            return Self(LeafShape::Single { row_bytes, leaf_bytes });
        }
        let zero_blocks = (leaf_bytes - row_bytes) / BLOCK_LEN;
        let start = ChainingValue::zero_prefix(zero_blocks);
        let image = leaf_bytes - zero_blocks * BLOCK_LEN;
        if image == row_bytes {
            Self(LeafShape::Direct { row_bytes, start })
        } else {
            assert!(image <= STAGE_TILE_BYTES, "a padded leaf fits the tile");
            Self(LeafShape::Staged {
                row_bytes,
                image,
                start,
            })
        }
    }

    /// Bytes of a row.
    pub(crate) const fn row_bytes(&self) -> usize {
        match self.0 {
            LeafShape::Direct { row_bytes, .. }
            | LeafShape::Staged { row_bytes, .. }
            | LeafShape::Single { row_bytes, .. } => row_bytes,
        }
    }

    /// Hash one leaf per row into `out`.
    pub(crate) fn hash(&self, rows: &[u8], out: &mut [MaybeUninit<Hash>]) {
        match self.0 {
            LeafShape::Direct { row_bytes, start } => {
                start.hash_many(rows, row_bytes, digests_as_bytes(out));
            }
            LeafShape::Staged {
                row_bytes,
                image,
                start,
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
                    start.hash_many(images, image, digests_as_bytes(out));
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
    pub(crate) fn finish(self) -> MerkleTree {
        assert!(self.progress.all_claimed(), "every leaf absorbed");
        // SAFETY: every block was absorbed once, and the last arrivals climbed every level above the blocks.
        MerkleTree(unsafe { self.nodes.assume_init() })
    }
}

/// A finished Merkle tree over a power of two of leaves.
///
/// Its nodes are stored level after level from the leaves, the root last.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MerkleTree(Vec<Hash>);

impl MerkleTree {
    /// The root.
    pub(crate) fn root(&self) -> Hash {
        *self.0.last().expect("a tree has a root")
    }

    /// The number of leaves.
    pub(crate) const fn num_leaves(&self) -> usize {
        self.0.len().div_ceil(2)
    }

    /// Open `positions`: one row per distinct position, and one octopus authenticating them all.
    ///
    /// - `row(q)` is the leaf at position `q`.
    /// - The octopus holds every sibling no queried subtree supplies.
    ///
    /// A sibling shared by several paths is stored once.
    /// So `q` queries in a tree of depth `d` store at most `q d` digests, what `q` independent paths would.
    pub(crate) fn prune<R: AsRef<[F64]>>(&self, positions: &[usize], row: impl Fn(usize) -> R) -> PrunedMerklePaths {
        let num_leaves = self.num_leaves();
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
                // Both children active: they fold into the same parent, so no sibling is needed.
                // Otherwise the sibling has to be sent.
                if i + 1 < active.len() && active[i + 1] == (p ^ 1) {
                    i += 2;
                } else {
                    sibling_hashes.push(self.0[level_start + (p ^ 1)]);
                    i += 1;
                }
                next.push(p >> 1);
            }
            // `next` stays sorted and unique: sibling pairs collapse to one parent, and `p >> 1` is otherwise increasing.
            active = next;
            level_start += level_len;
            level_len >>= 1;
        }

        // The distinct rows, one after another.
        let mut rows = Vec::new();
        for &q in &sorted {
            rows.extend_from_slice(row(q).as_ref());
        }
        PrunedMerklePaths { rows, sibling_hashes }
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
    #[expect(
        clippy::mut_from_ref,
        reason = "the nodes are written through a shared base pointer at disjoint ranges"
    )]
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

/// Hash each pair of children into its parent, all pairs together, into `parents`.
fn hash_pairs(pairs: &[[Hash; 2]], parents: &mut Vec<Hash>) {
    parents.clear();
    parents.resize(pairs.len(), [0; 32]);
    hash_many::<{ 2 * OUT_LEN }>(pairs.as_flattened().as_flattened(), parents.as_flattened_mut());
}

/// Query positions with duplicates removed, ascending.
///
/// It is the order a phase stores its rows in, and the order its octopus is built and checked against.
pub(crate) fn sorted_unique(queries: &[usize]) -> Vec<usize> {
    let mut unique = queries.to_vec();
    unique.sort_unstable();
    unique.dedup();
    unique
}

/// Each of the `n` rows' leaf digest, in order: rows of `row_words` words one after another, each hashed as its leaf image of `leaf_words` words, the missing words a zero prefix.
///
/// # Panics
///
/// Panics unless `0 < row_words <= leaf_words`, as [`LeafHasher::new`] does.
fn hash_rows(rows: &[F64], n: usize, row_words: usize, leaf_words: usize) -> Vec<Hash> {
    let mut leaf_hashes = Box::new_uninit_slice(n);
    LeafHasher::new(8 * row_words, 8 * leaf_words).hash(words_as_bytes(rows), &mut leaf_hashes);
    // SAFETY: the hasher wrote one digest per row.
    unsafe { leaf_hashes.assume_init() }.into_vec()
}

/// A node of the octopus rebuild: its index within its level, and its digest.
type Node = (usize, Hash);

/// One level of the octopus rebuild: pair each of `nodes` (ascending by index) with its sibling.
///
/// The sibling is the next node when that is the sibling, else the next supplied sibling from `siblings[used..]`.
/// Leaves each pair's parent index in `parents` and its children in `pairs`, and appends both children with their indices to `known`.
/// Returns how many siblings are used after this level, or nothing when the supplied siblings run out.
fn pair_level(
    nodes: &[Node],
    siblings: &[Hash],
    mut used: usize,
    parents: &mut Vec<usize>,
    pairs: &mut Vec<[Hash; 2]>,
    known: &mut Vec<Node>,
) -> Option<usize> {
    parents.clear();
    pairs.clear();
    let mut i = 0;
    while i < nodes.len() {
        let idx = nodes[i].0;
        let parent = idx >> 1;
        let paired = idx & 1 == 0 && i + 1 < nodes.len() && nodes[i + 1].0 == idx + 1;
        let (left, right) = if paired {
            (nodes[i].1, nodes[i + 1].1)
        } else if used == siblings.len() {
            return None;
        } else if idx & 1 == 0 {
            used += 1;
            (nodes[i].1, siblings[used - 1])
        } else {
            used += 1;
            (siblings[used - 1], nodes[i].1)
        };
        parents.push(parent);
        pairs.push([left, right]);
        known.push((2 * parent, left));
        known.push((2 * parent + 1, right));
        i += if paired { 2 } else { 1 };
    }
    Some(used)
}

/// Rebuild every node on the queried paths bottom-up from the `leaves` (ascending by index).
///
/// A stored sibling is pulled only where it is not itself a queried subtree.
/// Returns every level's known nodes in one buffer, level `l` at `starts[l]..starts[l + 1]` (both children of each parent, ascending by index), and `starts`.
/// Returns nothing when the siblings run out or are left over, or the last fold is not `root`.
fn rebuild(mut nodes: Vec<Node>, siblings: &[Hash], height: usize, root: &Hash) -> Option<(Vec<Node>, Vec<usize>)> {
    let mut used = 0;
    let mut known: Vec<Node> = Vec::new();
    let mut starts = Vec::with_capacity(height + 1);
    let (mut parents, mut pairs, mut digests) = (Vec::new(), Vec::new(), Vec::new());
    let mut level = 0;
    while level < height {
        starts.push(known.len());
        used = pair_level(&nodes, siblings, used, &mut parents, &mut pairs, &mut known)?;
        hash_pairs(&pairs, &mut digests);
        next_nodes(&parents, &digests, &mut nodes);
        level += 1;
    }
    starts.push(known.len());
    // The last fold leaves exactly the root, and nothing may be left over.
    if used < siblings.len() || nodes.is_empty() || nodes[0].1 != *root {
        return None;
    }
    Some((known, starts))
}

/// Each query's image and path, in query order.
///
/// The image is the query's row of `rows` (stored at its position in `sorted`) after a zero prefix, the path its sibling at every level of `known`.
fn expand(
    rows: &[F64],
    sorted: &[usize],
    known: &[Node],
    starts: &[usize],
    queries: &[usize],
    row_words: usize,
    leaf_words: usize,
) -> Option<Openings> {
    let height = starts.len() - 1;
    let mut openings = Openings {
        leaf_words,
        height,
        images: vec![F64::ZERO; queries.len() * leaf_words],
        paths: Vec::with_capacity(queries.len() * height),
    };
    let mut k = 0;
    while k < queries.len() {
        let q = queries[k];
        // The query's row is the image's tail, after the zero prefix.
        let slot = position(sorted, q)?;
        let image = (k + 1) * leaf_words;
        openings.images[image - row_words..image].copy_from_slice(&rows[slot * row_words..(slot + 1) * row_words]);

        // Its sibling at each level is a known node of that level.
        if !push_path(known, starts, q, &mut openings.paths) {
            return None;
        }
        k += 1;
    }
    Some(openings)
}

/// The next level's nodes: each parent index with its digest, replacing `nodes`.
fn next_nodes(parents: &[usize], digests: &[Hash], nodes: &mut Vec<Node>) {
    nodes.clear();
    let mut p = 0;
    while p < parents.len() {
        nodes.push((parents[p], digests[p]));
        p += 1;
    }
}

/// Where `key` sits in `sorted`, ascending without duplicates, if it does.
const fn position(sorted: &[usize], key: usize) -> Option<usize> {
    let (mut lo, mut hi) = (0, sorted.len());
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if sorted[mid] == key {
            return Some(mid);
        }
        if sorted[mid] < key {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    None
}

/// Where the node of index `key` sits in `level`, ascending by index without duplicates, if it does.
const fn node_position(level: &[Node], key: usize) -> Option<usize> {
    let (mut lo, mut hi) = (0, level.len());
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if level[mid].0 == key {
            return Some(mid);
        }
        if level[mid].0 < key {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    None
}

/// Push query `q`'s sibling at every level of `known` (level `l` at `starts[l]..starts[l + 1]`), lowest first.
///
/// Returns whether every level holds the sibling.
fn push_path(known: &[Node], starts: &[usize], q: usize, paths: &mut Vec<Hash>) -> bool {
    let mut lvl = 0;
    while lvl + 1 < starts.len() {
        let level = &known[starts[lvl]..starts[lvl + 1]];
        let node = q >> lvl;
        let sibling = if node & 1 == 0 { node + 1 } else { node - 1 };
        match node_position(level, sibling) {
            Some(pos) => paths.push(level[pos].1),
            None => return false,
        }
        lvl += 1;
    }
    true
}

/// The little-endian word at `hint[at..at + 8]`.
const fn word_at(hint: &[u8], at: usize) -> u64 {
    u64::from_le_bytes([
        hint[at],
        hint[at + 1],
        hint[at + 2],
        hint[at + 3],
        hint[at + 4],
        hint[at + 5],
        hint[at + 6],
        hint[at + 7],
    ])
}

/// One opening phase's Merkle data: the rows at each distinct queried position, ascending, and one octopus over them.
///
/// - A row is words of `K`, what a Merkle preimage is; a row of `w` elements of `E` is `3w` words.
/// - The phase never says how wide a row is: the caller announces it, which pins the leaf image the octopus checks.
/// - A row may be narrower than the image it hashes to, the missing words a zero prefix the caller also announces.
///
/// That prefix is what keeps an L0 commitment's absent lanes out of the proof.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct PrunedMerklePaths {
    /// The distinct rows, ascending by position, one after another.
    pub rows: Vec<F64>,
    /// The octopus: every sibling no queried subtree supplies, bottom level first.
    pub sibling_hashes: Vec<Hash>,
}

impl PrunedMerklePaths {
    /// The paths as a transcript hint: every row's words, then every sibling, all little-endian.
    ///
    /// No length is written: the verifier knows how many rows and how wide.
    #[must_use]
    pub(crate) fn to_hint(&self) -> Vec<u8> {
        let mut hint = Vec::with_capacity(8 * self.rows.len() + 32 * self.sibling_hashes.len());
        for word in &self.rows {
            hint.extend_from_slice(&word.0.to_le_bytes());
        }
        hint.extend_from_slice(self.sibling_hashes.as_flattened());
        hint
    }

    /// The paths a hint holds, given its number of rows and their width in words.
    ///
    /// The siblings are the rest, whole digests.
    ///
    /// Returns nothing when the bytes do not split that way, so each paths value has one hint.
    #[must_use]
    pub(crate) fn from_hint(hint: &[u8], n_rows: usize, row_words: usize) -> Option<Self> {
        let n_words = n_rows.checked_mul(row_words)?;
        let row_bytes = n_words.checked_mul(8)?;
        if hint.len() < row_bytes || !(hint.len() - row_bytes).is_multiple_of(32) {
            return None;
        }
        let mut rows = Vec::with_capacity(n_words);
        let mut i = 0;
        while i < n_words {
            rows.push(F64(word_at(hint, 8 * i)));
            i += 1;
        }
        let n_siblings = (hint.len() - row_bytes) / 32;
        let mut sibling_hashes = Vec::with_capacity(n_siblings);
        let mut j = 0;
        while j < n_siblings {
            let mut digest = [0u8; 32];
            digest.copy_from_slice(&hint[row_bytes + 32 * j..row_bytes + 32 * (j + 1)]);
            sibling_hashes.push(digest);
            j += 1;
        }
        Some(Self { rows, sibling_hashes })
    }

    /// Authenticate this phase against `root`, and expand it into one opening per query, in query order.
    ///
    /// - It is the one way to consume a phase, so no row is read before the Merkle check runs.
    /// - Rebuilding every node on the queried paths recomputes the root and yields each query's full sibling path.
    /// - So the pruned form is checked and the unpruned form produced in one walk.
    ///
    /// # Returns
    ///
    /// Nothing on a wrong row count or width, an out-of-range query, a wrong sibling count, or another root.
    pub(crate) fn open(
        &self,
        root: &Hash,
        num_leaves: usize,
        queries: &[usize],
        row_words: usize,
        leaf_words: usize,
    ) -> Option<Openings> {
        if !num_leaves.is_power_of_two() || num_leaves == 0 || queries.is_empty() || row_words > leaf_words {
            return None;
        }
        let height = num_leaves.trailing_zeros() as usize;
        let sorted = sorted_unique(queries);
        if sorted[sorted.len() - 1] >= num_leaves || self.rows.len() != sorted.len() * row_words {
            return None;
        }

        // The rows, one after another, hashed as the committer hashed them: zero prefix shared, leaves batched.
        let leaf_hashes = hash_rows(&self.rows, sorted.len(), row_words, leaf_words);
        let mut leaves: Vec<Node> = Vec::with_capacity(sorted.len());
        let mut i = 0;
        while i < sorted.len() {
            leaves.push((sorted[i], leaf_hashes[i]));
            i += 1;
        }
        let (known, starts) = rebuild(leaves, &self.sibling_hashes, height, root)?;
        expand(&self.rows, &sorted, &known, &starts, queries, row_words, leaf_words)
    }
}

/// A phase's openings, unpruned and in query order: each query's full leaf image and full sibling path.
///
/// Several queries repeat the siblings they share, which is what makes each one simple to consume:
/// recomputing the root is a walk up one path.
///
/// All images sit in one buffer and all paths in another, so a phase costs a fixed number of allocations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Openings {
    /// Words of a leaf image.
    pub leaf_words: usize,
    /// Siblings on a path: the tree's height.
    pub height: usize,
    /// The images, one after another, each with its zero prefix.
    pub images: Vec<F64>,
    /// The paths, one after another, each lowest sibling first.
    pub paths: Vec<Hash>,
}

impl Openings {
    /// The number of queries opened.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.images.len() / self.leaf_words
    }

    /// Whether no query was opened.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.images.is_empty()
    }

    /// Query `i`'s full leaf image, its zero prefix included.
    #[must_use]
    pub fn image(&self, i: usize) -> &[F64] {
        &self.images[i * self.leaf_words..][..self.leaf_words]
    }

    /// Each query's row: its leaf image with the zero prefix dropped, the last `row_words` words.
    #[must_use]
    pub fn rows(&self, row_words: usize) -> Vec<Vec<F64>> {
        // An index loop rather than a mapping closure.
        let n = self.len();
        let mut rows = Vec::with_capacity(n);
        let mut i = 0;
        while i < n {
            rows.push(self.image(i)[self.leaf_words - row_words..].to_vec());
            i += 1;
        }
        rows
    }

    /// Query `i`'s siblings, lowest first.
    #[must_use]
    pub fn path(&self, i: usize) -> &[Hash] {
        &self.paths[i * self.height..][..self.height]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Absorb all rows into `builder`, in parallel blocks.
    fn absorb_all(builder: &MerkleBuilder, data: &[u8]) {
        let num_leaves = builder.nodes.width(0);
        assert_eq!(data.len(), num_leaves * builder.leaves.row_bytes(), "one row per leaf");
        // Enough blocks for every worker, each at most one unit.
        let log_tasks = (4 * parallel::num_threads()).next_power_of_two().ilog2();
        let log_block = num_leaves.ilog2().saturating_sub(log_tasks).min(UNIT.ilog2());
        let block_bytes = builder.leaves.row_bytes() << log_block;
        parallel::for_each(num_leaves >> log_block, |b| {
            builder.absorb_bytes(b << log_block, &data[b * block_bytes..][..block_bytes]);
        });
    }

    /// The tree over `num_leaves` rows of `row_words`, each hashed as `zeros(leaf_words - row_words) || row`.
    fn merkle_tree_padded_rows(data: &[F64], num_leaves: usize, row_words: usize, leaf_words: usize) -> MerkleTree {
        assert_eq!(data.len(), row_words * num_leaves);
        let builder = MerkleBuilder::new(num_leaves, row_words, leaf_words);
        absorb_all(&builder, words_as_bytes(data));
        builder.finish()
    }

    /// The tree over `num_leaves` equal byte leaves, each hashed as plain BLAKE2s-256 of its bytes.
    fn merkle_tree(data: &[u8], num_leaves: usize) -> MerkleTree {
        let leaf_bytes = data.len() / num_leaves;
        let builder = MerkleBuilder::with_bytes(num_leaves, leaf_bytes, leaf_bytes);
        absorb_all(&builder, data);
        builder.finish()
    }

    /// The tree over these leaf digests, one parent at a time: the reference the builder is checked against.
    fn merkle_tree_sequential(leaves: impl Iterator<Item = Hash>) -> MerkleTree {
        let mut tree: Vec<Hash> = leaves.collect();
        let (mut start, mut len) = (0, tree.len());
        while len > 1 {
            for i in 0..len / 2 {
                tree.push(hash_pair(&tree[start + 2 * i], &tree[start + 2 * i + 1]));
            }
            (start, len) = (start + len, len / 2);
        }
        MerkleTree(tree)
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
            let want = merkle_tree_sequential(data.chunks(leaf_size).map(hash_leaf));
            assert_eq!(
                merkle_tree(&data, num_leaves),
                want,
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
            let want = merkle_tree_sequential(data.chunks(row_words).map(|row| {
                let mut image = vec![0u8; 8 * (leaf_words - row_words)];
                image.extend_from_slice(words_as_bytes(row));
                hash_leaf(&image)
            }));
            assert_eq!(
                merkle_tree_padded_rows(&data, num_leaves, row_words, leaf_words),
                want,
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
            assert_eq!(builder.finish(), want, "log_block={log_block}");
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

    /// A leaf's hash: its words' little-endian bytes.
    fn hash_words(image: &[F64]) -> Hash {
        hash_leaf(&image.iter().flat_map(|w| w.0.to_le_bytes()).collect::<Vec<u8>>())
    }

    /// The root a leaf image and its path reach, the direction at each level the index's bit.
    fn walk(image: &[F64], path: &[Hash], index: usize) -> Hash {
        (path.iter().enumerate()).fold(hash_words(image), |acc, (lvl, sibling)| {
            if index >> lvl & 1 == 0 {
                hash_pair(&acc, sibling)
            } else {
                hash_pair(sibling, &acc)
            }
        })
    }

    /// The tree whose leaves are these rows' words.
    fn tree_of(rows: &[Vec<F64>]) -> MerkleTree {
        merkle_tree_sequential(rows.iter().map(|r| hash_words(r)))
    }

    #[test]
    fn prune_open_roundtrip() {
        let (num_leaves, width, height) = (8usize, 4usize, 3usize);
        let rows: Vec<Vec<F64>> = (0..num_leaves)
            .map(|q| (0..width).map(|j| F64((q * width + j) as u64)).collect())
            .collect();
        let tree = tree_of(&rows);
        let root = tree.root();
        let queries = [5usize, 1, 5, 3, 1];

        let paths = tree.prune(&queries, |q| rows[q].clone());
        assert_eq!(paths.rows.len(), 3 * width, "one row per distinct query");

        let openings = paths.open(&root, num_leaves, &queries, width, width).expect("open");
        assert_eq!(openings.len(), queries.len());
        for (i, &q) in queries.iter().enumerate() {
            assert_eq!(openings.image(i), rows[q], "row must follow query order");
            assert_eq!(openings.path(i).len(), height);
            assert_eq!(
                walk(openings.image(i), openings.path(i), q),
                root,
                "each unpruned path must reach the root"
            );
        }
    }

    #[test]
    fn malformed_phases_are_rejected() {
        let (num_leaves, width) = (8usize, 4usize);
        let rows: Vec<Vec<F64>> = (0..num_leaves)
            .map(|q| (0..width).map(|j| F64((q * width + j) as u64)).collect())
            .collect();
        let tree = tree_of(&rows);
        let root = tree.root();
        let queries = [5usize, 1, 3];
        let good = tree.prune(&queries, |q| rows[q].clone());
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
        bad_row.rows[0].0 ^= 1;
        assert!(open(&bad_row, &queries, width, num_leaves).is_none(), "tampered row");

        let mut wide = good.clone();
        wide.rows.push(F64(0));
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
        let paths = tree.prune(&[5, 1, 3], |q| rows[q].clone());

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
