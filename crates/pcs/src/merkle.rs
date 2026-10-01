// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Binary Merkle tree with BLAKE2s, built in cache-resident subtree blocks.
//!
//! The committer's half. What a proof carries lives in [`fiat_shamir::merkle`].
//!
//! Layout for `n = 2^k` leaves, level `j` counted from the leaves:
//!
//! ```text
//!     tree[0 .. n]                  level 0, the leaf digests
//!     tree[n .. 3n/2]               level 1
//!     ...
//!     tree[2n - 2]                  the root
//! ```
//!
//! A node depends only on the aligned run of leaves below it.
//!
//! So one task hashes a block of leaves and climbs its subtree while the digests are in L1.
//!
//! The encoder hands blocks over as it finishes them, so leaves are hashed while the rows are in L2.
//!
//! Above the blocks, the last block to finish a unit of nodes climbs it, so no pass waits on a barrier.

use std::mem::MaybeUninit;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

pub use fiat_shamir::merkle::{Hash, hash_leaf, hash_pair};
use parallel::SendPtr;
use primitives::field::F64;
use primitives::hash::{BATCH, BLOCK_LEN, OUT_LEN, hash_many, hash_many_dyn_from_state, zero_prefix_state};
use zk_alloc::ArenaVec;

/// Nodes one climb takes at most: 32 KiB of digests, which stay in L1.
const UNIT: usize = 1 << 10;

/// Staging tile for leaves whose zero padding does not end on a block boundary.
const STAGE_TILE_BYTES: usize = 16 << 10;

/// A Merkle tree filled one aligned block of leaves at a time, from any thread.
///
/// Leaf `i` is `zeros(leaf_words - row_words) ‖ row_i`.
///
/// Blocks must all have the same power-of-two size, and together cover every leaf once.
pub struct MerkleBuilder {
    nodes: Nodes,
    leaves: LeafHasher,
    progress: Progress,
}

impl MerkleBuilder {
    /// An empty tree of `num_leaves` leaves of `leaf_words`, each committing `row_words`.
    pub fn new(num_leaves: usize, row_words: usize, leaf_words: usize) -> Self {
        Self::with_bytes(num_leaves, 8 * row_words, 8 * leaf_words)
    }

    fn with_bytes(num_leaves: usize, row_bytes: usize, leaf_bytes: usize) -> Self {
        assert!(num_leaves.is_power_of_two(), "num_leaves must be power of 2");
        Self {
            nodes: Nodes::new(num_leaves),
            leaves: LeafHasher::new(row_bytes, leaf_bytes),
            progress: Progress::new(num_leaves),
        }
    }

    /// Hash the leaves `first_leaf ..` of the rows in `rows`, and climb their subtree.
    ///
    /// # Panics
    ///
    /// Panics unless the block is aligned, sized like every other, and new.
    pub fn absorb(&self, first_leaf: usize, rows: &[F64]) {
        self.absorb_bytes(first_leaf, words_as_bytes(rows));
    }

    fn absorb_bytes(&self, first_leaf: usize, rows: &[u8]) {
        let n = rows.len() / self.leaves.row_bytes();
        assert_eq!(rows.len(), n * self.leaves.row_bytes(), "whole rows");
        self.progress.claim(first_leaf, n);
        // SAFETY: the claim makes these leaves, and their subtree up to the unit, ours alone.
        unsafe {
            self.leaves.hash(rows, self.nodes.level_mut(0, first_leaf, n));
            self.complete(0, first_leaf, n);
        }
    }

    /// Climb `n` finished nodes of `level` from node `first`, then hand them to their unit.
    ///
    /// The unit's last arrival climbs the unit in turn, up to the root.
    ///
    /// # Safety
    ///
    /// The nodes are initialized, and no other caller holds them.
    unsafe fn complete(&self, level: usize, first: usize, n: usize) {
        if n == self.nodes.width(level) {
            // SAFETY: forwarded, and the whole level climbs to the root.
            return unsafe { self.nodes.climb(level, 0, n, n.ilog2() as usize) };
        }
        // Climb while every level still fills whole batches.
        let height = (n / BATCH).max(1).ilog2() as usize;
        // SAFETY: forwarded.
        unsafe { self.nodes.climb(level, first, n, height) };
        let (level, first, n) = (level + height, first >> height, n >> height);

        let unit = UNIT.min(self.nodes.width(level));
        if self.progress.arrive(level, first / unit, n, unit) {
            // SAFETY: every node of the unit is written, and only its last arrival gets here.
            unsafe { self.complete(level, first - first % unit, unit) };
        }
    }

    /// Absorb all rows, in parallel blocks.
    #[cfg(test)]
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

    /// The finished tree.
    ///
    /// # Panics
    ///
    /// Panics unless every leaf was absorbed.
    pub fn finish(self) -> ArenaVec<Hash> {
        assert!(self.progress.all_claimed(), "every leaf absorbed");
        // SAFETY: every block was absorbed once, and the last arrivals climbed every level above.
        unsafe { self.nodes.assume_init() }
    }
}

/// The flat tree, written at disjoint nodes by concurrent climbs.
struct Nodes {
    tree: ArenaVec<MaybeUninit<Hash>>,
    base: SendPtr<MaybeUninit<Hash>>,
    num_leaves: usize,
}

impl Nodes {
    fn new(num_leaves: usize) -> Self {
        let mut tree = zk_alloc::alloc_uninit(2 * num_leaves - 1);
        let base = SendPtr(tree.as_mut_ptr());
        Self { tree, base, num_leaves }
    }

    /// Nodes on `level`.
    fn width(&self, level: usize) -> usize {
        self.num_leaves >> level
    }

    /// Index of `level`'s first node.
    fn start(&self, level: usize) -> usize {
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
    /// The nodes are initialized, and nothing else touches their subtree.
    unsafe fn climb(&self, level: usize, first: usize, n: usize, height: usize) {
        let (mut first, mut n) = (first, n);
        for j in level..level + height {
            // SAFETY: level `j` of the subtree is initialized, and level `j + 1` is ours to write.
            let (children, parents) = unsafe { (self.level_mut(j, first, n), self.level_mut(j + 1, first / 2, n / 2)) };
            hash_many::<{ 2 * OUT_LEN }>(digests_as_bytes(children), digests_as_bytes(parents));
            (first, n) = (first / 2, n / 2);
        }
    }

    /// # Safety
    ///
    /// Every node is written.
    unsafe fn assume_init(self) -> ArenaVec<Hash> {
        // SAFETY: forwarded.
        unsafe { zk_alloc::assume_init(self.tree) }
    }
}

/// Which blocks arrived, and how many nodes of each unit above them are finished.
struct Progress {
    /// One flag per block, sized by the first block to arrive.
    blocks: OnceLock<Box<[AtomicBool]>>,
    /// Per level, one counter per unit.
    units: Box<[Box<[AtomicUsize]>]>,
    num_leaves: usize,
}

impl Progress {
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
    /// Panics unless the block is aligned, sized like every other, and new.
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
    /// AcqRel: the last arrival sees every node the others wrote.
    fn arrive(&self, level: usize, u: usize, n: usize, unit: usize) -> bool {
        self.units[level][u].fetch_add(n, Ordering::AcqRel) + n == unit
    }

    fn all_claimed(&self) -> bool {
        self.blocks
            .get()
            .is_some_and(|b| b.iter().all(|f| f.load(Ordering::Acquire)))
    }
}

/// How rows become leaf digests, chosen once from the leaf shape.
///
/// Whole blocks of leading zeros are one chaining value, absorbed once for every leaf.
enum LeafHasher {
    /// Past the shared prefix, each row is its own whole-block image.
    Direct {
        row_bytes: usize,
        state: [u32; 8],
        t_offset: u64,
    },
    /// The rest of the padding does not fill a block, so rows are zero-extended in a tile first.
    ///
    /// The copy also aligns each image to whole cache lines, which the hasher's loads want.
    Staged {
        row_bytes: usize,
        image: usize,
        state: [u32; 8],
        t_offset: u64,
    },
    /// Leaves of no whole block: one at a time, zero-extended to `leaf_bytes`.
    Single { row_bytes: usize, leaf_bytes: usize },
}

impl LeafHasher {
    fn new(row_bytes: usize, leaf_bytes: usize) -> Self {
        assert!(0 < row_bytes && row_bytes <= leaf_bytes, "a leaf holds its row");
        if !leaf_bytes.is_multiple_of(BLOCK_LEN) {
            assert!(
                row_bytes == leaf_bytes || leaf_bytes <= STAGE_TILE_BYTES,
                "a padded leaf fits the tile"
            );
            return Self::Single { row_bytes, leaf_bytes };
        }
        let zero_blocks = (leaf_bytes - row_bytes) / BLOCK_LEN;
        let (state, t_offset) = (zero_prefix_state(zero_blocks), (zero_blocks * BLOCK_LEN) as u64);
        let image = leaf_bytes - zero_blocks * BLOCK_LEN;
        if image == row_bytes {
            Self::Direct {
                row_bytes,
                state,
                t_offset,
            }
        } else {
            assert!(image <= STAGE_TILE_BYTES, "a padded leaf fits the tile");
            Self::Staged {
                row_bytes,
                image,
                state,
                t_offset,
            }
        }
    }

    fn row_bytes(&self) -> usize {
        match *self {
            Self::Direct { row_bytes, .. } | Self::Staged { row_bytes, .. } | Self::Single { row_bytes, .. } => {
                row_bytes
            }
        }
    }

    /// Hash one leaf per row into `out`.
    fn hash(&self, rows: &[u8], out: &mut [MaybeUninit<Hash>]) {
        match *self {
            Self::Direct {
                row_bytes,
                state,
                t_offset,
            } => {
                hash_many_dyn_from_state(rows, row_bytes, &state, t_offset, digests_as_bytes(out));
            }
            Self::Staged {
                row_bytes,
                image,
                state,
                t_offset,
            } => {
                // Whole batches per tile.
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
            Self::Single { row_bytes, leaf_bytes } if row_bytes == leaf_bytes => {
                for (slot, row) in out.iter_mut().zip(rows.chunks_exact(row_bytes)) {
                    slot.write(hash_leaf(row));
                }
            }
            Self::Single { row_bytes, leaf_bytes } => {
                let mut tile = Tile::new();
                for (slot, row) in out.iter_mut().zip(rows.chunks_exact(row_bytes)) {
                    slot.write(hash_leaf(tile.extend(row, row_bytes, leaf_bytes)));
                }
            }
        }
    }
}

/// A zeroed staging buffer.
struct Tile([u64; STAGE_TILE_BYTES / 8]);

impl Tile {
    fn new() -> Self {
        Self([0; STAGE_TILE_BYTES / 8])
    }

    /// Lay each `row_bytes` row at the end of its own `image`-byte slot, and return the slots.
    ///
    /// The bytes before each row are never written, so they stay zero.
    fn extend(&mut self, rows: &[u8], row_bytes: usize, image: usize) -> &[u8] {
        // SAFETY: any byte pattern is a u64.
        let tile: &mut [u8] = unsafe { std::slice::from_raw_parts_mut(self.0.as_mut_ptr().cast(), STAGE_TILE_BYTES) };
        let n = rows.len() / row_bytes;
        for (slot, row) in tile.chunks_exact_mut(image).zip(rows.chunks_exact(row_bytes)) {
            slot[image - row_bytes..].copy_from_slice(row);
        }
        &tile[..n * image]
    }
}

fn words_as_bytes(words: &[F64]) -> &[u8] {
    // SAFETY: F64 is repr(transparent) over u64, so on this LE target the slice is its words' byte image.
    unsafe { std::slice::from_raw_parts(words.as_ptr().cast(), std::mem::size_of_val(words)) }
}

fn digests_as_bytes(out: &mut [MaybeUninit<Hash>]) -> &mut [u8] {
    // SAFETY: a digest is 32 bytes with no padding, and the hasher only writes.
    unsafe { std::slice::from_raw_parts_mut(out.as_mut_ptr().cast(), out.len() * OUT_LEN) }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The tree over `num_leaves` rows of `row_words`, each hashed as `zeros(leaf_words - row_words) ‖ row`.
    fn merkle_tree_padded_rows(data: &[F64], num_leaves: usize, row_words: usize, leaf_words: usize) -> ArenaVec<Hash> {
        assert_eq!(data.len(), row_words * num_leaves);
        let builder = MerkleBuilder::new(num_leaves, row_words, leaf_words);
        builder.absorb_all(words_as_bytes(data));
        builder.finish()
    }

    /// The tree over `num_leaves` equal byte leaves, each hashed as plain BLAKE2s-256 of its bytes.
    fn merkle_tree(data: &[u8], num_leaves: usize) -> ArenaVec<Hash> {
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
}
