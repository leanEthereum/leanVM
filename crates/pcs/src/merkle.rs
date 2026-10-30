// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Binary Merkle tree with Keccak-256, built in cache-resident subtree blocks.
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

pub use fiat_shamir::merkle::{Hash, PrunedMerklePaths, hash_leaf, hash_pair};
use parallel::SendPtr;
use primitives::field::F64;
use primitives::hash::{LANES, OUT_LEN, RATE, STATE_LANES, hash_many, hash_many_from_state, zero_prefix_state};
use primitives::{cast_slice, cast_slice_mut};

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
    /// Levels below it are never stored: see [`CutTree`].
    cut: usize,
    leaves: LeafHasher,
    progress: Progress,
}

impl MerkleBuilder {
    /// An empty tree of `num_leaves` leaves of `leaf_words`, each committing `row_words`.
    ///
    /// A tree of `CUT_FROM` leaves or more is cut, so its blocks must hold whole leaf groups.
    pub fn new(num_leaves: usize, row_words: usize, leaf_words: usize) -> Self {
        let cut = if num_leaves >= CUT_FROM { CUT } else { 0 };
        Self::with_bytes(num_leaves, 8 * row_words, 8 * leaf_words, cut)
    }

    fn with_bytes(num_leaves: usize, row_bytes: usize, leaf_bytes: usize, cut: usize) -> Self {
        assert!(num_leaves.is_power_of_two(), "num_leaves must be power of 2");
        Self {
            nodes: Nodes::new(num_leaves, cut),
            cut,
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
        self.absorb_bytes(first_leaf, cast_slice(rows));
    }

    fn absorb_bytes(&self, first_leaf: usize, rows: &[u8]) {
        let n = rows.len() / self.leaves.row_bytes();
        assert_eq!(rows.len(), n * self.leaves.row_bytes(), "whole rows");
        // Every shape check comes before the claim, so a claimed block is always written.
        let chunk = n.min(SCRATCH_LEAVES);
        if self.cut > 0 {
            assert!(n >= 1 << self.cut, "a block holds whole leaf groups");
            assert!(n.is_multiple_of(chunk), "a block holds whole chunks");
        }
        self.progress.claim(first_leaf, n);
        // SAFETY: the claim makes these leaves, and their subtree up to the unit, ours alone.
        unsafe {
            if self.cut == 0 {
                self.leaves.hash(rows, self.nodes.level_mut(0, first_leaf, n));
                return self.complete(0, first_leaf, n);
            }
            // The groups climb to the cut in a stack scratch, a chunk of leaves at a time, and only their tops are kept.
            let tops = n >> self.cut;
            let mut scratch = [MaybeUninit::<Hash>::uninit(); 2 * SCRATCH_LEAVES];
            for (k, rows) in rows.chunks_exact(chunk * self.leaves.row_bytes()).enumerate() {
                let (a, b) = scratch.split_at_mut(SCRATCH_LEAVES);
                self.leaves.hash(rows, &mut a[..chunk]);
                let (mut src, mut dst, mut m) = (a, b, chunk);
                for _ in 0..self.cut {
                    hash_many(
                        digests_as_bytes(&mut src[..m]),
                        2 * OUT_LEN,
                        digests_as_bytes(&mut dst[..m / 2]),
                    );
                    (src, dst, m) = (dst, src, m / 2);
                }
                self.nodes
                    .level_mut(self.cut, (first_leaf >> self.cut) + k * m, m)
                    .copy_from_slice(&src[..m]);
            }
            self.complete(self.cut, first_leaf >> self.cut, tops);
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
        let height = (n / LANES).max(1).ilog2() as usize;
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
        let log_block = num_leaves
            .ilog2()
            .saturating_sub(log_tasks)
            .min(UNIT.ilog2())
            .max(self.cut as u32);
        let block_bytes = self.leaves.row_bytes() << log_block;
        parallel::for_each(num_leaves >> log_block, |b| {
            self.absorb_bytes(b << log_block, &data[b * block_bytes..][..block_bytes]);
        });
    }

    /// The finished tree, cut at the builder's level.
    ///
    /// # Panics
    ///
    /// Panics unless every leaf was absorbed.
    pub fn finish(self) -> CutTree {
        assert!(self.progress.all_claimed(), "every leaf absorbed");
        let (cut, num_leaves) = (self.cut, self.nodes.num_leaves);
        // SAFETY: every block was absorbed once, and the last arrivals climbed every level above.
        let nodes = unsafe { self.nodes.assume_init() };
        CutTree { nodes, cut, num_leaves }
    }
}

/// The flat tree from level `cut` up, written at disjoint nodes by concurrent climbs.
struct Nodes {
    tree: Vec<MaybeUninit<Hash>>,
    base: SendPtr<MaybeUninit<Hash>>,
    num_leaves: usize,
    cut: usize,
}

impl Nodes {
    fn new(num_leaves: usize, cut: usize) -> Self {
        let mut tree = Box::new_uninit_slice(((2 * num_leaves) >> cut) - 1).into_vec();
        let base = SendPtr(tree.as_mut_ptr());
        Self {
            tree,
            base,
            num_leaves,
            cut,
        }
    }

    /// Nodes on `level`.
    fn width(&self, level: usize) -> usize {
        self.num_leaves >> level
    }

    /// Index of `level`'s first node.
    fn start(&self, level: usize) -> usize {
        CutTree::start(self.num_leaves, level) - CutTree::start(self.num_leaves, self.cut)
    }

    /// Nodes `first .. first + n` of `level`.
    ///
    /// # Safety
    ///
    /// No other live slice overlaps them.
    #[allow(clippy::mut_from_ref)]
    unsafe fn level_mut(&self, level: usize, first: usize, n: usize) -> &mut [MaybeUninit<Hash>] {
        debug_assert!(self.cut <= level && first + n <= self.width(level));
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
            hash_many(digests_as_bytes(children), 2 * OUT_LEN, digests_as_bytes(parents));
            (first, n) = (first / 2, n / 2);
        }
    }

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

/// Leaves a block hashes and climbs to the cut at a time, in a stack scratch that stays in L1.
const SCRATCH_LEAVES: usize = 256;

/// Levels below which a large tree keeps nothing: groups of `2^CUT` leaves are rehashed from their rows when opened.
const CUT: usize = 4;

/// Trees of this many leaves or more are cut, so every block they are built from holds a leaf group.
const CUT_FROM: usize = 1 << 12;

/// A finished tree that keeps only the levels from `cut` up, in the flat layout of the full tree.
///
/// Opening a leaf group takes its rows again: the levels below `cut` are recomputed from them.
pub struct CutTree {
    nodes: Vec<Hash>,
    cut: usize,
    num_leaves: usize,
}

impl CutTree {
    /// Index of `level`'s first node in the flat tree of `num_leaves` leaves.
    fn start(num_leaves: usize, level: usize) -> usize {
        2 * num_leaves - ((2 * num_leaves) >> level)
    }

    pub fn root(&self) -> Hash {
        self.nodes[self.nodes.len() - 1]
    }

    /// Distinct groups the `positions` fall in, ascending.
    fn groups(&self, positions: &[usize]) -> Vec<usize> {
        let mut groups: Vec<usize> = positions.iter().map(|&q| q >> self.cut).collect();
        groups.sort_unstable();
        groups.dedup();
        groups
    }

    /// Every leaf of the groups `positions` fall in, ascending: the rows [`Self::prune`] takes.
    pub fn group_positions(&self, positions: &[usize]) -> Vec<usize> {
        let groups = self.groups(positions);
        groups
            .iter()
            .flat_map(|&g| g << self.cut..(g + 1) << self.cut)
            .collect()
    }

    /// The octopus over `positions`, with `row(q)` the row stored at `q`.
    ///
    /// `group_rows` are the full rows of [`Self::group_positions`], `row_words` each, back to back, hashed
    /// as the leaves `zeros(leaf_words - row_words) ‖ row`.
    pub fn prune<'a>(
        &self,
        positions: &[usize],
        row_words: usize,
        leaf_words: usize,
        group_rows: &[F64],
        row: impl Fn(usize) -> &'a [F64],
    ) -> PrunedMerklePaths {
        let (groups, size) = (self.groups(positions), 1usize << self.cut);
        let n = groups.len() * size;
        assert_eq!(group_rows.len(), n * row_words, "the rows of every group");
        // All groups' leaves as one flat tree up to the cut: a group is aligned, so no climb mixes two.
        // An uncut tree stores every node, so it needs none of them.
        let local = if self.cut == 0 || n == 0 {
            Vec::new()
        } else {
            let mut nodes = Nodes::new(n, 0);
            // SAFETY: the nodes are ours alone, the climb writes every level it reads, and the levels kept are written.
            unsafe {
                LeafHasher::new(8 * row_words, 8 * leaf_words).hash(cast_slice(group_rows), nodes.level_mut(0, 0, n));
                nodes.climb(0, 0, n, self.cut);
                nodes.tree.truncate(Self::start(n, self.cut));
                nodes.assume_init()
            }
        };
        let node = |level: usize, i: usize| {
            if level >= self.cut {
                return self.nodes[Self::start(self.num_leaves, level) - Self::start(self.num_leaves, self.cut) + i];
            }
            let width = 1usize << (self.cut - level);
            let group = groups
                .binary_search(&(i / width))
                .expect("a sibling is in an opened group");
            local[Self::start(n, level) + group * width + i % width]
        };
        PrunedMerklePaths::prune(self.num_leaves, positions, node, row)
    }
}

/// How rows become leaf digests, chosen once from the leaf shape.
///
/// Whole blocks of leading zeros are one sponge state, absorbed once for every leaf.
enum LeafHasher {
    /// Past the shared prefix, each row is its own image.
    Direct {
        row_bytes: usize,
        state: [u64; STATE_LANES],
    },
    /// The rest of the padding does not fill a block, so rows are zero-extended in a tile first.
    Staged {
        row_bytes: usize,
        image: usize,
        state: [u64; STATE_LANES],
    },
}

impl LeafHasher {
    fn new(row_bytes: usize, leaf_bytes: usize) -> Self {
        assert!(0 < row_bytes && row_bytes <= leaf_bytes, "a leaf holds its row");
        let zero_blocks = (leaf_bytes - row_bytes) / RATE;
        let state = zero_prefix_state(zero_blocks);
        let image = leaf_bytes - zero_blocks * RATE;
        if image == row_bytes {
            Self::Direct { row_bytes, state }
        } else {
            assert!(image <= STAGE_TILE_BYTES, "a padded leaf fits the tile");
            Self::Staged {
                row_bytes,
                image,
                state,
            }
        }
    }

    fn row_bytes(&self) -> usize {
        match *self {
            Self::Direct { row_bytes, .. } | Self::Staged { row_bytes, .. } => row_bytes,
        }
    }

    /// Hash one leaf per row into `out`.
    fn hash(&self, rows: &[u8], out: &mut [MaybeUninit<Hash>]) {
        match *self {
            Self::Direct { row_bytes, state } => {
                hash_many_from_state(rows, row_bytes, &state, digests_as_bytes(out));
            }
            Self::Staged {
                row_bytes,
                image,
                state,
            } => {
                // Whole batches per tile.
                let per_tile = STAGE_TILE_BYTES / image;
                let per_tile = if per_tile >= LANES {
                    per_tile / LANES * LANES
                } else {
                    per_tile
                };
                let mut tile = Tile::new();
                for (out, rows) in out.chunks_mut(per_tile).zip(rows.chunks(per_tile * row_bytes)) {
                    let images = tile.extend(rows, row_bytes, image);
                    hash_many_from_state(images, image, &state, digests_as_bytes(out));
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
        let tile: &mut [u8] = cast_slice_mut(&mut self.0);
        let n = rows.len() / row_bytes;
        for (slot, row) in tile.chunks_exact_mut(image).zip(rows.chunks_exact(row_bytes)) {
            slot[image - row_bytes..].copy_from_slice(row);
        }
        &tile[..n * image]
    }
}

fn digests_as_bytes(out: &mut [MaybeUninit<Hash>]) -> &mut [u8] {
    // SAFETY: a digest is 32 bytes with no padding, and the hasher only writes.
    unsafe { std::slice::from_raw_parts_mut(out.as_mut_ptr().cast(), out.len() * OUT_LEN) }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The tree over `num_leaves` equal byte leaves, each hashed as [`primitives::hash::hash`] of its bytes.
    fn merkle_tree(data: &[u8], num_leaves: usize) -> Vec<Hash> {
        let leaf_bytes = data.len() / num_leaves;
        let builder = MerkleBuilder::with_bytes(num_leaves, leaf_bytes, leaf_bytes, 0);
        builder.absorb_all(data);
        builder.finish().nodes
    }

    /// The tree over `num_leaves` rows of `row_words`, each hashed as `zeros(leaf_words - row_words) ‖ row`.
    fn merkle_tree_padded_rows(data: &[F64], num_leaves: usize, row_words: usize, leaf_words: usize) -> Vec<Hash> {
        assert_eq!(data.len(), row_words * num_leaves);
        let builder = MerkleBuilder::with_bytes(num_leaves, 8 * row_words, 8 * leaf_words, 0);
        builder.absorb_all(cast_slice(data));
        builder.finish().nodes
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
        // Leaf sizes on both sides of a block, whole blocks or not.
        //
        // Leaf counts cross the batch, the block, and the parallel top.
        for (num_leaves, leaf_size) in [
            (1usize, 32usize),
            (2, 48),
            (8, 32),
            (32, 64),
            (64, 128),
            (64, 136),
            (64, 272),
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
            (256, 30, 64),
            (1 << 14, 47, 64),
            // A prefix shorter than one block: nothing shared, still staged.
            (32, 5, 8),
            (256, 61, 64),
            // Leaves that are not a whole number of blocks.
            (16, 3, 5),
            (64, 7, 40),
        ] {
            let data: Vec<F64> = (0..row_words * num_leaves)
                .map(|i| F64(i.wrapping_mul(0x9E37_79B9_7F4A_7C15) as u64 | 1))
                .collect();
            let want = merkle_tree_sequential(
                data.chunks(row_words).map(|row| {
                    let mut image = vec![0u8; 8 * (leaf_words - row_words)];
                    image.extend_from_slice(cast_slice(row));
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
    fn cut_tree_prunes_like_the_full_tree() {
        // Invariant: opening through the cut tree gives the octopus of the full tree.
        for (num_leaves, row_words, leaf_words) in [(256usize, 8usize, 16usize), (1 << 10, 24, 24), (32, 8, 8)] {
            let data: Vec<F64> = (0..row_words * num_leaves)
                .map(|i| F64(i as u64 * 0x9E37_79B9 + 1))
                .collect();
            let full = merkle_tree_padded_rows(&data, num_leaves, row_words, leaf_words);
            let row = |q: usize| &data[q * row_words..][..row_words];
            let builder = MerkleBuilder::with_bytes(num_leaves, 8 * row_words, 8 * leaf_words, CUT);
            builder.absorb_all(cast_slice(&data));
            let cut = builder.finish();
            assert_eq!(cut.root(), *full.last().unwrap());
            for positions in [
                vec![0usize],
                vec![5, 5, 6, 200 % num_leaves, num_leaves - 1],
                (0..num_leaves).step_by(7).collect(),
            ] {
                let group = cut.group_positions(&positions);
                let rows: Vec<F64> = group.iter().flat_map(|&q| row(q)).copied().collect();
                let got = cut.prune(&positions, row_words, leaf_words, &rows, row);
                let level_start = |level: usize| 2 * num_leaves - ((2 * num_leaves) >> level);
                let node = |level: usize, i: usize| full[level_start(level) + i];
                assert_eq!(got, PrunedMerklePaths::prune(num_leaves, &positions, node, row));
            }
        }
    }

    #[test]
    fn blocks_of_any_size_build_one_tree() {
        // Invariant: the tree does not depend on the block size the encoder picks.
        let (num_leaves, row_words) = (1usize << 12, 6usize);
        let data: Vec<F64> = (0..row_words * num_leaves).map(|i| F64(i as u64 * 7 + 1)).collect();
        let want = merkle_tree_padded_rows(&data, num_leaves, row_words, row_words);
        for log_block in [0usize, 3, 5, 6, 9, 12] {
            let builder = MerkleBuilder::with_bytes(num_leaves, 8 * row_words, 8 * row_words, 0);
            // Blocks arrive out of order, as the encoder's tasks finish.
            for b in (0..num_leaves >> log_block).rev() {
                let rows = row_words << log_block;
                builder.absorb(b << log_block, &data[b * rows..][..rows]);
            }
            assert_eq!(&builder.finish().nodes[..], &want[..], "log_block={log_block}");
        }
        // A cut tree is the full tree without its lowest levels, whatever the block size.
        for log_block in [4usize, 5, 9, 12] {
            let builder = MerkleBuilder::with_bytes(num_leaves, 8 * row_words, 8 * row_words, CUT);
            for b in (0..num_leaves >> log_block).rev() {
                let rows = row_words << log_block;
                builder.absorb(b << log_block, &data[b * rows..][..rows]);
            }
            assert_eq!(
                &builder.finish().nodes[..],
                &want[CutTree::start(num_leaves, CUT)..],
                "log_block={log_block}"
            );
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
