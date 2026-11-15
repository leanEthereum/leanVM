//! The guest's witness for one child proof, and the opening shapes it shares with the guest's constants.

use super::cells::{ONE, ZERO, count, hash_to_scalars};
use super::deferred::DeferredSubproof;
use super::error::AggregateError;
use super::hints::SubHints;
use keccak256::hash_pair;
use lean_vm_core::cpu::{Layout, block_kappa_sources, col_kappa_sources, from_scalar};
use lean_vm_core::leaf::{self, Block};
use lean_vm_core::tables::N_TABLES;
use verifier::{E, K};

/// The layout of an execution of a `2^kbc`-instruction program with `2^log_mem` cells of memory and `rows` rows in each
/// table, as the prover builds it. It reads the program only through its public columns, which no coordinate the guest
/// is given depends on, so a stand-in program of that size serves.
pub(super) fn execution_layout(kbc: usize, log_mem: usize, rows: [usize; N_TABLES]) -> Layout {
    let stand_in = vec![isa::Op::Xor { a: 0, b: 0, c: 0 }; 1 << kbc];
    lean_vm_core::cpu::layout(&stand_in, log_mem, rows, [from_scalar(ZERO); 2])
}

/// The stacked opening's shape at one committed size and rate, plus the query packing derived from it. The hint
/// builder needs it for the real opening and the placeholder map for every candidate size, so it lives here: a
/// candidate whose shape differed from the real one would compile a guest that cannot open the proof it is handed.
pub(super) struct WhirShape {
    /// Per-level query counts.
    pub(super) queries: Vec<usize>,
    /// Per-level fold counts, the lane fold first.
    pub(super) folds: Vec<usize>,
    /// Log message columns after each level's fold.
    pub(super) log_msg_cols: Vec<usize>,
    /// The residual cube's dimension, left after every fold.
    pub(super) yr_log_n: usize,
    /// Merkle tree depth per level.
    pub(super) depth: Vec<usize>,
    /// Query positions carried by one squeezed word, per level.
    pub(super) per_squeeze: Vec<usize>,
}

pub(super) fn whir_shape(mu: usize, log_inv_rate: usize) -> WhirShape {
    let config = pcs::whir::config_for_rate(mu, log_inv_rate).expect("stacked whir config");
    let levels = config.level_shapes(mu);
    let depth: Vec<usize> = levels.block_len.iter().map(|b| b.trailing_zeros() as usize).collect();
    WhirShape {
        queries: config.queries,
        folds: levels.ks,
        log_msg_cols: levels.log_msg_cols,
        yr_log_n: levels.yr_log_n,
        per_squeeze: depth.iter().map(|&d| 128 / d).collect(),
        depth,
    }
}

/// The path bits a query's Merkle walk dispatches on at a time, the guest's `QW` (`walk_path`).
pub(super) const QUERY_WINDOW_BITS: usize = 6;
/// The cells `decode_query_windows` holds a squeezed word's windows in, the guest's `QUERY_WINDOWS_CAP`.
pub(super) const QUERY_WINDOWS_CAP: usize = 36;

/// The depth of the cap a level's paths are walked into, which leaves the walked part whole windows of
/// [`QUERY_WINDOW_BITS`] bits: at least two levels deep, and from `log2(queries) - 5` to five levels below that.
pub(super) fn merkle_cap_depth(queries: usize, depth: usize) -> usize {
    let near = (queries.next_power_of_two().ilog2() as usize)
        .saturating_sub(QUERY_WINDOW_BITS - 1)
        .max(2)
        .min(depth);
    depth - (depth - near) / QUERY_WINDOW_BITS * QUERY_WINDOW_BITS
}

/// The first column of each column group: a maximal run of committed columns, in compact order, sharing one kappa
/// source. The stacked order (descending kappa, then index) keeps a group's columns consecutive, since any other
/// column of equal kappa lies outside it.
pub(super) fn col_groups(sources: &[(usize, usize)]) -> Vec<usize> {
    (0..sources.len())
        .filter(|&c| c == 0 || sources[c] != sources[c - 1])
        .collect()
}

/// The first block of each block group: as [`col_groups`], over the bus blocks, a group never crossing the start of a
/// side (`side_starts`), since a side's blocks tile its own cube.
pub(super) fn block_groups(sources: &[(usize, usize)], side_starts: &[usize]) -> Vec<usize> {
    (0..sources.len())
        .filter(|&b| side_starts.contains(&b) || sources[b] != sources[b - 1])
        .collect()
}

/// `count(g)` for each run of one group `g` in `groups`, in order. A group that came back after another would be
/// named twice, which the caller's count of runs catches.
fn group_runs(groups: impl Iterator<Item = usize>) -> Vec<E> {
    let mut runs: Vec<usize> = groups.collect();
    runs.dedup();
    runs.into_iter().map(count).collect()
}

/// The guest's witness for verifying one child (`guests/lean_ethereum.py`), built from the layout of an execution of
/// the `2^kbc`-instruction inner program at the sizes the `summary` the `verifier` crate read out of the child's
/// `proof` announces, and from that proof's Merkle paths, whose positions and sizes its replay pinned. Nothing here
/// says the child verifies: the guest's run does.
pub(super) fn gen_verify(
    kbc: usize,
    public_input: [E; 2],
    proof: &verifier::Proof,
    summary: &verifier::Summary,
    bytecode_value: E,
) -> Result<(SubHints, DeferredSubproof), AggregateError> {
    let rows = std::array::from_fn(|t| summary.table_rows[t] as usize);
    let layout = execution_layout(kbc, summary.log_memory, rows);
    let taus = layout.taus;
    let sides = [layout.push, layout.pull, layout.count];
    // The guest's buffers have fixed capacities, so its constants do not depend on a child's shape. A child that
    // verifies fits them.
    let fits = sides.iter().all(|blocks| leaf::layout(blocks).mu <= MU_CAP) && proof.stream.len() <= STREAM_CAP;
    if !fits {
        return Err(AggregateError::InvalidChild);
    }
    let column_offsets: Vec<usize> = layout.placements.iter().map(|p| p.offset).collect();
    let mu = layout.shape.mu;
    let mut stream = proof.stream.clone();
    stream.resize(STREAM_CAP, ZERO);

    // The guest replays the proof off the same stream the native verifier reads: every transmitted scalar is already
    // there in protocol order.
    let mut hints: SubHints = vec![
        ("stream", stream),
        // The table sumcheck's round count, which the guest certifies is the largest of the taus.
        ("zc_tau_max", vec![count(*taus.iter().max().unwrap())]),
        // Every table's log height, which the guest certifies against its row count.
        ("table_logs", taus.iter().map(|&t| count(t)).collect()),
        ("col_group_order", col_group_order(kbc, &column_offsets)),
        ("block_group_order", block_group_order(kbc, &sides)),
    ];
    hints.extend(merkle_hints(&whir_shape(mu, summary.log_inv_rate), proof));
    let deferred = DeferredSubproof {
        public_input,
        bytecode_point: summary.bytecode_point.clone(),
        bytecode_value,
    };
    Ok((hints, deferred))
}

/// The committed columns in their stacking order (`column_offsets`, from `placements_of`: descending kappa, then
/// index), each run of a column group ([`col_groups`]) named once. The guest certifies the order before it reads
/// claims by it.
fn col_group_order(kbc: usize, column_offsets: &[usize]) -> Vec<E> {
    let sources = col_kappa_sources(kbc);
    // Compact index to global column.
    let committed: Vec<usize> = (0..sources.len()).filter(|&c| sources[c].is_some()).collect();
    let groups = col_groups(&sources.iter().flatten().copied().collect::<Vec<_>>());
    let mut stacked: Vec<usize> = (0..committed.len()).collect();
    stacked.sort_by_key(|&compact| column_offsets[committed[compact]]);
    let order = group_runs(
        stacked
            .into_iter()
            .map(|compact| groups.partition_point(|&start| start <= compact) - 1),
    );
    assert_eq!(order.len(), groups.len(), "a column group's columns are consecutive");
    order
}

/// Per bus side, its blocks in their stacking order (`leaf::layout`'s offsets), each run of a block group
/// ([`block_groups`]) named once. The guest certifies the native verifier's order (descending kappa, then index)
/// before it derives offsets from it.
fn block_group_order(kbc: usize, sides: &[Vec<Block>; 3]) -> Vec<E> {
    let mut side_starts = vec![0];
    for blocks in sides {
        side_starts.push(side_starts.last().unwrap() + blocks.len());
    }
    let groups = block_groups(&block_kappa_sources(kbc), &side_starts);
    let mut stacked = Vec::new();
    for (blocks, start) in sides.iter().zip(&side_starts) {
        let offsets = leaf::layout(blocks).offsets;
        let mut order: Vec<usize> = (0..blocks.len()).collect();
        order.sort_by_key(|&i| offsets[i]);
        stacked.extend(order.into_iter().map(|i| start + i));
    }
    // A group never crosses a side, so runs never merge across one.
    let order = group_runs(
        stacked
            .into_iter()
            .map(|block| groups.partition_point(|&start| start <= block) - 1),
    );
    assert_eq!(order.len(), groups.len(), "a block group's blocks are consecutive");
    order
}

/// The stacked WHIR opening's Merkle witness, per level: each query's leaf row and the children of every node it
/// climbs through below the level's cap, then the cap, every node of the top [`merkle_cap_depth`] levels the queries
/// reach, and which of its nodes they reach. The upper tree is shared by a level's queries; a subtree no query reaches
/// stays zero, unread.
fn merkle_hints(stack: &WhirShape, proof: &verifier::Proof) -> SubHints {
    let mut hints = Vec::new();
    let levels = stack.queries.iter().zip(&stack.depth);
    for (level, ((&queries, &depth), phase)) in levels.zip(&proof.merkle_openings).enumerate() {
        let cap_depth = merkle_cap_depth(queries, depth);
        let path_depth = depth - cap_depth;
        let mut nodes = vec![[0u8; 32]; 2 << cap_depth];
        let mut active = vec![ZERO; 1 << cap_depth];
        for opening in phase {
            // Level 0's rows are K lanes, a cell each; deeper ones E words, two lanes a cell.
            let row = if level == 0 {
                opening.leaf.iter().map(|&x| E::from(x)).collect()
            } else {
                let pairs = opening.leaf.as_chunks().0.iter();
                pairs.map(|&[c0, c1]: &[K; 2]| E::new(c0.0, c1.0)).collect()
            };
            hints.push(("merkle_leaf_rows", row));
            let mut path_children = Vec::with_capacity(4 * path_depth);
            let leaf: Vec<u8> = opening.leaf.iter().flat_map(|word| word.to_bytes()).collect();
            let mut node = keccak256::hash(&leaf);
            let mut index = (1 << depth) + opening.leaf_index as usize;
            for (height, sibling) in opening.siblings.iter().enumerate() {
                let (left, right) = if index & 1 == 0 {
                    (&node, sibling)
                } else {
                    (sibling, &node)
                };
                if height < path_depth {
                    path_children.extend(hash_to_scalars(left));
                    path_children.extend(hash_to_scalars(right));
                } else {
                    nodes[index] = node;
                    nodes[index ^ 1] = *sibling;
                    active[index >> 1] = ONE;
                }
                node = hash_pair(left, right);
                index >>= 1;
            }
            nodes[1] = node;
            hints.push(("merkle_children", path_children));
        }
        hints.push(("merkle_caps", nodes.iter().flat_map(hash_to_scalars).collect()));
        hints.push(("merkle_cap_active", active));
    }
    hints
}

/// The guest's baked buffer caps, which `placeholder_map` compiles in and
/// `gen_verify` admits against: one definition, so a hinted shape can never
/// outgrow the buffer the guest was compiled with.
pub(super) const MU_CAP: usize = 40;
pub(super) const STREAM_CAP: usize = 8192;
