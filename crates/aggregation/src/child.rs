//! The guest's witness for one child proof, and the opening shapes it shares with the guest's constants.

use super::cells::count;
use super::error::AggregateError;
use super::hints::SubHints;
use fiat_shamir_prover::merkle::{hash_pair, hash_to_scalars, hash_words};
use lean_vm_core::cpu::{block_kappa_sources, col_kappa_sources, from_scalar, layout_of};
use lean_vm_core::leaf;
use lean_vm_core::witness::Placement;
use primitives::field::F128;

/// The stacked WHIR opening of a `2^mu` stack at a rate: the verifier's config, then each level's message columns
/// after its folds and its Merkle tree's depth. The hint builder needs it for the real opening and the placeholder map
/// for every candidate size, so it lives here: a candidate whose shape differed from the real one would compile a
/// guest that cannot open the proof it is handed. `None` for a shape no proof has.
pub(super) fn whir_levels(mu: usize, log_inv_rate: usize) -> Option<(verifier::WhirConfig, Vec<usize>, Vec<usize>)> {
    let config = verifier::derive_config(mu, log_inv_rate).ok()?;
    let log_msg_cols: Vec<usize> = config
        .folds
        .iter()
        .scan(mu, |cols, &fold| {
            *cols -= fold;
            Some(*cols)
        })
        .collect();
    let depth = log_msg_cols
        .iter()
        .zip(&config.log_inv_rates)
        .map(|(c, r)| c + r)
        .collect();
    Some((config, log_msg_cols, depth))
}

/// The path bits a query's Merkle walk dispatches on at a time, the guest's `QW` (`walk_path`).
pub(super) const QUERY_WINDOW_BITS: usize = 6;
/// The cells `decode_query_windows` holds a squeezed word's windows in, the guest's `QUERY_WINDOWS_CAP`.
#[cfg(feature = "compile-guest")]
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

/// `count(g)` for each run of one group `g` in the stacking order, which `keys` sorts the members by, `groups` holding
/// each group's first member. A group that came back after another would be named twice, so the run count checks
/// each group is one run.
fn group_order(keys: &[(usize, usize)], groups: &[usize]) -> Vec<F128> {
    // An insertion sort: a child has a few hundred members at most.
    let mut order: Vec<usize> = (0..keys.len()).collect();
    for i in 1..order.len() {
        let mut j = i;
        while j > 0 && keys[order[j - 1]] > keys[order[j]] {
            order.swap(j - 1, j);
            j -= 1;
        }
    }
    let mut runs: Vec<usize> = Vec::with_capacity(order.len());
    for member in order {
        let group = groups.partition_point(|&start| start <= member) - 1;
        if runs.last() != Some(&group) {
            runs.push(group);
        }
    }
    assert_eq!(runs.len(), groups.len(), "a group's members are consecutive");
    runs.into_iter().map(count).collect()
}

/// The guest's witness for verifying one child (`guests/lean_ethereum.py`), built from the layout of an execution of
/// the `2^kbc`-instruction inner program at the sizes the `summary` the `verifier` crate read out of the child's
/// `proof` announces, and from that proof's Merkle paths, whose positions and sizes its replay pinned. Nothing here
/// says the child verifies: the guest's run does.
pub(super) fn gen_verify(
    kbc: usize,
    proof: &verifier::Proof,
    summary: &verifier::Summary,
) -> Result<SubHints, AggregateError> {
    let rows = std::array::from_fn(|t| summary.table_rows[t] as usize);
    let layout = layout_of(kbc, summary.log_memory, rows);
    let taus = layout.taus;
    let sides = [&layout.push, &layout.pull, &layout.count].map(|blocks| leaf::layout(blocks));
    // The guest's buffers have fixed capacities, so its constants do not depend on a child's shape. A child that
    // verifies fits them.
    let fits = sides.iter().all(|side| side.mu <= MU_CAP) && proof.stream.len() <= STREAM_CAP;
    if !fits {
        return Err(AggregateError::InvalidChild);
    }
    let block_offsets = sides.map(|side| side.offsets);
    let mu = layout.shape.mu;
    let mut stream: Vec<F128> = proof.stream.iter().copied().map(from_scalar).collect();
    stream.resize(STREAM_CAP, F128::ZERO);

    // The guest replays the proof off the same stream the native verifier reads: every transmitted scalar is already
    // there in protocol order.
    let rounds = *taus.iter().max().unwrap();
    let mut hints: SubHints = vec![
        ("stream", stream),
        // The table sumcheck's round count, which the guest certifies is the largest of the taus.
        ("zc_tau_max", vec![count(rounds)]),
        // Every table's log height, which the guest certifies against its row count.
        ("table_logs", taus.iter().map(|&t| count(t)).collect()),
        ("col_group_order", col_group_order(kbc, &layout.placements)),
        ("block_group_order", block_group_order(kbc, &block_offsets)),
    ];
    let (config, _, depth) = whir_levels(mu, summary.log_inv_rate).ok_or(AggregateError::InvalidChild)?;
    hints.extend(merkle_hints(config.queries, &depth, proof));
    Ok(hints)
}

/// The committed columns in their stacking order (`placements_of`: descending kappa, then index), each run of a column
/// group ([`col_groups`]) named once. The guest certifies the order before it reads claims by it.
fn col_group_order(kbc: usize, placements: &[Placement]) -> Vec<F128> {
    let (mut keys, mut sources) = (Vec::new(), Vec::new());
    for (placement, source) in placements.iter().zip(col_kappa_sources(kbc)) {
        if let Some(source) = source {
            keys.push((0, placement.offset));
            sources.push(source);
        }
    }
    group_order(&keys, &col_groups(&sources))
}

/// Per bus side, its blocks in their stacking order (their `offsets` in the side's layout), each run of a block group
/// ([`block_groups`]) named once. The guest certifies the native verifier's order (descending kappa, then index)
/// before it derives offsets from it.
fn block_group_order(kbc: usize, offsets: &[Vec<usize>]) -> Vec<F128> {
    let (mut keys, mut side_starts) = (Vec::new(), Vec::new());
    for (side, offsets) in offsets.iter().enumerate() {
        side_starts.push(keys.len());
        keys.extend(offsets.iter().map(|&offset| (side, offset)));
    }
    group_order(&keys, &block_groups(&block_kappa_sources(kbc), &side_starts))
}

/// The stacked WHIR opening's Merkle witness, per level: each query's leaf row and the sibling of every node it
/// climbs through below the level's cap, then the cap, every node of the top [`merkle_cap_depth`] levels the queries
/// reach, and which of its nodes they reach. The upper tree is shared by a level's queries; a subtree no query reaches
/// stays zero, unread.
fn merkle_hints(queries: &[usize], depth: &[usize], proof: &verifier::Proof) -> SubHints {
    let mut hints = Vec::new();
    let levels = queries.iter().zip(depth);
    for (level, ((&queries, &depth), phase)) in levels.zip(&proof.merkle_openings).enumerate() {
        let cap_depth = merkle_cap_depth(queries, depth);
        let path_depth = depth - cap_depth;
        let mut nodes = vec![[0u8; 32]; 2 << cap_depth];
        let mut active = vec![F128::ZERO; 1 << cap_depth];
        for opening in phase {
            let leaf: Vec<u64> = opening.leaf.iter().map(|word| word.0).collect();
            // Level 0's rows are K lanes, a cell each; deeper ones E words, two lanes a cell.
            let row = if level == 0 {
                leaf.iter().map(|&x| F128::new(x, 0)).collect()
            } else {
                leaf.as_chunks().0.iter().map(|&[c0, c1]| F128::new(c0, c1)).collect()
            };
            hints.push(("merkle_leaf_rows", row));
            let mut path_siblings = Vec::with_capacity(2 * path_depth);
            let mut node = hash_words(leaf);
            let mut index = (1 << depth) + opening.leaf_index as usize;
            for (height, sibling) in opening.siblings.iter().enumerate() {
                let (left, right) = if index & 1 == 0 {
                    (&node, sibling)
                } else {
                    (sibling, &node)
                };
                if height < path_depth {
                    path_siblings.extend(hash_to_scalars::<F128>(sibling));
                } else {
                    nodes[index] = node;
                    nodes[index ^ 1] = *sibling;
                    active[index >> 1] = F128::ONE;
                }
                node = hash_pair(left, right);
                index >>= 1;
            }
            nodes[1] = node;
            hints.push(("merkle_children", path_siblings));
        }
        let mut caps = Vec::with_capacity(2 * nodes.len());
        for node in &nodes {
            caps.extend(hash_to_scalars::<F128>(node));
        }
        hints.push(("merkle_caps", caps));
        hints.push(("merkle_cap_active", active));
    }
    hints
}

/// The guest's baked buffer caps, which `placeholder_map` compiles in and
/// `gen_verify` admits against: one definition, so a hinted shape can never
/// outgrow the buffer the guest was compiled with.
pub(super) const MU_CAP: usize = 40;
pub(super) const STREAM_CAP: usize = 8192;
