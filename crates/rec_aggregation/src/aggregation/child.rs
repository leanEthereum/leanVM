//! The guest's witness for one child proof, and the opening shapes it shares with the guest's constants.

use super::cells::{ONE, ZERO, count, hash_pair, hash_to_scalars};
use super::deferred::DeferredSubproof;
use super::error::AggregateError;
use super::hints::SubHints;
use crate::protocol::{block_kappa_sources, bus_blocks, col_kappa_sources, column_stack, side_stack, table_logs};
use verifier::{E, K};

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
    let config = verifier::derive_config(mu, log_inv_rate).expect("stacked whir config");
    let log_msg_cols: Vec<usize> = config
        .folds
        .iter()
        .scan(mu, |cols, &fold| {
            *cols -= fold;
            Some(*cols)
        })
        .collect();
    let depth: Vec<usize> = log_msg_cols
        .iter()
        .zip(&config.log_inv_rates)
        .map(|(c, r)| c + r)
        .collect();
    WhirShape {
        queries: config.queries.to_vec(),
        yr_log_n: *log_msg_cols.last().unwrap(),
        per_squeeze: depth.iter().map(|&d| 128 / d).collect(),
        folds: config.folds,
        log_msg_cols,
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

/// The first column of each column group: a maximal run of committed columns, in compact
/// order, sharing one kappa source. The stacked order (descending kappa, then index) keeps
/// a group's columns consecutive, since any other column of equal kappa lies outside it.
pub(super) fn block_groups(sources: &[(usize, usize)], side_starts: &[usize]) -> Vec<usize> {
    // As `col_groups`, per side: a side's blocks tile its own cube.
    (0..sources.len())
        .filter(|&b| side_starts.contains(&b) || sources[b] != sources[b - 1])
        .collect()
}

pub(super) fn col_groups(sources: &[(usize, usize)]) -> Vec<usize> {
    (0..sources.len())
        .filter(|&c| c == 0 || sources[c] != sources[c - 1])
        .collect()
}

/// Config + hints for the recursion guest (`guests/lean_ethereum.py`), built
/// from the layout of an execution of the `2^kbc`-instruction inner program at the
/// sizes the `summary` the `verifier` crate read out of the child's `proof` announces,
/// and that proof's Merkle paths, whose positions and sizes its replay pinned.
/// Nothing here says the child verifies: the guest's run does.
pub(super) fn gen_verify(
    kbc: usize,
    public_input: [E; 2],
    proof: &verifier::Proof,
    summary: &verifier::Summary,
    bytecode_value: E,
) -> Result<(SubHints, DeferredSubproof), AggregateError> {
    let taus = table_logs(&summary.table_rows);
    let sides = bus_blocks(kbc, summary.log_memory, &taus);
    let side_layouts = sides.each_ref().map(|blocks| side_stack(blocks));
    // The guest holds one opening arm per committed size an execution can have, so
    // a child the native verifier accepts always has one. Fixed capacities: every
    // buffer/stride placeholder is a global cap so the placeholder map is
    // SHAPE-INDEPENDENT (the definition of generic). A child that verifies fits them.
    let fits = side_layouts.iter().all(|&(_, mu)| mu <= MU_CAP) && proof.stream.len() <= STREAM_CAP;
    if !fits {
        return Err(AggregateError::InvalidChild);
    }
    let (offsets, mu) = column_stack(kbc, summary.log_memory, &taus);

    // ---- typed extraction: the proof's stream + the verifier's summary ----
    // Push and pull share the bytecode point.
    let bytecode_point = summary.bytecode_point.clone();

    // ---- the stacked opening: config + the opening summary ----
    let stack = whir_shape(mu, summary.log_inv_rate);

    // ---- per-sub HINT data (the placeholder map is built once, elsewhere) ----
    // Per side, the packing order read straight off `leaf::layout`'s offsets:
    // sort_order[side_base + rank] = g^{global index of the rank-r block}. The
    // guest certifies it is the native verifier's order (descending kappa, then
    // ascending index) before deriving offsets from it.
    let mut sort_order: Vec<E> = Vec::new();
    let mut gbase = 0usize;
    let block_sources = block_kappa_sources(kbc);
    let side_starts: Vec<usize> = sides
        .iter()
        .scan(0, |at, blocks| {
            let start = *at;
            *at += blocks.len();
            Some(start)
        })
        .chain([block_sources.len()])
        .collect();
    let block_groups = block_groups(&block_sources, &side_starts);
    for (s, blocks) in sides.iter().enumerate() {
        let mut order: Vec<usize> = (0..blocks.len()).collect();
        order.sort_by_key(|&i| side_layouts[s].0[i]);
        let mut last_group = usize::MAX;
        for &i in &order {
            // g^{global group index}, once per group: its blocks are consecutive.
            let group = block_groups.partition_point(|&start| start <= gbase + i) - 1;
            if group != last_group {
                sort_order.push(count(group));
                last_group = group;
            }
        }
        gbase += blocks.len();
    }
    assert_eq!(
        sort_order.len(),
        block_groups.len(),
        "a block group's blocks are consecutive"
    );
    // The stacked commitment uses witness::placements_of: committed columns
    // sorted by descending kappa, then by their native column index. Transport
    // compact committed-column indices; the guest certifies the permutation,
    // ordering, and accumulated offsets before using them as claim selectors.
    let col_sources = col_kappa_sources(kbc);
    let committed_globals: Vec<usize> = col_sources
        .iter()
        .enumerate()
        .filter_map(|(i, source)| source.map(|_| i))
        .collect();
    let mut compact_col = vec![usize::MAX; col_sources.len()];
    for (compact, &global) in committed_globals.iter().enumerate() {
        compact_col[global] = compact;
    }
    let mut col_order = committed_globals;
    col_order.sort_by_key(|&global| offsets[global]);
    // The order by column group (`col_groups`): its columns are consecutive in it.
    let groups = col_groups(&col_sources.iter().flatten().copied().collect::<Vec<_>>());
    let group_of = |compact: usize| groups.partition_point(|&start| start <= compact) - 1;
    let mut col_group_order: Vec<E> = Vec::new();
    let mut last_group = usize::MAX;
    for &global in &col_order {
        let group = group_of(compact_col[global]);
        if group != last_group {
            col_group_order.push(count(group));
            last_group = group;
        }
    }
    assert_eq!(
        col_group_order.len(),
        groups.len(),
        "a column group's columns are consecutive"
    );

    // ---- Hints for the stacked WHIR opening ----
    // Share the upper Merkle tree across a level's queries, one cap entry a level. Unknown,
    // unused subtrees stay opaque; the guest authenticates every cap leaf a query reaches.
    let mut query_hints = Vec::new();
    let levels = stack.queries.iter().zip(&stack.depth);
    for (level, ((&queries, &depth), phase)) in levels.zip(&proof.merkle_openings).enumerate() {
        let cap_depth = merkle_cap_depth(queries, depth);
        let n = 1 << cap_depth;
        let path_depth = depth - cap_depth;
        let mut nodes = vec![[0u8; 32]; 2 * n];
        let mut active = vec![ZERO; n];
        for opening in phase {
            // Level 0's rows are K lanes, a cell each; deeper ones E words, two lanes a cell.
            let row = if level == 0 {
                opening.leaf.iter().map(|&x| E::from(x)).collect()
            } else {
                opening
                    .leaf
                    .as_chunks()
                    .0
                    .iter()
                    .map(|&[c0, c1]: &[K; 2]| E::new(c0.0, c1.0))
                    .collect()
            };
            query_hints.push(("merkle_leaf_rows", row));
            let mut path_children = Vec::with_capacity(4 * path_depth);
            let leaf: Vec<u8> = opening.leaf.iter().flat_map(|word| word.to_bytes()).collect();
            let mut node = keccak256::hash(&leaf);
            let mut index = (1 << depth) + opening.leaf_index as usize;
            for (height, sibling) in opening.siblings.iter().enumerate() {
                if height >= path_depth {
                    nodes[index] = node;
                    nodes[index ^ 1] = *sibling;
                    active[index >> 1] = ONE;
                }
                let (left, right) = if index & 1 == 0 {
                    (&node, sibling)
                } else {
                    (sibling, &node)
                };
                if height < path_depth {
                    path_children.extend(hash_to_scalars(left));
                    path_children.extend(hash_to_scalars(right));
                }
                node = hash_pair(left, right);
                index >>= 1;
            }
            nodes[1] = node;
            query_hints.push(("merkle_children", path_children));
        }
        query_hints.push(("merkle_caps", nodes.iter().flat_map(hash_to_scalars).collect()));
        query_hints.push(("merkle_cap_active", active));
    }
    let deferred = DeferredSubproof {
        public_input,
        bytecode_point,
        bytecode_value,
    };

    let mut hints = vec![
        ("stream", {
            // The guest replays the proof off the same stream the native verifier
            // reads: every transmitted scalar (the level-0 OOD value, the fold rounds' tables,
            // level roots, high parts, OOD values, grind nonces, the final lane, the
            // closing rounds) is already there in protocol order, so there is nothing
            // to reassemble.
            let mut stream = proof.stream.clone();
            stream.resize(STREAM_CAP, ZERO);
            stream
        }),
        // the table sumcheck's round count: max_t tau_t, certified in-guest as a
        // maximum (one of the taus, and dominating them all).
        ("zc_tau_max", vec![count(*taus.iter().max().unwrap())]),
        // Every table's log height, which the guest certifies against its row count.
        ("table_logs", taus.iter().map(|&t| count(t)).collect()),
        ("col_group_order", col_group_order),
        ("block_group_order", sort_order),
    ];
    hints.extend(query_hints);
    Ok((hints, deferred))
}

/// The guest's baked buffer caps, which `placeholder_map` compiles in and
/// `gen_verify` admits against: one definition, so a hinted shape can never
/// outgrow the buffer the guest was compiled with.
pub(super) const MU_CAP: usize = 40;
pub(super) const STREAM_CAP: usize = 8192;
