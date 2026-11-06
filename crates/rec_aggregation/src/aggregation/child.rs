//! The guest's witness for one child proof, and the opening shapes it shares with the guest's constants.

use super::cells::count;
use super::deferred::DeferredSubproof;
use super::error::AggregationError;
use super::hints::SubHints;
use fiat_shamir::merkle::hash_to_scalars;
use leanvm_core::cpu::{Program, from_scalar};
use leanvm_core::leaf::Block;
use primitives::field::F192;

/// The verifier-side WHIR config for one committed size and rate, plus the
/// query packing derived from it. The hint builder needs it for the real
/// opening and the placeholder map for every candidate size, so it lives here:
/// a candidate whose shape differed from the real one would compile a guest
/// that cannot open the proof it is handed.
pub(super) struct WhirShape {
    pub(super) config: pcs::whir::ProverConfig,
    pub(super) levels: pcs::whir::LevelShapes,
    /// Merkle tree depth per level.
    pub(super) depth: Vec<usize>,
    /// Query positions carried by one squeezed F192 word, per level.
    pub(super) per_squeeze: Vec<usize>,
}

pub(super) fn whir_shape(mu: usize, log_inv_rate: usize) -> WhirShape {
    let config = pcs::whir::config_for_rate(mu, log_inv_rate).expect("stacked whir config");
    let levels = config.level_shapes(mu);
    let depth: Vec<usize> = levels.block_len.iter().map(|b| b.trailing_zeros() as usize).collect();
    let per_squeeze = depth.iter().map(|&d| 192 / d).collect();
    WhirShape {
        config,
        levels,
        depth,
        per_squeeze,
    }
}

pub(super) fn merkle_cap_depth(queries: usize, depth: usize) -> usize {
    (queries.next_power_of_two().ilog2() as usize).min(depth)
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
/// from the REAL `cpu::layout` of the inner program and the `summary` the
/// `verifier` crate read out of the child's proof, whose scalars are
/// `proof_stream` (zero hand-mirroring drift). Nothing here says the child
/// verifies: the guest's run does.
pub(super) fn gen_verify(
    program: &Program,
    public_input: [F192; 2],
    proof_stream: &[F192],
    summary: &verifier::Summary,
    bytecode_value: F192,
) -> Result<(SubHints, DeferredSubproof), AggregationError> {
    let layout = program.layout(
        summary.memory_cells as usize,
        std::array::from_fn(|t| summary.table_rows[t] as usize),
        public_input,
    );
    let sides: [&[Block]; 3] = [&layout.push, &layout.pull, &layout.count];
    let side_layouts = sides.map(leanvm_core::leaf::layout);
    // The guest holds one opening arm per candidate committed size, so a child
    // outside that window has no arm to dispatch to. `min_log_committed` keeps
    // every aggregate above the low end, leaving only the ceiling reachable.
    // Fixed capacities: every buffer/stride placeholder is a global cap so
    // the placeholder map is SHAPE-INDEPENDENT (the definition of generic). A
    // child that verifies and has an arm fits them; one that does not need not.
    let fits = side_layouts.iter().all(|side| side.mu <= MU_CAP) && proof_stream.len() <= STREAM_CAP;
    if !(MU_MIN..=MU_MAX).contains(&layout.shape.mu) || !fits {
        return Err(AggregationError::ChildOutOfRange {
            log_committed: layout.shape.mu,
        });
    }

    // ---- typed extraction: the proof's stream + the verifier's summary ----
    let scalars = |values: &[verifier::E]| -> Vec<F192> { values.iter().copied().map(from_scalar).collect() };
    // Push and pull share the bytecode point.
    let bytecode_point = scalars(&summary.bytecode_point);
    let kbc = bytecode_point.len() - leanvm_core::leaf::N_BYTECODE_SELECTORS;

    let taus = layout.taus;
    // ---- the stacked opening: config + the opening summary ----
    let stack = whir_shape(layout.shape.mu, summary.log_inv_rate);

    // ---- hints ----
    // The program's whole share of a bytecode leaf: ONE value, the stacked
    // polynomial at (ζ_lo, α⃗), the slot coordinates of the claim's own point being
    // the fingerprint challenges (§sec:e2e-bc). The summary carries the point
    // only; the caller evaluates it.
    let bcv = vec![bytecode_value];

    // ---- per-sub HINT data (the placeholder map is built once, elsewhere) ----
    // Per side, the packing order read straight off `leaf::layout`'s offsets:
    // sort_order[side_base + rank] = g^{global index of the rank-r block}. The
    // guest certifies it is the native verifier's order (descending kappa, then
    // ascending index) before deriving offsets from it.
    let mut sort_order: Vec<F192> = Vec::new();
    let mut gbase = 0usize;
    let block_sources = leanvm_core::cpu::block_kappa_sources(kbc);
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
        order.sort_by_key(|&i| side_layouts[s].offsets[i]);
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
    // The stacked commitment uses witness::placements_of: committed pieces
    // sorted by descending kappa, then by their native column and piece index.
    // Transport compact committed-piece indices; the guest certifies the permutation,
    // ordering, and accumulated offsets before using them as claim selectors.
    // A memory piece the memory's cells do not have takes no room, and ranks as one
    // of log 0: where it sits changes no other piece's offset.
    let col_sources = leanvm_core::cpu::col_kappa_sources(kbc);
    let committed: Vec<(usize, usize)> = col_sources
        .iter()
        .enumerate()
        .flat_map(|(i, source)| (0..source.as_ref().map_or(0, |s| s.pieces.len())).map(move |piece| (i, piece)))
        .collect();
    let placement = |compact: usize| {
        let (global, piece) = committed[compact];
        layout.columns[global].placements.get(piece)
    };
    let mut col_order: Vec<usize> = (0..committed.len()).collect();
    col_order.sort_by_key(|&compact| (std::cmp::Reverse(placement(compact).map_or(0, |p| p.n_vars)), compact));
    assert!(
        col_order
            .iter()
            .filter_map(|&compact| placement(compact))
            .map(|p| p.offset)
            .is_sorted(),
        "the rank order is the stacked order"
    );
    // The order by column group (`col_groups`): its pieces are consecutive in it.
    let groups = col_groups(
        &col_sources
            .iter()
            .flatten()
            .flat_map(|s| &s.pieces)
            .copied()
            .collect::<Vec<_>>(),
    );
    let group_of = |compact: usize| groups.partition_point(|&start| start <= compact) - 1;
    let mut col_group_order: Vec<F192> = Vec::new();
    let mut last_group = usize::MAX;
    for &compact in &col_order {
        let group = group_of(compact);
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

    // ---- Phase E2 hints (the stacked WHIR opening) ----
    // Share the upper Merkle tree across queries. Unknown, unused subtrees stay
    // opaque; the guest authenticates every cap leaf a query reaches.
    let mut query_hints = Vec::new();
    let (mut caps, mut cap_active) = (Vec::new(), Vec::new());
    let mut openings = summary.merkle_paths.iter();
    for (&queries, &depth) in stack.config.queries.iter().zip(&stack.depth) {
        let cap_depth = merkle_cap_depth(queries, depth);
        let n = 1 << cap_depth;
        let path_depth = depth - cap_depth;
        let mut nodes = vec![[0u8; 32]; 2 * n];
        let mut active = vec![F192::ZERO; n];
        for opening in openings.by_ref().take(queries) {
            query_hints.push((
                "merkle_leaf_rows",
                opening.leaf.iter().map(|x| F192::new(x.0, 0, 0)).collect(),
            ));
            let mut path_children = Vec::with_capacity(4 * path_depth);
            let bytes: Vec<_> = opening.leaf.iter().flat_map(|x| x.to_bytes()).collect();
            let mut node = pcs::merkle::hash_leaf(&bytes);
            let mut index = (1 << depth) + opening.leaf_index as usize;
            for (height, sibling) in opening.siblings.iter().enumerate() {
                if height >= path_depth {
                    nodes[index] = node;
                    nodes[index ^ 1] = *sibling;
                    active[index >> 1] = F192::ONE;
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
                node = pcs::merkle::hash_pair(left, right);
                index >>= 1;
            }
            nodes[1] = node;
            query_hints.push(("merkle_children", path_children));
        }
        caps.extend(nodes.iter().flat_map(hash_to_scalars));
        cap_active.extend(active);
    }
    let deferred = DeferredSubproof {
        public_input,
        bytecode_point,
        bytecode_value,
    };

    let mut hints = vec![
        ("stream", {
            // The guest replays the WHIR opening off the same stream the native
            // verifier reads: every transmitted scalar (sumcheck messages, level
            // roots, OOD claims, grind nonces, `yr`) is already there in protocol
            // order, so there is nothing to reassemble. The guest's `open_stacked`
            // picks it up at `msg_cursor = cursor`, which sits where the Keccak
            // reduction stopped; the ring-switch messages are struct-observed and
            // still do not advance that cursor.
            let mut stream = proof_stream.to_vec();
            stream.resize(STREAM_CAP, F192::ZERO);
            stream
        }),
        ("bytecode_val", bcv),
        ("merkle_caps", caps),
        ("merkle_cap_active", cap_active),
        // the table sumcheck's round count: max_t tau_t, certified in-guest as a
        // maximum (one of the taus, and dominating them all).
        ("zc_tau_max", vec![count(*taus.iter().max().unwrap())]),
        // Every table's log height, which the guest certifies against its row count.
        ("table_logs", taus.iter().map(|&t| count(t)).collect()),
        ("col_group_order", col_group_order),
        ("mem_pieces", memory_piece_hints(summary.memory_cells)),
        ("block_group_order", sort_order),
    ];
    hints.extend(query_hints);
    Ok((hints, deferred))
}

// The guest's memory pieces, these hints and its coefficients are written for three pieces: any other count would
// leave cells nothing writes, for the prover to choose.
const _: () = assert!(
    leanvm_core::cpu::MEMORY_PIECES == 3,
    "the guest is written for three memory pieces"
);

/// The memory's pieces as the guest takes them: the log of each of its three pieces as a
/// g-power, `g^0` for a piece it does not have, then whether it has the second and the third.
pub(super) fn memory_piece_hints(memory_cells: u64) -> Vec<F192> {
    let logs = leanvm_core::cpu::memory_pieces(memory_cells as usize);
    let log = |i: usize| logs.get(i).map_or(count(0), |&k| count(k));
    let has = |i: usize| if i < logs.len() { F192::ONE } else { F192::ZERO };
    vec![log(0), log(1), log(2), has(1), has(2)]
}

/// The guest's stacked-size dispatch range: one `match_range` opening arm per
/// candidate `mu` in `MU_MIN..=MU_MAX` (mirrored by the soundness test's
/// residual-log cap).
pub(super) const MU_MIN: usize = 22;
pub(super) const MU_MAX: usize = leanvm_core::pcs::MAX_MU;

const _: () = assert!(MU_MIN >= leanvm_core::pcs::MIN_MU);

/// The guest's baked buffer caps, which `placeholder_map` compiles in and
/// `gen_verify` admits against: one definition, so a hinted shape can never
/// outgrow the buffer the guest was compiled with.
pub(super) const MU_CAP: usize = 40;
pub(super) const STREAM_CAP: usize = 8192;
