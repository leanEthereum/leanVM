//! The guest's witness for one child proof, and the opening shapes it shares with the guest's constants.

use super::cells::count;
use super::error::AggregateError;
use super::hints::SubHints;
use fiat_shamir_prover::merkle::{hash_pair, hash_to_scalars, hash_words};
use lean_vm_core::cpu::from_scalar;
use primitives::field::F128;
use verifier::layout::{SizeSource, StackBlock, stack_blocks};

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
pub(super) const QUERY_WINDOWS_CAP: usize = 42;

/// The depth of the cap a level's paths are walked into, which leaves the walked part whole windows of
/// [`QUERY_WINDOW_BITS`] bits: at least two levels deep, and from `log2(queries) - 5` to five levels below that.
pub(super) fn merkle_cap_depth(queries: usize, depth: usize) -> usize {
    let near = (queries.next_power_of_two().ilog2() as usize)
        .saturating_sub(QUERY_WINDOW_BITS - 1)
        .max(2)
        .min(depth);
    depth - (depth - near) / QUERY_WINDOW_BITS * QUERY_WINDOW_BITS
}

/// The guest's witness for verifying one child (`guests/lean_ethereum.py`): the proof stream, the shape the guest
/// certifies against the announced sizes (each table's log height, the tallest, the pointer width), the stack's
/// placement, the split program's columns where the link reads them (`split_values`, the claim the child raises) and
/// the opening's Merkle paths. Nothing here says the child verifies: the guest's run does.
pub(super) fn gen_verify(
    kbc: usize,
    proof: &verifier::Proof,
    summary: &verifier::Summary,
    split_values: &[F128],
) -> Result<SubHints, AggregateError> {
    // The guest's buffers have fixed capacities, so its constants do not depend on a child's shape. A child that
    // verifies fits them.
    if proof.stream.len() > STREAM_CAP {
        return Err(AggregateError::InvalidChild);
    }
    let heights = verifier::layout::table_log_heights(&summary.table_rows);
    let cycles: u64 = summary.table_rows.iter().sum();
    let bits = (u64::BITS - cycles.leading_zeros()) as usize;
    let width = verifier::pointer_width(summary.log_memory, kbc, cycles);
    let n_rows = *heights.iter().max().unwrap();
    let kappas: Vec<usize> = stack_blocks()
        .iter()
        .map(|block| {
            let base = match block.source {
                SizeSource::Memory => summary.log_memory,
                SizeSource::Table(t) => heights[t],
            };
            base + block.adj
        })
        .collect();
    let mut stream: Vec<F128> = proof.stream.iter().copied().map(from_scalar).collect();
    stream.resize(
        stream.len().next_multiple_of(STREAM_CHUNK).max(STREAM_CHUNK),
        F128::ZERO,
    );

    let mut hints: SubHints = vec![("stream_chunks", vec![count(stream.len() / STREAM_CHUNK)])];
    hints.extend(stream.chunks(STREAM_CHUNK).map(|chunk| ("stream", chunk.to_vec())));
    hints.extend([
        ("table_logs", heights.iter().map(|&h| count(h)).collect()),
        // The tallest table's log height, the pointer width, whether the width is the cycles' bit length, and how
        // many permutations draw the link's packed challenges.
        (
            "link_shape",
            vec![
                count(n_rows),
                count(width),
                if width == bits { F128::ONE } else { F128::ZERO },
                count(verifier::packed_challenges(&verifier::layout::tables(), n_rows, width).div_ceil(8)),
            ],
        ),
    ]);
    hints.push(("stk_group_order", stk_group_order(&kappas)));
    hints.push(("split_values", split_values.to_vec()));
    let (config, _, depth) =
        whir_levels(summary.stack_log, summary.log_inv_rate).ok_or(AggregateError::InvalidChild)?;
    hints.extend(merkle_hints(config.queries, &depth, proof));
    Ok(hints)
}

/// A block's kappa source in the guest's `kappa_base`: 1 for the memory, `2 + t` for table `t`.
pub(super) fn source_index(source: SizeSource) -> usize {
    match source {
        SizeSource::Memory => 1,
        SizeSource::Table(table) => 2 + table,
    }
}

/// The first block of each run of consecutive blocks sharing a source and an adjustment. A run's blocks have one
/// size, so they are consecutive in the stack's order.
pub(super) fn block_groups(blocks: &[StackBlock]) -> Vec<usize> {
    let key = |block: &StackBlock| (block.source, block.adj);
    (0..blocks.len())
        .filter(|&i| i == 0 || key(&blocks[i]) != key(&blocks[i - 1]))
        .collect()
}

/// The block groups in the stack's order (`verifier::stack_offsets`: size down, then index), which `certify_stack`
/// certifies, for blocks of log sizes `kappas` (in [`stack_blocks`] order).
pub(super) fn stk_group_order(kappas: &[usize]) -> Vec<F128> {
    let starts = block_groups(&stack_blocks());
    let mut order: Vec<usize> = (0..starts.len()).collect();
    order.sort_by_key(|&g| (std::cmp::Reverse(kappas[starts[g]]), starts[g]));
    order.into_iter().map(count).collect()
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
        hints.push(("merkle_caps", nodes.iter().flat_map(hash_to_scalars).collect()));
        hints.push(("merkle_cap_active", active));
    }
    hints
}

/// The guest's baked buffer caps, which `placeholder_map` compiles in and
/// `gen_verify` admits against: one definition, so a hinted shape can never
/// outgrow the buffer the guest was compiled with.
pub(super) const STREAM_CAP: usize = 8192;
/// Proof-stream words a hint: the guest's stream buffer is the child's stream in whole chunks of them.
pub(super) const STREAM_CHUNK: usize = 256;
