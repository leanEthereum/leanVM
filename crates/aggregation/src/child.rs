//! The guest's witness for one child proof, and the opening shapes it shares with the guest's constants.

use super::cells::count;
use super::error::AggregateError;
use super::hints::Hints;
use fiat_shamir_prover::merkle::{hash_pair, hash_to_scalars, hash_words};
use lean_vm_core::cpu::{col_kappa_sources, from_scalar, layout_of};
use lean_vm_core::leaf::{self, Block};
use lean_vm_core::witness::Placement;
use primitives::field::F128;

/// The path bits a query's Merkle walk dispatches on at a time, the guest's `QW` (`walk_path`).
pub(super) const QUERY_WINDOW_BITS: usize = 6;

/// The depth of the cap a level's paths are walked into, which leaves the walked part whole windows of
/// [`QUERY_WINDOW_BITS`] bits: at least two levels deep, and from `log2(queries) - 5` to five levels below that.
pub(super) fn merkle_cap_depth(queries: usize, depth: usize) -> usize {
    let near = (queries.next_power_of_two().ilog2() as usize)
        .saturating_sub(QUERY_WINDOW_BITS - 1)
        .max(2)
        .min(depth);
    depth - (depth - near) / QUERY_WINDOW_BITS * QUERY_WINDOW_BITS
}

/// `count(g)` for each run of one group `g` in the stacking order, `members` holding each member's place in that order
/// and whether it starts a group, in member order. A group that came back after another would be named twice, so the
/// run count checks each group is one run.
fn group_order(members: &[((usize, usize), bool)]) -> Vec<F128> {
    // Each member's place and group, insertion sorted by place: a child has a few hundred members at most.
    let mut order: Vec<((usize, usize), usize)> = Vec::with_capacity(members.len());
    let mut groups = 0;
    for &(place, starts) in members {
        groups += usize::from(starts);
        order.push((place, groups - 1));
        let mut j = order.len() - 1;
        while j > 0 && order[j - 1].0 > place {
            order.swap(j - 1, j);
            j -= 1;
        }
    }
    let mut runs = Vec::with_capacity(groups);
    let mut last = None;
    for (_, group) in order {
        if last != Some(group) {
            runs.push(count(group));
            last = Some(group);
        }
    }
    assert_eq!(runs.len(), groups, "a group's members are consecutive");
    runs
}

/// The guest's witness for verifying one child (`guests/lean_ethereum.py`), built from the layout of an execution of
/// the `2^kbc`-instruction inner program at the sizes the `summary` the `verifier` crate read out of the child's
/// `proof` announces, and from that proof's Merkle paths, whose positions and sizes its replay pinned. Nothing here
/// says the child verifies: the guest's run does.
pub(super) fn gen_verify(
    kbc: usize,
    proof: &verifier::Proof,
    summary: &verifier::Summary,
) -> Result<Hints, AggregateError> {
    let rows = std::array::from_fn(|t| summary.table_rows[t] as usize);
    let layout = layout_of(kbc, summary.log_memory, rows);
    let blocks = [&layout.push[..], &layout.pull, &layout.count];
    // The guest's buffers have fixed capacities, so its constants do not depend on a child's shape. A child that
    // verifies fits them.
    let sides = blocks.map(leaf::layout);
    if proof.stream.len() > STREAM_CAP || sides.iter().any(|side| side.mu > MU_CAP) {
        return Err(AggregateError::InvalidChild);
    }
    // The guest replays the proof off the same stream the native verifier reads: every transmitted scalar is already
    // there in protocol order.
    let stream = (0..STREAM_CAP).map(|i| proof.stream.get(i).map_or(F128::ZERO, |&x| from_scalar(x)));
    let mut hints = Hints::default();
    hints.push("stream", stream.collect());
    // The table sumcheck's round count, which the guest certifies is the largest of the taus.
    hints.push_count("zc_tau_max", *layout.taus.iter().max().unwrap());
    // Every table's log height, which the guest certifies against its row count.
    hints.push("table_logs", layout.taus.iter().map(|&t| count(t)).collect());
    hints.push("col_group_order", col_group_order(kbc, &layout.placements));
    hints.push("block_group_order", block_group_order(blocks, &sides));
    merkle_hints(&mut hints, proof);
    Ok(hints)
}

/// The committed columns in their stacking order (`placements_of`: descending kappa, then index), each run of a column
/// group (a maximal run of committed columns, in compact order, of one kappa source) named once. The guest certifies
/// the order before it reads claims by it.
fn col_group_order(kbc: usize, placements: &[Placement]) -> Vec<F128> {
    let (mut members, mut last) = (Vec::new(), None);
    for (placement, source) in placements.iter().zip(col_kappa_sources(kbc)) {
        if source.is_some() {
            members.push(((0, placement.offset), source != last));
            last = source;
        }
    }
    group_order(&members)
}

/// Per bus side, its blocks in their stacking order (their offsets in the side's `layouts`), each run of a block group
/// (a maximal run of a side's blocks of one kappa source, `block_kappa_sources`: each boundary block its own, a table's
/// blocks their table's) named once. The guest certifies the native verifier's order (descending kappa, then index)
/// before it derives offsets from it.
fn block_group_order(sides: [&[Block]; 3], layouts: &[leaf::Layout; 3]) -> Vec<F128> {
    let mut members = Vec::new();
    for (side, (blocks, layout)) in sides.iter().zip(layouts).enumerate() {
        for (b, (block, &offset)) in blocks.iter().zip(&layout.offsets).enumerate() {
            let starts = b == 0 || block.owner.is_none() || block.owner != blocks[b - 1].owner;
            members.push(((side, offset), starts));
        }
    }
    group_order(&members)
}

/// The stacked WHIR opening's Merkle witness, per level: each query's leaf row and the sibling of every node it
/// climbs through below the level's cap, then the cap, every node of the top [`merkle_cap_depth`] levels the queries
/// reach, and which of its nodes they reach. The upper tree is shared by a level's queries; a subtree no query reaches
/// stays zero, unread. A level's query count and tree depth are its paths', which the replay pinned.
fn merkle_hints(hints: &mut Hints, proof: &verifier::Proof) {
    for (level, phase) in proof.merkle_openings.iter().enumerate() {
        let depth = phase.first().map_or(0, |opening| opening.siblings.len());
        let cap_depth = merkle_cap_depth(phase.len(), depth);
        let path_depth = depth - cap_depth;
        let mut nodes = vec![[0u8; 32]; 2 << cap_depth];
        let mut active = vec![F128::ZERO; 1 << cap_depth];
        for opening in phase {
            // Level 0's rows are K lanes, a cell each; deeper ones E words, two lanes a cell.
            let (leaf, width) = (&opening.leaf, if level == 0 { 1 } else { 2 });
            let cell = |i: usize| F128::new(leaf[width * i].0, if width == 2 { leaf[2 * i + 1].0 } else { 0 });
            let row = (0..leaf.len() / width).map(cell).collect();
            hints.push("merkle_leaf_rows", row);
            let mut path_siblings = Vec::with_capacity(2 * path_depth);
            let mut node = hash_words(opening.leaf.iter().map(|word| word.0));
            let mut index = (1 << depth) + opening.leaf_index as usize;
            for (height, sibling) in opening.siblings.iter().enumerate() {
                let (left, right) = if index & 1 == 0 {
                    (&node, sibling)
                } else {
                    (sibling, &node)
                };
                if height < path_depth {
                    path_siblings.extend_from_slice(&hash_to_scalars::<F128>(sibling));
                } else {
                    nodes[index] = node;
                    nodes[index ^ 1] = *sibling;
                    active[index >> 1] = F128::ONE;
                }
                node = hash_pair(left, right);
                index >>= 1;
            }
            nodes[1] = node;
            hints.push("merkle_children", path_siblings);
        }
        let mut caps = Vec::with_capacity(2 * nodes.len());
        for node in &nodes {
            caps.extend_from_slice(&hash_to_scalars::<F128>(node));
        }
        hints.push("merkle_caps", caps);
        hints.push("merkle_cap_active", active);
    }
}

/// The guest's baked buffer caps, which `placeholder_map` compiles in and
/// `gen_verify` admits against: one definition, so a hinted shape can never
/// outgrow the buffer the guest was compiled with.
pub(super) const MU_CAP: usize = 40;
pub(super) const STREAM_CAP: usize = 8192;
