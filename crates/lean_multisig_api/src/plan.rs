//! Recursion-tree planner.
//!
//! A single proving job has a bounded trace size, so aggregating more than roughly
//! `LEAF_TARGET` signatures needs a tree: leaves prove chunks of raw signatures, internal
//! nodes prove batches of child proofs, and the root produces the proof that goes on the wire.
//!
//! This module computes only the *shape* of that tree. It is pure: no proving, no I/O. That
//! keeps the topology testable in milliseconds rather than at proving cost.

use rec_aggregation::MAX_RECURSIONS;
use std::ops::Range;

/// Raw signatures per leaf.
///
/// Originally taken from `src/main.rs`'s tuned topology (leaves of 508..1550), then measured:
/// `round_trip.rs`'s two `#[ignore]`d boundary tests prove a full 1500-signature leaf and the
/// 1501 split, so this is a size the prover demonstrably accepts rather than a number inherited
/// from a benchmark.
///
/// Still unmeasured: the *largest* leaf that proves. 1500 sits under that topology's observed
/// 1550 for inherited reasons, so this is known-good, not known-optimal, and the headroom above
/// it is unknown. The 2^22 table height is the underlying bound but has never been computed
/// against. Raising it is a measurement task, and those two tests are where to do it.
pub(crate) const LEAF_TARGET: usize = 1500;

/// Most children one node may recurse over. Upstream rejects `children.len() > MAX_RECURSIONS`,
/// so a fan-in of exactly `MAX_RECURSIONS` is legal.
pub(crate) const MAX_FAN_IN: usize = MAX_RECURSIONS;

// Termination and well-formedness both depend on these, and `MAX_FAN_IN` comes from another
// crate: at a fan-in of 1 the fold below would never shrink the pool, and `step_by(0)` panics.
const _: () = assert!(MAX_FAN_IN >= 2 && LEAF_TARGET >= 1);

/// Fast proving, large proof. Leaf proofs are consumed immediately, so size is irrelevant.
pub(crate) const RATE_LEAF: usize = 1;

/// Internal proofs are also consumed by their parent, but there are fewer of them than leaves,
/// so they can afford a slower rate for a smaller intermediate proof.
pub(crate) const RATE_INTERNAL: usize = 2;

/// Smallest proof. Only the root goes on the wire.
pub(crate) const RATE_ROOT: usize = 4;

// The three rates above are literals restating the band `lean_prover::default_whir_config`
// accepts, and it `assert!`s rather than erroring — so a narrowed band upstream would abort
// every aggregation at proving time with no compile-time or test-time signal. Same guard the
// two constants above get, for the same reason: this crate does not own the value.
const _: () = assert!(
    RATE_LEAF >= lean_vm::MIN_WHIR_LOG_INV_RATE
        && RATE_ROOT <= lean_vm::MAX_WHIR_LOG_INV_RATE
        && RATE_LEAF <= RATE_INTERNAL
        && RATE_INTERNAL <= RATE_ROOT
);

/// One node of the recursion tree, or a caller-supplied aggregate reused as-is.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Plan {
    /// Return a caller-supplied aggregate unchanged; the index is into the supplied children.
    Passthrough(usize),
    /// A proving job.
    Node {
        /// Range into the raw-signature vector. Always empty when `children` is non-empty:
        /// the planner never mixes raw signatures and child proofs in one node, because
        /// `LEAF_TARGET` was tuned for raw-only nodes and the combined trace size is unmeasured.
        /// Upstream permits mixing (`src/main.rs` does it at raw counts of 10 and 25), so folding
        /// a small raw batch directly into a merging node — one proving job instead of two — is
        /// still open. It is roughly a 2x on the incremental "add my signatures to an existing
        /// aggregate" path, which is the likeliest real call shape. What blocks it is that
        /// whether `LEAF_TARGET` raw plus a full fan-in of children fits the trace bound has
        /// never been measured, and guessing wrong means a failed proof after minutes of work.
        raw: Range<usize>,
        children: Vec<Plan>,
        log_inv_rate: usize,
    },
}

/// Shapes the recursion tree for `n_raw` raw signatures and `n_children` supplied aggregates.
///
/// Does not enforce the `MAX_XMSS_AGGREGATED` signer ceiling: that is a property of the signer
/// set, not of the tree, and `aggregate` checks it up front before any proving happens.
///
/// Callers must reject empty input before calling: `plan(0, 0)` returns an empty root node
/// rather than erroring, because `aggregate` has already returned `Error::Empty` by then.
pub(crate) fn plan(n_raw: usize, n_children: usize) -> Plan {
    // A lone aggregate is already a valid proof; re-proving it would buy nothing.
    if n_raw == 0 && n_children == 1 {
        return Plan::Passthrough(0);
    }
    // Everything fits in one node: prove it directly at the root rate.
    if n_raw <= LEAF_TARGET && n_children == 0 {
        return Plan::Node {
            raw: 0..n_raw,
            children: vec![],
            log_inv_rate: RATE_ROOT,
        };
    }

    // Bottom level: raw signatures partitioned into leaves. Supplied aggregates join them as
    // passthroughs, since they are already proved.
    //
    // The split is greedy, so the remainder can be tiny: `plan(LEAF_TARGET + 1, 0)` gives leaves
    // of 1500 and 1, a whole proving job for one signature. `execute` proves nodes one after
    // another, so wall-clock is the sum over nodes and a greedy split is not itself worse
    // than a balanced 751 + 750 — the open question is whether per-node trace padding makes the
    // degenerate leaf cost more than balancing would. Unmeasured.
    //
    // One data point against balancing: proving 1501 as [1500, 1] plus a root measures *faster*
    // than proving 1500 as a single node (6.7s vs 8.2s), because leaves run at `RATE_LEAF` and
    // only the root pays `RATE_ROOT`. The rate a node is assigned dominates the node count.
    let mut pool: Vec<Plan> = (0..n_raw)
        .step_by(LEAF_TARGET)
        .map(|start| Plan::Node {
            raw: start..(start + LEAF_TARGET).min(n_raw),
            children: vec![],
            log_inv_rate: RATE_LEAF,
        })
        .collect();
    pool.extend((0..n_children).map(Plan::Passthrough));

    // Fold the pool upwards until one node can fan in over all of what is left. Greedy again:
    // 17 items become 16 + 1 rather than a balanced 9 + 8. Since wall-clock is the sum over
    // nodes rather than a critical path, greedy chunking minimizes the node count and is the
    // better default; whether trace padding makes a lopsided split cost more is the same
    // unmeasured question as above.
    while pool.len() > MAX_FAN_IN {
        pool = pool
            .chunks(MAX_FAN_IN)
            .map(|group| {
                // A leftover group of one is already a valid proof of exactly its own contents;
                // wrapping it in a node would prove it a second time for no benefit.
                if let [only] = group {
                    only.clone()
                } else {
                    Plan::Node {
                        raw: 0..0,
                        children: group.to_vec(),
                        log_inv_rate: RATE_INTERNAL,
                    }
                }
            })
            .collect();
    }

    Plan::Node {
        raw: 0..0,
        children: pool,
        log_inv_rate: RATE_ROOT,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rec_aggregation::MAX_XMSS_AGGREGATED;

    #[test]
    fn leaf_target_is_mirrored_in_the_integration_suite() {
        // `tests/round_trip.rs` cannot see this constant — `pub(crate)` in a private module, and
        // an integration test is a separate crate — so it hard-codes 1500 to size the two
        // `#[ignore]`d tests that prove a real leaf of exactly `LEAF_TARGET` signatures and a real
        // split at `LEAF_TARGET + 1`. If you change this, change that: otherwise those tests go on
        // passing while testing a boundary that has moved out from under them.
        //
        // Every other test in this module uses `LEAF_TARGET` symbolically and so would follow a
        // change silently. This is the only one that pins the value.
        assert_eq!(LEAF_TARGET, 1500);
    }

    #[test]
    fn single_child_alone_is_passed_through() {
        // Re-proving a lone aggregate would burn a whole proving job for no benefit.
        assert_eq!(plan(0, 1), Plan::Passthrough(0));
    }

    #[test]
    fn small_raw_batch_is_one_node_at_root_rate() {
        // Must be RATE_ROOT, not RATE_LEAF: this node IS the wire proof.
        assert_eq!(
            plan(1, 0),
            Plan::Node {
                raw: 0..1,
                children: vec![],
                log_inv_rate: RATE_ROOT
            }
        );
        assert_eq!(
            plan(LEAF_TARGET, 0),
            Plan::Node {
                raw: 0..LEAF_TARGET,
                children: vec![],
                log_inv_rate: RATE_ROOT
            }
        );
    }

    #[test]
    fn empty_input_plans_an_empty_root() {
        // Documented contract: `plan` does not reject empty input, because `aggregate` has
        // already returned `Error::Empty` before it gets here.
        assert_eq!(
            plan(0, 0),
            Plan::Node {
                raw: 0..0,
                children: vec![],
                log_inv_rate: RATE_ROOT
            }
        );
    }

    #[test]
    fn overflowing_one_leaf_splits_and_adds_a_root() {
        let p = plan(LEAF_TARGET + 1, 0);
        let Plan::Node {
            raw,
            children,
            log_inv_rate,
        } = p
        else {
            panic!("expected a node")
        };
        assert!(raw.is_empty());
        assert_eq!(log_inv_rate, RATE_ROOT);
        assert_eq!(children.len(), 2);
        assert_eq!(
            children[0],
            Plan::Node {
                raw: 0..LEAF_TARGET,
                children: vec![],
                log_inv_rate: RATE_LEAF
            }
        );
        // The greedy split leaves a whole proving job for one signature. Asserted so the
        // degenerate shape is recorded rather than merely tolerated.
        assert_eq!(
            children[1],
            Plan::Node {
                raw: LEAF_TARGET..LEAF_TARGET + 1,
                children: vec![],
                log_inv_rate: RATE_LEAF
            }
        );
    }

    /// The sizes every whole-tree invariant is checked against. `LEAF_TARGET * 17` is the one
    /// that folds to a leftover group of one, the shape most likely to regress into a
    /// single-child node.
    const SHAPES: [usize; 6] = [
        1,
        2,
        LEAF_TARGET,
        LEAF_TARGET * 17,
        LEAF_TARGET * 40,
        MAX_XMSS_AGGREGATED,
    ];

    #[test]
    fn shape_invariants_hold_at_every_node() {
        for n in SHAPES {
            assert_shape(&plan(n, 0));
        }
    }

    fn assert_shape(p: &Plan) {
        if let Plan::Node { raw, children, .. } = p {
            assert!(children.len() <= MAX_FAN_IN, "fan-in {} too wide", children.len());
            // A node has either no children or at least two: a single-child node would prove its
            // only child a second time for nothing. Generalizes the leftover-of-one rule to every
            // level, including the root.
            assert!(children.len() != 1, "pointless single-child node");
            // The planner never mixes raw signatures with child proofs.
            assert!(raw.is_empty() || children.is_empty(), "unexpected mixed node");
            children.iter().for_each(assert_shape);
        }
    }

    #[test]
    fn a_leftover_group_of_one_is_not_wrapped_in_a_pointless_node() {
        // 17 leaves chunk into 16 + 1. Giving that lone leftover its own node would prove it a
        // second time for no benefit, the same waste `Passthrough` exists to avoid.
        let p = plan(LEAF_TARGET * 17, 0);
        let Plan::Node { children, .. } = &p else {
            panic!("expected a node")
        };
        assert_eq!(children.len(), 2);
        assert_eq!(
            children[1],
            Plan::Node {
                raw: LEAF_TARGET * 16..LEAF_TARGET * 17,
                children: vec![],
                log_inv_rate: RATE_LEAF
            }
        );
    }

    #[test]
    fn every_raw_signature_is_covered_exactly_once() {
        // The planner returns index ranges, so off-by-ones would otherwise be silent.
        let n = LEAF_TARGET * 3 + 7;
        let mut seen = vec![0u8; n];
        // No children supplied: any Passthrough here is itself a failure.
        collect(&plan(n, 0), &mut seen, &mut []);
        assert!(seen.iter().all(|&c| c == 1), "each raw sig must appear exactly once");
    }

    #[test]
    fn mixed_raw_and_children_are_each_covered_exactly_once() {
        // Passthrough indices are used to index the caller's supplied-children slice, so a
        // dropped, duplicated, or off-by-one index is an out-of-bounds panic at best and the
        // wrong signer set proved at worst. Wide enough to need more than one fold level.
        let (n_raw, n_children) = (LEAF_TARGET * 17 + 3, 20);
        let p = plan(n_raw, n_children);
        // The whole-tree invariants are otherwise only checked on raw-only plans.
        assert_shape(&p);
        assert_rates(&p, true);
        let mut raw_seen = vec![0u8; n_raw];
        let mut child_seen = vec![0u8; n_children];
        collect(&p, &mut raw_seen, &mut child_seen);
        assert!(
            raw_seen.iter().all(|&c| c == 1),
            "each raw sig must appear exactly once"
        );
        assert!(
            child_seen.iter().all(|&c| c == 1),
            "each supplied child must appear exactly once"
        );
    }

    /// Tallies how often each raw-signature index and each supplied-child index appears.
    /// An index outside either slice fails here, which is itself the failure we want.
    fn collect(p: &Plan, raw_seen: &mut [u8], child_seen: &mut [u8]) {
        match p {
            Plan::Passthrough(i) => {
                let n_children = child_seen.len();
                let Some(tally) = child_seen.get_mut(*i) else {
                    panic!("passthrough index {i} out of range (n_children = {n_children})")
                };
                *tally += 1;
            }
            Plan::Node { raw, children, .. } => {
                for i in raw.clone() {
                    raw_seen[i] += 1;
                }
                children.iter().for_each(|c| collect(c, raw_seen, child_seen));
            }
        }
    }

    #[test]
    fn log_inv_rate_rises_toward_the_root() {
        for n in SHAPES {
            assert_rates(&plan(n, 0), true);
        }
    }

    /// The root ships on the wire, so it is proved at `RATE_ROOT` whether or not it has
    /// children. Below it, leaves get `RATE_LEAF` and every internal node `RATE_INTERNAL`.
    fn assert_rates(p: &Plan, is_root: bool) {
        if let Plan::Node {
            children, log_inv_rate, ..
        } = p
        {
            let expected = if is_root {
                RATE_ROOT
            } else if children.is_empty() {
                RATE_LEAF
            } else {
                RATE_INTERNAL
            };
            assert_eq!(*log_inv_rate, expected, "wrong rate for {p:?}");
            children.iter().for_each(|c| assert_rates(c, false));
        }
    }
}
