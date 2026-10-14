//! Aggregation: prove one leaf once, then a tree over copies of its proof, and report each kind of node and the whole tree.

use crate::refuse;
use crate::workload::Workload;
use bench::{Plan, Timing};
use bench::{pretty_f64, pretty_integer};
use clap::ValueEnum;
use leanvm::aggregate::{
    Aggregate, Capacity, CircuitStats, ClaimGroup, ClaimLeaf, ClaimSet, ClaimShape, Kind, Leaf, LeafShape,
    LeafStatement, Leaves, Subtree, TableStats, Tree, TreeProof, TreeShape,
};
use leanvm::{
    ProvenRun, Prover, SphincsBatch, SphincsClaim, SphincsProof, SphincsSignature, Stats, XmssBatch, XmssClaim,
    XmssProof, XmssSignature,
};

/// The leaf program.
#[derive(Clone, Copy, Debug, PartialEq, Eq, ValueEnum)]
pub enum LeafProgram {
    /// Fibonacci modulo 2^64, `n` steps.
    Fibonacci,
    /// `n` leanXMSS signatures, checked by a RISC-V guest.
    Leanxmss,
    /// `n` leanSPHINCS signatures, checked by a RISC-V guest.
    Leansphincs,
    /// `n` leanXMSS signatures, checked by one recursion circuit.
    LeanxmssRec,
    /// `n` leanSPHINCS signatures, checked by one recursion circuit.
    LeansphincsRec,
}

/// The tree's leaf family: its key and what each of its leaves proves.
enum Family {
    /// A RISC-V program's runs, and the shape their proofs announce.
    Runs {
        workload: Workload,
        stats: Stats,
        shape: LeafShape,
    },
    /// A leanXMSS batch circuit, and the claims and signatures each leaf proves.
    Xmss {
        batch: XmssBatch,
        claims: Vec<XmssClaim>,
        signatures: Vec<XmssSignature>,
    },
    /// A leanSPHINCS batch circuit, and the claims and signatures each leaf proves.
    Sphincs {
        batch: SphincsBatch,
        claims: Vec<SphincsClaim>,
        signatures: Vec<SphincsSignature>,
    },
}

/// The family's proven leaf.
enum Proven {
    Run(Box<ProvenRun>),
    Xmss(XmssProof),
    Sphincs(SphincsProof),
}

impl Family {
    /// The family of `program` at size `n`, its leaves proven by `prover`: zero knowledge only for a RISC-V program's runs.
    fn new(program: LeafProgram, n: usize, prover: &Prover) -> Self {
        let rate = prover.rate();
        let runs = |workload: Workload| {
            // The run, measured, gives the shape its proofs announce: the tree is built before anything is proven.
            let stats = workload.measure();
            let shape = LeafShape::measured(&stats, rate);
            let shape = if prover.is_zero_knowledge() {
                shape.zero_knowledge()
            } else {
                shape
            };
            Self::Runs { workload, stats, shape }
        };
        if prover.is_zero_knowledge() && matches!(program, LeafProgram::LeanxmssRec | LeafProgram::LeansphincsRec) {
            refuse(format_args!(
                "--zk is not for {program:?} leaves: a recursion proof is never zero knowledge"
            ));
        }
        match program {
            LeafProgram::Fibonacci => runs(Workload::fibonacci(n)),
            LeafProgram::Leanxmss => runs(Workload::leanxmss(n)),
            LeafProgram::Leansphincs => runs(Workload::leansphincs(n)),
            LeafProgram::LeanxmssRec => {
                let (claims, signatures) = crate::xmss::signed(n);
                Self::Xmss {
                    batch: XmssBatch::new(n, rate).unwrap_or_else(|e| refuse(format_args!("{e}"))),
                    claims,
                    signatures,
                }
            }
            LeafProgram::LeansphincsRec => {
                let (claims, signatures) = crate::sphincs::signed(n);
                Self::Sphincs {
                    batch: SphincsBatch::new(n, rate).unwrap_or_else(|e| refuse(format_args!("{e}"))),
                    claims,
                    signatures,
                }
            }
        }
    }

    fn title(&self) -> String {
        match self {
            Self::Runs { workload, .. } => workload.title.clone(),
            Self::Xmss { batch, .. } => format!(
                "leanXMSS verification on the recursion machine, {} signatures",
                batch.n()
            ),
            Self::Sphincs { batch, .. } => {
                format!(
                    "leanSPHINCS verification on the recursion machine, {} signatures",
                    batch.n()
                )
            }
        }
    }

    const fn leaves(&self) -> Leaves<'_> {
        match self {
            Self::Runs { workload, shape, .. } => Leaves::Runs {
                program: &workload.program,
                shape: *shape,
            },
            Self::Xmss { batch, .. } => batch.leaves(),
            Self::Sphincs { batch, .. } => batch.leaves(),
        }
    }

    fn prove(&self, prover: &Prover) -> Proven {
        match self {
            Self::Runs { workload, .. } => Proven::Run(Box::new(workload.prove(prover))),
            Self::Xmss {
                batch,
                claims,
                signatures,
            } => Proven::Xmss(batch.prove(claims, signatures).expect("honest signatures")),
            Self::Sphincs {
                batch,
                claims,
                signatures,
            } => Proven::Sphincs(batch.prove(claims, signatures).expect("honest signatures")),
        }
    }

    /// The leaf of its proven leaf, and what it states.
    fn leaf<'a>(&'a self, proven: &'a Proven) -> (Leaf<'a>, LeafStatement) {
        let leaf = match (self, proven) {
            (Self::Runs { .. }, Proven::Run(run)) => Leaf::from(&**run),
            (Self::Xmss { batch, claims, .. }, Proven::Xmss(proof)) => batch.leaf(claims, proof).expect("its claims"),
            (Self::Sphincs { batch, claims, .. }, Proven::Sphincs(proof)) => {
                batch.leaf(claims, proof).expect("its claims")
            }
            _ => unreachable!("a family's own proof"),
        };
        let statement = leaf.statement();
        (leaf, statement)
    }

    /// The claim set each leaf of `program` at size `n` publishes in a claim-set tree: the guest's signer set, or the
    /// batch's one group.
    fn claim_set(&self, program: LeafProgram, n: usize) -> ClaimSet {
        let groups = match (self, program) {
            (Self::Runs { .. }, LeafProgram::Leanxmss) => leanxmss_host::batch(n).set.label_groups(),
            (Self::Runs { .. }, LeafProgram::Leansphincs) => leansphincs_host::batch(n).set.label_groups(),
            (Self::Runs { .. }, _) => refuse(format_args!("{program:?} publishes no claim set")),
            (Self::Xmss { batch, claims, .. }, _) => {
                return batch.claim_set(claims).unwrap_or_else(|e| refuse(format_args!("{e}")));
            }
            (Self::Sphincs { batch, claims, .. }, _) => {
                return batch.claim_set(claims).unwrap_or_else(|e| refuse(format_args!("{e}")));
            }
        };
        ClaimSet {
            groups: (groups.into_iter())
                .map(|(label, members)| ClaimGroup { label, members })
                .collect(),
        }
    }

    /// Its circuit's rows per table, if a recursion circuit, and the words a proof commits.
    fn cost(&self) -> (Option<CircuitStats>, usize) {
        match self {
            Self::Runs { stats, .. } => (None, stats.committed),
            Self::Xmss { batch, .. } => {
                let stats = batch.stats();
                let committed = stats.committed;
                (Some(stats), committed)
            }
            Self::Sphincs { batch, .. } => {
                let stats = batch.stats();
                let committed = stats.committed;
                (Some(stats), committed)
            }
        }
    }
}

impl Proven {
    fn bytes(&self) -> usize {
        match self {
            Self::Run(run) => run.proof.to_bytes().len(),
            Self::Xmss(proof) => proof.to_bytes().len(),
            Self::Sphincs(proof) => proof.to_bytes().len(),
        }
    }
}

fn ms(t: &Timing) -> String {
    format!("{} ms{}", pretty_f64(t.mean() * 1000.0), t.spread())
}

fn secs(t: &Timing) -> String {
    format!("{} s{}", pretty_f64(t.mean()), t.spread())
}

/// A circuit's rows per table and padded heights, and the words a proof commits.
fn print_cost(stats: Option<&CircuitStats>, committed: usize) {
    if let Some(stats) = stats {
        let rows: Vec<String> = stats.tables.iter().map(table_row).collect();
        println!("  rows                        : {}", rows.join("  "));
    }
    println!(
        "  committed words             : {} (2^{:.3})",
        pretty_integer(&committed),
        (committed as f64).log2()
    );
}

/// One kind of node: its circuit, its proof, and its times.
fn report(name: &str, tree: &Tree<'_>, kind: Kind, proof: &TreeProof, prove: &Timing, verify: &Timing) {
    let stats = tree.stats(kind);
    println!("{name}");
    print_cost(Some(&stats), stats.committed);
    println!(
        "  proof size                  : {:.1} KiB",
        proof.to_bytes().len() as f64 / 1024.0
    );
    println!("  proving                     : {}", secs(prove));
    println!("  verifying as a root         : {}", ms(verify));
}

/// Prove one leaf of `program` at size `n` at `leaf_prover`'s rate, then the tree of `leaves` over copies of its proof, every tree proof at `prover`'s rate, and print the report.
///
/// The tree's first level verifies `arity_0` leaves, each node `arity` children. With `claims`, a claim-set tree of that
/// capacity: each leaf publishes its signer set, every node declares the union of its children's, and each proof is
/// verified as a root of its set.
pub fn run(
    (program, n): (LeafProgram, usize),
    (leaves, arity_0, arity): (usize, usize, usize),
    claims: Option<Capacity>,
    (leaf_prover, prover): (&Prover, &Prover),
    plan: Plan,
) {
    let rate = prover.rate();
    let shape = TreeShape {
        arity_0,
        arity,
        rate,
        claims: claims.map(ClaimShape::new),
    };
    shape.depth(leaves).unwrap_or_else(|e| refuse(format_args!("{e}")));
    let family = Family::new(program, n, leaf_prover);
    let set = claims.map(|_| family.claim_set(program, n));
    let title = family.title();

    let (proven, leaf_time) = plan.warm_then_measure(|| family.prove(leaf_prover));

    let (tree, setup) = Plan::default().measure_quiet(|| {
        let _span = tracing::info_span!("Tree setup").entered();
        Tree::new(family.leaves(), shape).unwrap_or_else(|e| refuse(format_args!("{e}")))
    });
    let (leaf, statement) = family.leaf(&proven);

    let semantics = claims.map_or_else(
        || "Aggregation tree".to_owned(),
        |c| {
            format!(
                "Claim-set tree (fewer than {} claims, at most {} groups)",
                c.claims, c.groups
            )
        },
    );
    println!(
        "{semantics} over {leaves} leaves of {title}, first level {arity_0}, arity {arity}, leaves at log-inv-rate {}, tree proofs at {}",
        leaf_prover.rate().log_inv_rate(),
        rate.log_inv_rate()
    );
    println!("leaf: {title}");
    let (stats, committed) = family.cost();
    print_cost(stats.as_ref(), committed);
    println!(
        "  proof size                  : {:.1} KiB",
        proven.bytes() as f64 / 1024.0
    );
    println!("  proving                     : {}", secs(&leaf_time));
    println!("tree setup (every circuit, the fixed polynomials): {}", secs(&setup));

    let arities = (leaves, arity_0, arity);
    match &set {
        None => outputs(&tree, &shape, (leaf, statement), arities, plan),
        Some(set) => claim_sets(&tree, &ClaimLeaf::new(leaf, set), arities, plan),
    }
    println!(
        "  peak memory                 : {} GiB",
        pretty_f64(bench::peak_rss_bytes() as f64 / (1u64 << 30) as f64)
    );
}

/// A tree of outputs over copies of `leaf`: its first-level node, its node, and the whole tree.
fn outputs(
    tree: &Tree<'_>,
    shape: &TreeShape,
    (leaf, statement): (Leaf<'_>, LeafStatement),
    (leaves, arity_0, arity): (usize, usize, usize),
    plan: Plan,
) {
    let quiet = plan.without_cooldown();
    let firsts = vec![leaf.clone(); arity_0];
    let (first, first_time) = plan.warm_then_measure(|| tree.prove_first(&firsts).expect("honest leaves"));
    let first_level = Subtree::First(vec![statement.clone(); arity_0]);
    let (_, first_verify) = quiet.measure_quiet(|| tree.verify(&first, &first_level).expect("a first-level root"));
    report(
        &format!("first-level node, {arity_0} leaves"),
        tree,
        Kind::First,
        &first,
        &first_time,
        &first_verify,
    );

    if leaves > arity_0 {
        let children = vec![first; arity];
        let (node, node_time) = plan.warm_then_measure(|| tree.prove_node(&children).expect("honest children"));
        let expected = Subtree::Node(vec![first_level; arity]);
        let (_, node_verify) = quiet.measure_quiet(|| tree.verify(&node, &expected).expect("a root"));
        report(
            &format!("node, {arity} first-level children"),
            tree,
            Kind::Node,
            &node,
            &node_time,
            &node_verify,
        );
    }

    let all = vec![leaf; leaves];
    let expected = Subtree::balanced(vec![statement; leaves], shape).unwrap_or_else(|e| refuse(format_args!("{e}")));
    let (root, whole) = Plan::default().measure_quiet(|| {
        let _span = tracing::info_span!("Prove tree", leaves).entered();
        tree.prove(&all).unwrap_or_else(|e| refuse(format_args!("{e}")))
    });
    let (_, root_verify) = quiet.measure_quiet(|| tree.verify(&root, &expected).expect("the root verifies"));
    print_whole(&whole, &root_verify);
}

/// A claim-set tree over copies of `leaf`: its first-level node, its node of `arity` children, and the balanced tree,
/// every node declaring the union of its children's sets.
fn claim_sets(tree: &Tree<'_>, leaf: &ClaimLeaf<'_>, (leaves, arity_0, arity): (usize, usize, usize), plan: Plan) {
    let quiet = plan.without_cooldown();
    let firsts = vec![leaf.clone(); arity_0];
    let (first, first_time) = plan.warm_then_measure(|| tree.aggregate_leaves(&firsts, None).expect("honest leaves"));
    let (_, first_verify) =
        quiet.measure_quiet(|| (tree.verify_claims(&first.proof, &first.claims)).expect("a first-level root"));
    report(
        &format!("first-level node, {arity_0} leaves"),
        tree,
        Kind::First,
        &first.proof,
        &first_time,
        &first_verify,
    );

    if leaves > arity_0 {
        let children = vec![&first; arity];
        let (node, node_time) = plan.warm_then_measure(|| tree.aggregate(&children, None).expect("honest children"));
        let (_, node_verify) = quiet.measure_quiet(|| (tree.verify_claims(&node.proof, &node.claims)).expect("a root"));
        report(
            &format!("node, {arity} first-level children"),
            tree,
            Kind::Node,
            &node.proof,
            &node_time,
            &node_verify,
        );
    }

    let (root, whole) = Plan::default().measure_quiet(|| {
        let _span = tracing::info_span!("Prove tree", leaves).entered();
        let refused = |e| refuse(format_args!("{e}"));
        let mut level: Vec<Aggregate> = (0..leaves / arity_0)
            .map(|_| tree.aggregate_leaves(&firsts, None).unwrap_or_else(refused))
            .collect();
        while level.len() > 1 {
            level = (level.chunks(arity))
                .map(|c| {
                    tree.aggregate(&c.iter().collect::<Vec<_>>(), None)
                        .unwrap_or_else(refused)
                })
                .collect();
        }
        level.pop().expect("one root")
    });
    let (_, root_verify) =
        quiet.measure_quiet(|| (tree.verify_claims(&root.proof, &root.claims)).expect("the root verifies"));
    print_whole(&whole, &root_verify);
    println!("  root's set                  : {} claims", root.claims.n_claims());
}

/// The whole tree's time after the leaf proofs, and its root's verification.
fn print_whole(whole: &Timing, root_verify: &Timing) {
    println!("whole tree");
    println!("  proving every node          : {}, after the leaf proofs", secs(whole));
    println!("  verifying the root          : {}", ms(root_verify));
}

/// A table's name, its rows and its height: `HASH 1,234 (2^11)`, or `STEP 0 (absent)` for a table the proof leaves out.
pub fn table_row(t: &TableStats) -> String {
    let height = t
        .height_log
        .map_or_else(|| "absent".to_owned(), |tau| format!("2^{tau}"));
    format!("{} {} ({height})", t.name, pretty_integer(&t.rows))
}
