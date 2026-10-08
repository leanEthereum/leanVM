//! Aggregation: prove a leaf program once, then a tree over copies of its proof, and report each kind of node and the whole tree.

use crate::refuse;
use crate::workload::Workload;
use bench::{Plan, Timing};
use clap::ValueEnum;
use leanvm::Prover;
use leanvm::aggregate::{Kind, Leaf, LeafShape, Tree, TreeProof, TreeShape};
use primitives::{pretty_f64, pretty_integer};

/// The leaf program.
#[derive(Clone, Copy, Debug, ValueEnum)]
pub enum LeafProgram {
    /// Fibonacci modulo 2^64, `n` steps.
    Fibonacci,
    /// `n` leanXMSS signatures.
    Leanxmss,
    /// `n` leanSPHINCS signatures.
    Leansphincs,
}

impl LeafProgram {
    /// The leaf's run at size `n`.
    pub fn workload(self, n: usize) -> Workload {
        match self {
            Self::Fibonacci => Workload::fibonacci(n),
            Self::Leanxmss => Workload::leanxmss(n),
            Self::Leansphincs => Workload::leansphincs(n),
        }
    }
}

fn ms(t: &Timing) -> String {
    format!("{} ms{}", pretty_f64(t.mean() * 1000.0), t.spread())
}

fn secs(t: &Timing) -> String {
    format!("{} s{}", pretty_f64(t.mean()), t.spread())
}

/// One kind of node: its circuit, its proof, and its times.
fn report(name: &str, tree: &Tree<'_>, kind: Kind, proof: &TreeProof, prove: &Timing, verify: &Timing) {
    let stats = tree.stats(kind);
    let rows: Vec<String> = (stats.tables.iter())
        .map(|t| format!("{} {} (2^{})", t.name, pretty_integer(&t.rows), t.height_log))
        .collect();
    println!("{name}");
    println!("  rows                        : {}", rows.join("  "));
    println!(
        "  committed words             : {} (2^{:.3})",
        pretty_integer(&stats.committed),
        (stats.committed as f64).log2()
    );
    println!(
        "  proof size                  : {:.1} KiB",
        proof.to_bytes().len() as f64 / 1024.0
    );
    println!("  proving                     : {}", secs(prove));
    println!("  verifying as a root         : {}", ms(verify));
}

/// Prove the leaf at `leaf_prover`'s rate, then the tree of `leaves` over copies of its proof, every tree proof at `prover`'s rate, and print the report.
///
/// The tree's first level verifies `arity_0` leaves, each node `arity` children.
pub fn run(
    leaf: &Workload,
    leaves: usize,
    arity_0: usize,
    arity: usize,
    leaf_prover: &Prover,
    prover: &Prover,
    plan: Plan,
) {
    let rate = prover.rate();
    let title = &leaf.title;

    // The leaf's run, measured, gives the shape its proofs announce: the tree is checked before anything is proven.
    let stats = leaf.measure();
    let shape = TreeShape {
        leaf: LeafShape::measured(&stats, leaf_prover.rate()),
        arity_0,
        arity,
        rate,
    };
    shape.root_kind(leaves).unwrap_or_else(|e| refuse(format_args!("{e}")));

    let (proved, leaf_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        leaf.prove(leaf_prover)
    });
    let (proof, output) = (&proved.proof, proved.output);
    let quiet = Plan::new(plan.repeat, 0);

    let (tree, setup) = Plan::new(1, 0).measure_quiet(|_| {
        let _span = tracing::info_span!("Tree setup").entered();
        Tree::new(&leaf.program, shape).unwrap_or_else(|e| refuse(format_args!("{e}")))
    });
    let leaves_proofs = vec![Leaf::new(proof, output); leaves];

    println!(
        "Aggregation tree over {leaves} x {title}, first level {arity_0}, arity {arity}, leaves at log-inv-rate {}, tree proofs at {}",
        leaf_prover.rate().log_inv_rate(),
        rate.log_inv_rate()
    );
    println!("leaf");
    println!(
        "  committed words             : {} (2^{:.3})",
        pretty_integer(&stats.committed),
        (stats.committed as f64).log2()
    );
    println!(
        "  proof size                  : {:.1} KiB",
        proof.to_bytes().len() as f64 / 1024.0
    );
    println!("  proving                     : {}", secs(&leaf_time));
    println!("tree setup (both circuits, the fixed polynomials): {}", secs(&setup));

    let firsts = vec![Leaf::new(proof, output); arity_0];
    let (first, first_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        tree.prove_first(&firsts).expect("honest leaves")
    });
    let outputs = vec![output; arity_0];
    let (_, first_verify) = quiet.measure_quiet(|_| tree.verify(&first, &outputs).expect("a first-level root"));
    report(
        &format!("first-level node, {arity_0} leaves"),
        &tree,
        Kind::First,
        &first,
        &first_time,
        &first_verify,
    );

    if leaves > arity_0 {
        let children = vec![first; arity];
        let (node, node_time) = plan.warm_then_measure(|last| {
            let _quiet = (!last).then(bench::suppress_tracing);
            tree.prove_node(&children).expect("honest children")
        });
        let outputs = vec![output; arity_0 * arity];
        let (_, node_verify) = quiet.measure_quiet(|_| tree.verify(&node, &outputs).expect("a root"));
        report(
            &format!("node, {arity} children"),
            &tree,
            Kind::Node,
            &node,
            &node_time,
            &node_verify,
        );
    }

    let (root, whole) = Plan::new(1, 0).measure_quiet(|_| {
        let _span = tracing::info_span!("Prove tree", leaves).entered();
        tree.prove(&leaves_proofs)
            .unwrap_or_else(|e| refuse(format_args!("{e}")))
    });
    let outputs = vec![output; leaves];
    let (_, root_verify) = quiet.measure_quiet(|_| tree.verify(&root, &outputs).expect("the root verifies"));
    println!("whole tree");
    println!(
        "  proving every node          : {}, after the leaf proofs",
        secs(&whole)
    );
    println!("  verifying the root          : {}", ms(&root_verify));
    println!(
        "  peak memory                 : {} GiB",
        pretty_f64(bench::peak_rss_bytes() as f64 / (1u64 << 30) as f64)
    );
}
