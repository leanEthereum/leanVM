//! Aggregation: prove a leaf program once, then a tree over copies of its proof, and report each kind of node and the whole tree.

use bench::{Plan, Timing};
use clap::ValueEnum;
use leanvm::aggregate::{Kind, Leaf, LeafShape, Tree, TreeProof, TreeShape};
use leanvm::{Program, ProvenRun, Prover};
use primitives::{pretty_f64, pretty_integer};

use crate::guest::refuse;
use crate::{fibonacci, workload};

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

/// A tree's arities and leaf count.
#[derive(Clone, Copy, Debug)]
pub struct Shape {
    pub leaves: usize,
    pub arity_0: usize,
    pub arity: usize,
}

impl Shape {
    /// Whether the leaves are `arity_0` times a power of `arity`, and the arities make a tree.
    const fn is_tree(self) -> bool {
        if self.arity_0 == 0 || self.arity < 2 || !self.leaves.is_multiple_of(self.arity_0) {
            return false;
        }
        let mut nodes = self.leaves / self.arity_0;
        while nodes > 1 && nodes.is_multiple_of(self.arity) {
            nodes /= self.arity;
        }
        nodes == 1
    }
}

impl LeafProgram {
    /// The program, its advice and the output it must give.
    fn run(self, n: usize) -> (String, Program, Vec<u64>, [u64; 4]) {
        match self {
            Self::Fibonacci => {
                let (program, expected) = fibonacci::fibonacci_program(n);
                (
                    format!("Fibonacci, N = {}", pretty_integer(&n)),
                    program,
                    Vec::new(),
                    expected,
                )
            }
            Self::Leanxmss | Self::Leansphincs => {
                let w = if matches!(self, Self::Leanxmss) {
                    workload::leanxmss(n)
                } else {
                    workload::leansphincs(n)
                };
                (w.title.clone(), w.program(), w.advice, w.expected)
            }
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

/// Prove the leaf program, then the tree over copies of its proof, every proof at the prover's rate, and print the report.
pub fn run(leaf: LeafProgram, n: usize, shape: Shape, prover: &Prover, plan: Plan) {
    let rate = prover.rate();
    let Shape { leaves, arity_0, arity } = shape;
    if !shape.is_tree() {
        refuse(format_args!(
            "{leaves} leaves make no tree of a first level of {arity_0} and nodes of {arity}"
        ));
    }
    let (title, program, advice, expected) = leaf.run(n);
    let (proved, leaf_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        (prover.prove(&program, &advice)).unwrap_or_else(|e| refuse(format_args!("{title} has no proof: {e}")))
    });
    let ProvenRun {
        proof, output, stats, ..
    } = proved;
    assert_eq!(output, expected, "the leaf's output is the native reference's");
    let quiet = Plan::new(plan.repeat, 0);

    let leaf_shape = LeafShape::of(&proof).expect("an honest announcement");
    let (tree, setup) = Plan::new(1, 0).measure_quiet(|_| {
        let _span = tracing::info_span!("Tree setup").entered();
        Tree::new(
            &program,
            TreeShape {
                leaf: leaf_shape,
                arity_0,
                arity,
                rate,
            },
        )
        .unwrap_or_else(|e| refuse(format_args!("{e}")))
    });
    let leaves_proofs = vec![Leaf::new(&proof, output); leaves];

    println!(
        "Aggregation tree over {leaves} x {title}, first level {arity_0}, arity {arity}, log-inv-rate {}",
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

    let firsts = vec![Leaf::new(&proof, output); arity_0];
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
