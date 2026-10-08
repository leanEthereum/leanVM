//! Aggregation: prove a leaf program once, then a tree of verifier programs over copies of its proof, and report each kind of node and the root.

use crate::refuse;
use crate::workload::Workload;
use bench::Plan;
use clap::ValueEnum;
use leanvm::aggregate::{Kind, LeafShape, Tree, TreeProof};
use leanvm::{Prover, Stats};
use primitives::{pretty_f64, pretty_integer};
use std::time::Instant;

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

/// One kind of tree proof: its program's run, its proof, and the time to make it.
fn report(name: &str, proof: &TreeProof, seconds: f64) {
    let stats: &Stats = proof.stats();
    println!("{name}");
    println!("  cycles (RISC-V)             : {}", pretty_integer(&stats.cycles()));
    println!(
        "  committed words             : {} (2^{:.3})",
        pretty_integer(&stats.committed),
        (stats.committed as f64).log2()
    );
    println!(
        "  proof size                  : {:.1} KiB",
        proof.proof().to_bytes().len() as f64 / 1024.0
    );
    println!("  proving                     : {} s", pretty_f64(seconds));
}

/// Prove the leaf at `leaf_prover`'s rate, then a tree over `leaves` copies of its proof, every tree proof at
/// `prover`'s rate, and print each kind's report: the first level verifies `arity_0` leaves, a node `arity` children.
pub fn run(
    leaf: &Workload,
    leaves: usize,
    arity_0: usize,
    arity: usize,
    leaf_prover: &Prover,
    prover: &Prover,
    _: Plan,
) {
    let proven = leaf.prove(leaf_prover);
    println!(
        "{}: proof at rate 1/{} of {} cycles, 2^{:.2} committed words",
        leaf.title,
        1 << leaf_prover.rate().log_inv_rate(),
        pretty_integer(&proven.stats.cycles()),
        (proven.stats.committed as f64).log2()
    );
    let shape = LeafShape::measured(&proven.stats, leaf_prover.rate());
    let start = Instant::now();
    let tree = Tree::new(&leaf.program, &shape, arity_0, arity, prover.rate())
        .unwrap_or_else(|e| refuse(format_args!("{} has no tree: {e}", leaf.title)));
    println!(
        "the tree's two programs     : built in {} s",
        pretty_f64(start.elapsed().as_secs_f64())
    );

    let timed = |f: &dyn Fn() -> TreeProof| {
        let start = Instant::now();
        let proof = f();
        (proof, start.elapsed().as_secs_f64())
    };
    let leaf_proof = (proven.output, &proven.proof);
    let (first, seconds) = timed(&|| {
        (tree.prove_first(&vec![leaf_proof; arity_0]))
            .unwrap_or_else(|e| refuse(format_args!("no first-level proof: {e}")))
    });
    report(
        &format!("First level: verifier of {arity_0} leaf proofs"),
        &first,
        seconds,
    );

    // Up the tree over copies, a node over first-level proofs, then nodes over nodes.
    let (mut root, mut covered) = (first, arity_0);
    while covered < leaves {
        let below = if root.kind() == Some(Kind::First) {
            "first-level"
        } else {
            "node"
        };
        let (node, seconds) = timed(&|| {
            (tree.prove_node(&vec![root.clone(); arity])).unwrap_or_else(|e| refuse(format_args!("no node: {e}")))
        });
        report(&format!("Node: verifier of {arity} {below} proofs"), &node, seconds);
        (root, covered) = (node, covered * arity);
    }
    let start = Instant::now();
    (tree.verify(&root, &vec![proven.output; covered]))
        .unwrap_or_else(|e| refuse(format_args!("the root does not verify: {e}")));
    println!(
        "root over {covered} leaves           : verified in {} ms",
        pretty_f64(start.elapsed().as_secs_f64() * 1000.0)
    );
}
