//! Assumptions: prove two runs of the Fibonacci guest and a guest that assumes them (`programs/defer`), check the
//! latter alone, then prove the tree that resolves its assumptions.

use crate::aggregate::{report, secs};
use crate::refuse;
use crate::workload::Workload;
use bench::Plan;
use leanvm::aggregate::{AssumedProofs, Kind, Leaf, LeafShape, Tree, TreeShape};
use leanvm::{Assumption, Output, Program, ProvenRun, Prover};
use primitives::pretty_integer;

/// Prove `F(n + 2)` from proofs of `F(n)` and `F(n + 1)`, resolve the assumptions in a tree, and print the report.
///
/// The three runs are leaves, proven at `leaf_prover`'s rate; the tree proof at `prover`'s.
pub fn run(n: u64, leaf_prover: &Prover, prover: &Prover, plan: Plan) {
    let rate = prover.rate();
    println!(
        "Assumptions resolved in a tree: the runs at log-inv-rate {}, the tree proof at {}",
        leaf_prover.rate().log_inv_rate(),
        rate.log_inv_rate()
    );
    let fibonacci = Program::from_elf(defer_host::FIBONACCI_ELF).expect("a guest's ELF file");
    let assuming = defer_host::run(fibonacci.digest_words(), n);
    // The three runs, each checked against the output its host computed.
    let runs: [Workload; 2] = std::array::from_fn(|i| Workload {
        title: format!("the Fibonacci guest, n = {}", n + i as u64),
        program: fibonacci.clone(),
        advice: vec![n + i as u64],
        expected: Some(Output::new(assuming.assumed[i].1)),
        items: None,
    });
    let outer = Workload {
        title: "the guest assuming both".into(),
        program: Program::from_elf(defer_host::ELF).expect("a guest's ELF file"),
        advice: assuming.run.advice,
        expected: Some(Output::new(assuming.run.expected)),
        items: None,
    };
    let prove = |workload: &Workload| {
        let (proved, time) = plan.warm_then_measure(|last| {
            let _quiet = (!last).then(bench::suppress_tracing);
            workload.prove(leaf_prover)
        });
        println!(
            "{}: {} cycles, proving {}",
            workload.title,
            pretty_integer(&proved.stats.cycles()),
            secs(&time)
        );
        proved
    };
    let inner: Vec<ProvenRun> = runs.iter().map(prove).collect();
    let proved = prove(&outer);
    let outer = &outer.program;

    // Alone, the guest's proof shows its committed values only under its assumptions.
    let committed = Output::new(assuming.committed);
    let assumptions = (assuming.assumed).map(|(program, output)| Assumption::new(program, Output::new(output)));
    let unresolved = (outer.verify_assuming(committed, &assumptions, &proved.proof))
        .unwrap_or_else(|e| refuse(format_args!("the guest's proof: {e}")));
    println!(
        "native verifier, the guest's proof alone: verifies, {} assumptions unresolved",
        unresolved.len()
    );

    let shape = |proof| LeafShape::of(proof).expect("an honest announcement");
    if shape(&inner[0].proof) != shape(&inner[1].proof) {
        refuse(format_args!(
            "the two Fibonacci runs have proofs of different shapes: pick another n"
        ));
    }
    let tree_shape = TreeShape {
        leaf: shape(&proved.proof),
        arity_0: 1,
        arity: 2,
        rate,
    };
    let tree = Tree::assuming(
        outer,
        tree_shape,
        AssumedProofs {
            program: &fibonacci,
            leaf: shape(&inner[0].proof),
            count: 2,
        },
    )
    .unwrap_or_else(|e| refuse(format_args!("{e}")));
    let assumed: Vec<Leaf<'_>> = inner.iter().map(Leaf::from).collect();
    let leaf = Leaf::assuming(&proved.proof, committed, &assumed);
    let (root, root_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        tree.prove_first(&[leaf])
            .unwrap_or_else(|e| refuse(format_args!("{e}")))
    });
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|_| {
        tree.verify(&root, &[committed])
            .unwrap_or_else(|e| refuse(format_args!("the root: {e}")));
    });
    report(
        "first-level node resolving 2 assumptions",
        &tree,
        Kind::First,
        &root,
        &root_time,
        &verify_time,
    );

    // The same guest's proof alone, its assumptions left in its output: what resolving them adds.
    let alone = Tree::new(outer, tree_shape).unwrap_or_else(|e| refuse(format_args!("{e}")));
    let rows = |tree: &Tree<'_>| -> Vec<(&'static str, i64)> {
        (tree.stats(Kind::First).tables.iter())
            .map(|t| (t.name, i64::try_from(t.rows).expect("rows fit")))
            .collect()
    };
    let added: Vec<String> = (rows(&tree).into_iter().zip(rows(&alone)))
        .map(|((name, with), (_, without))| format!("{name} {}", pretty_integer(&(with - without))))
        .collect();
    println!("rows the 2 assumptions add to a first-level node: {}", added.join("  "));
}
