//! Aggregation: prove a leaf program, then a tree over copies of its proof, and report each kind of node and the
//! whole tree.

use bench::{Plan, Timing};
use leanvm::aggregate::{Kind, Tree, TreeProof};
use leanvm::{Proved, Prover, Rate};
use primitives::{pretty_f64, pretty_integer};

use crate::recursion::{TABLES, inner};

fn ms(t: &Timing) -> String {
    format!("{} ms{}", pretty_f64(t.mean() * 1000.0), t.spread())
}

fn secs(t: &Timing) -> String {
    format!("{} s{}", pretty_f64(t.mean()), t.spread())
}

/// One kind of node: its circuit, its proof and statement, and its times.
fn report(name: &str, tree: &Tree, kind: Kind, proof: &TreeProof, prove: &Timing, verify: &Timing) {
    let stats = tree.stats(kind);
    let rows: Vec<String> = TABLES
        .iter()
        .zip(stats.rows.iter().zip(&stats.log_rows))
        .map(|(name, (rows, log))| format!("{name} {} (2^{log})", pretty_integer(rows)))
        .collect();
    println!("{name}");
    println!("  rows                        : {}", rows.join("  "));
    println!(
        "  committed words             : {} (2^{:.3})",
        pretty_integer(&stats.committed),
        (stats.committed as f64).log2()
    );
    println!(
        "  proof size                  : {:.1} KiB proof, {} statement words",
        proof.proof.to_bytes().len() as f64 / 1024.0,
        proof.statement.words().len()
    );
    println!("  proving                     : {}", secs(prove));
    println!("  verifying the proof         : {}", ms(verify));
}

/// Prove the leaf program at `rate`, then the tree of `arity` over `leaves` copies of its proof, every proof at
/// `rate`, and print the report.
pub fn run(program: &str, n: usize, leaves: usize, arity: usize, prover: &Prover, rate: Rate, plan: Plan) {
    let (title, program, advice, expected) = inner(program, n);
    let (proved, leaf_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        prover.prove(&program, &advice, rate).expect("the run halts")
    });
    let Proved {
        proof, output, stats, ..
    } = proved;
    assert_eq!(output, expected, "the leaf output is the native reference's");
    let quiet = Plan::new(plan.repeat, 0);
    let (_, leaf_verify) =
        quiet.measure_quiet(|_| leanvm::verify(&program, &output, &proof).expect("the leaf verifies"));

    let start = std::time::Instant::now();
    let tree = Tree::new(&program, &proof, arity, rate).expect("a leaf shape");
    let setup = start.elapsed().as_secs_f64();

    println!(
        "Aggregation tree over {leaves} x {title}, arity {arity}, log-inv-rate {}",
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
    println!("  verifying                   : {}", ms(&leaf_verify));
    println!(
        "tree setup (the three circuits, the fixed polynomials): {} s",
        pretty_f64(setup)
    );

    let (lift, lift_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        tree.prove_lift(prover, &proof, output).expect("an honest leaf")
    });
    let (_, lift_verify) = quiet.measure_quiet(|_| tree.verify_proof(&lift).expect("the lift verifies"));
    report("lift node", &tree, Kind::Lift, &lift, &lift_time, &lift_verify);

    let children = vec![lift; arity];
    let (first, first_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        tree.prove_node(prover, &children).expect("honest children")
    });
    let (_, first_verify) = quiet.measure_quiet(|_| tree.verify_proof(&first).expect("the node verifies"));
    report(
        &format!("first-level node, arity {arity}"),
        &tree,
        Kind::First,
        &first,
        &first_time,
        &first_verify,
    );
    let (_, settle) = quiet.measure_quiet(|_| tree.verify(&first, &vec![output; arity]).expect("a root"));
    println!("  as a root, with its claims  : {}", ms(&settle));

    let children = vec![first; arity];
    let (node, node_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        tree.prove_node(prover, &children).expect("honest children")
    });
    let (_, node_verify) = quiet.measure_quiet(|_| tree.verify_proof(&node).expect("the node verifies"));
    report(
        &format!("node over nodes, arity {arity}"),
        &tree,
        Kind::Node,
        &node,
        &node_time,
        &node_verify,
    );
    let outputs = vec![output; arity * arity];
    let (_, settle) = quiet.measure_quiet(|_| tree.verify(&node, &outputs).expect("a root"));
    println!("  as a root, with its claims  : {}", ms(&settle));

    let leaf_proofs = vec![(&proof, output); leaves];
    let start = std::time::Instant::now();
    let root = tree.prove(prover, &leaf_proofs).expect("honest leaves");
    let whole = start.elapsed().as_secs_f64();
    let outputs = vec![output; leaves];
    let (_, root_verify) = quiet.measure_quiet(|_| tree.verify(&root, &outputs).expect("the root verifies"));
    println!("whole tree");
    println!(
        "  proving every lift and node : {} s, after {leaves} leaf proofs",
        pretty_f64(whole)
    );
    println!("  verifying the root          : {}", ms(&root_verify));
    println!(
        "  peak memory                 : {} GiB",
        pretty_f64(bench::peak_rss_bytes() as f64 / (1u64 << 30) as f64)
    );
}
