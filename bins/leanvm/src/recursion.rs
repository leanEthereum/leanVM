//! Recursion on the machine itself: prove a leaf program once, then a program verifying copies of its proof.

use crate::refuse;
use crate::workload::{Items, Workload};
use bench::Plan;
use leanvm::aggregate::VerifierProgram;
use leanvm::{Output, Prover};

/// Prove the leaf at `leaf_prover`'s rate, then the verifier of `leaves` copies of its proof at `prover`'s rate, and print both reports.
pub fn run(leaf: &Workload, leaves: usize, leaf_prover: &Prover, prover: &Prover, plan: Plan) {
    let proven = leaf.prove(leaf_prover);
    let child = (&leaf.program, leaf_prover.rate(), proven.output, &proven.proof);
    let verifier = VerifierProgram::of(&vec![child; leaves])
        .unwrap_or_else(|e| refuse(format_args!("{} has no verifier program: {e}", leaf.title)));
    println!(
        "{}: proof at rate 1/{} of {} cycles, 2^{:.2} committed words",
        leaf.title,
        1 << leaf_prover.rate().log_inv_rate(),
        proven.stats.cycles(),
        (proven.stats.committed as f64).log2()
    );
    Workload {
        title: format!("Verifier of {leaves} proofs of: {}", leaf.title),
        program: verifier.program,
        advice: verifier.advice,
        expected: Some(Output::new(verifier.output)),
        items: Some(Items {
            count: leaves,
            name: "proof",
        }),
    }
    .run(prover, plan);
}
