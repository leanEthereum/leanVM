//! Recursion on the machine itself: prove a leaf program once, then a tower of programs each verifying copies of the proof below it.

use crate::refuse;
use crate::workload::{Items, Workload};
use bench::Plan;
use leanvm::aggregate::VerifierProgram;
use leanvm::{Output, Prover};

/// Prove the leaf at `leaf_prover`'s rate, then `levels` verifier programs at `prover`'s rate, each verifying
/// `leaves` copies of the proof below it, and print each one's report.
pub fn run(leaf: &Workload, leaves: usize, levels: usize, leaf_prover: &Prover, prover: &Prover, plan: Plan) {
    let proven = leaf.prove(leaf_prover);
    println!(
        "{}: proof at rate 1/{} of {} cycles, 2^{:.2} committed words",
        leaf.title,
        1 << leaf_prover.rate().log_inv_rate(),
        proven.stats.cycles(),
        (proven.stats.committed as f64).log2()
    );
    let (mut program, mut rate, mut below) = (leaf.program.clone(), leaf_prover.rate(), proven);
    for level in 1..=levels {
        let child = (&program, rate, below.output, &below.proof);
        let verifier = VerifierProgram::of(&vec![child; leaves])
            .unwrap_or_else(|e| refuse(format_args!("level {level} has no verifier program: {e}")));
        let workload = Workload {
            title: format!("Level {level}: verifier of {leaves} proofs of level {}", level - 1),
            program: verifier.program,
            advice: verifier.advice,
            expected: Some(Output::new(verifier.output)),
            items: Some(Items {
                count: leaves,
                name: "proof",
            }),
        };
        workload.run(prover, plan);
        if level < levels {
            below = workload.prove(prover);
            (program, rate) = (workload.program, prover.rate());
        }
    }
}
