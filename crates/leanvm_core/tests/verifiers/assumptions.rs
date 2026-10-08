//! A run that assumes proofs: both verifiers check it against its committed values' digest and its assumptions, in
//! order, and leave those assumptions unresolved.

use super::programs::fibonacci;
use super::python_verifier::PythonStatement;
use leanvm_core::asm::*;
use leanvm_core::{Assumption, Output, Program, ProvenRun, Prover, Rate, Region};

/// The program exiting with its four advice words.
fn echo() -> Program {
    let text = Asm::new()
        .li(Reg::T0, Region::ADVICE.base())
        .load(Ld, Reg::A0, 0, Reg::T0)
        .load(Ld, Reg::A1, 8, Reg::T0)
        .load(Ld, Reg::A2, 16, Reg::T0)
        .load(Ld, Reg::A3, 24, Reg::T0)
        .exit()
        .finish();
    Program::new(&text, Region::TEXT.base(), vec![], 2, 2).expect("a valid program")
}

/// The assumptions as the Python verifier reads them: each one's program digest, then its output.
fn words(assumptions: &[Assumption]) -> Vec<u64> {
    (assumptions.iter())
        .flat_map(|a| a.program().iter().copied().chain(<[u64; 4]>::from(a.output())))
        .collect()
}

fn hex(words: &[u64; 4]) -> String {
    words.map(|w| format!("{w:016x}")).join(" ")
}

/// A proof of a run assuming two proofs verifies against its committed digest with exactly those assumptions, in that
/// order, which both verifiers return unresolved; Python's fold is pinned to `Output::assuming` by accepting at all.
#[test]
fn both_verifiers_bind_the_assumptions_in_order() {
    let program = echo();
    let (fib, fib_output) = fibonacci();
    let committed = Output::new([11, 22, 33, 44]);
    let assumptions = [
        Assumption::new(fib.digest_words(), Output::new(fib_output)),
        Assumption::new(program.digest_words(), Output::new([1, 2, 3, 4])),
    ];
    let folded = committed.assuming(&assumptions);
    let ProvenRun { proof, output, .. } = Prover::new(Rate::MIN)
        .prove(&program, folded.words())
        .expect("the run halts");
    assert_eq!(folded, output);
    let unresolved = program
        .verify_assuming(committed, &assumptions, &proof)
        .expect("honest proof verifies");
    assert_eq!(unresolved, assumptions);

    let raw = program.verify_to_raw(output, &proof).expect("honest proof verifies");
    let python = PythonStatement::new("assuming", &program, committed.words());
    let accepted = python.verify_assuming(&raw, &words(&assumptions));
    assert!(
        accepted.status.success(),
        "Python refused the assumptions:\n{}",
        String::from_utf8_lossy(&accepted.stderr),
    );
    let mut expected: String = (assumptions.iter())
        .map(|a| {
            format!(
                "unresolved assumption: program {} output {}\n",
                hex(a.program()),
                hex(a.output().words())
            )
        })
        .collect();
    expected.push_str("verification succeeded\n");
    assert_eq!(String::from_utf8_lossy(&accepted.stdout), expected);

    PythonStatement::assert_rejects(&python.verify(&raw), "the committed digest without its assumptions");
    assert!(program.verify_assuming(committed, &[], &proof).is_err());

    let [first, second] = assumptions;
    let mut digest = *first.program();
    digest[0] ^= 1;
    let other = Assumption::new(digest, first.output());
    let wrong = [
        ("the assumptions reordered", vec![second, first]),
        ("one assumption dropped", vec![first]),
        ("one assumption duplicated", vec![first, second, second]),
        ("an assumption of another program", vec![other, second]),
    ];
    for (what, assumptions) in &wrong {
        PythonStatement::assert_rejects(&python.verify_assuming(&raw, &words(assumptions)), what);
        assert!(
            program.verify_assuming(committed, assumptions, &proof).is_err(),
            "Rust accepted {what}"
        );
    }
    let cut = &words(&assumptions)[..7];
    PythonStatement::assert_rejects(&python.verify_assuming(&raw, cut), "an assumption cut short");
}
