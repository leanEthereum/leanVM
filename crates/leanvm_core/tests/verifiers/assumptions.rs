//! A run that assumes proofs: the verifier checks it against its committed values' digest and its assumptions, in
//! order, and leaves those assumptions unresolved.

use super::programs::fibonacci;
use leanvm::asm::*;
use leanvm::{Assumption, Output, Program, ProvenRun, Prover, Rate, Region};

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

/// The fold is BLAKE2s-256 personalized `assuming` over each assumption's program digest and output words, then the
/// committed digest's, all little-endian: a known answer of Python's `hashlib.blake2s(data, person=b"assuming")`.
#[test]
fn the_fold_is_blake2s_personalized_by_assuming() {
    let assumptions = [
        Assumption::new([1, 2, 3, 4], Output::new([5, 6, 7, 8])),
        Assumption::new([9, 10, 11, 12], Output::new([13, 14, 15, 16])),
    ];
    let committed = Output::new([11, 22, 33, 44]);
    assert_eq!(
        committed.assuming(&assumptions),
        Output::new([
            0xA768_5D74_C2D1_3403,
            0xA625_59EF_10D7_2384,
            0xA1B4_2850_0BC5_B2BF,
            0x8CD1_1330_BCD3_E848,
        ])
    );
    assert_eq!(committed.assuming(&[]), committed);
}

/// A proof of a run assuming two proofs verifies against its committed digest with exactly those assumptions, in that
/// order, which the verifier returns unresolved, and against nothing else.
#[test]
fn the_verifier_binds_the_assumptions_in_order() {
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
    program.verify(folded, &proof).expect("the folded output is the run's");

    assert!(
        program.verify(committed, &proof).is_err(),
        "the committed digest without its assumptions"
    );
    assert!(program.verify_assuming(committed, &[], &proof).is_err());

    let [first, second] = assumptions;
    let mut digest = *first.program();
    digest[0] ^= 1;
    let other = Assumption::new(digest, first.output());
    let mut moved = *second.output().words();
    moved[3] ^= 1;
    let wrong_output = Assumption::new(*second.program(), Output::new(moved));
    let wrong = [
        ("the assumptions reordered", vec![second, first]),
        ("one assumption dropped", vec![first]),
        ("one assumption duplicated", vec![first, second, second]),
        ("an assumption of another program", vec![other, second]),
        ("an assumption of another output", vec![first, wrong_output]),
    ];
    for (what, assumptions) in &wrong {
        assert!(
            program.verify_assuming(committed, assumptions, &proof).is_err(),
            "accepted {what}"
        );
    }
}
