//! The no-arena path, in its own binary: `enable_arena` is a process-wide
//! one-way opt-in, so a test that must not have it cannot share a process with
//! `api.rs`.

use leanvm::asm::*;
use leanvm::*;

#[test]
fn proving_without_the_arena() {
    let prover = Prover::without_arena();
    assert!(!zk_alloc::is_enabled(), "this path must leave the arena disengaged");

    // A countdown, returning how far it counted.
    let text = Asm::new()
        .li(Reg::T0, 300)
        .label("loop")
        .i(Addi, Reg::A0, Reg::A0, 1)
        .i(Addi, Reg::T0, Reg::T0, -1)
        .branch(Bne, Reg::T0, Reg::ZERO, "loop")
        .exit()
        .finish();
    let program = Program::new(&text, TEXT_BASE, vec![], 2, 0).expect("valid instruction program");
    let Proved { proof, output, .. } = prover.prove(&program, &[], Rate::MIN).expect("the run halts");
    assert_eq!(output, [300, 0, 0, 0]);
    verify(&program, &output, &proof).expect("the proof verifies");

    let mut wrong_output = output;
    wrong_output[0] += 1;
    assert!(verify(&program, &wrong_output, &proof).is_err());
}
