//! The no-arena path, in its own binary: `enable_arena` is a process-wide
//! one-way opt-in, so a test that must not have it cannot share a process with
//! `tests/api.rs`.

use leanvm::asm::*;
use leanvm::*;

#[test]
fn proving_without_the_arena() {
    setup_prover_without_arena();
    assert!(!zk_alloc::is_enabled(), "this path must leave the arena disengaged");

    // A countdown, returning how far it counted.
    let text = Asm::new()
        .li(T0, 300)
        .label("loop")
        .i("addi", A0, A0, 1)
        .i("addi", T0, T0, -1)
        .branch("bne", T0, ZERO, "loop")
        .exit()
        .finish();
    let program = Program::new(&text, TEXT_BASE, vec![], 2, 0);
    let (proof, output, _) = prove(&program, [0; 4], &[], MIN_LOG_INV_RATE).expect("the run halts");
    assert_eq!(output, [300, 0, 0, 0]);
    verify(&program, &[0; 4], &output, &proof).expect("the proof verifies");

    let mut wrong_output = output;
    wrong_output[0] += 1;
    assert!(verify(&program, &[0; 4], &wrong_output, &proof).is_err());
}
