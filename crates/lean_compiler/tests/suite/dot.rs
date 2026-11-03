//! `dot(x, w, acc)`: one `DOT` instruction, `acc + Σ_j w[j]·x_j` over the lanes of a run of
//! frame cells, two lanes a cell, the weights a heap slice read through its pointer.

use lean_compiler::{compile, parse};
use leanvm_core::cpu::{Op, prove, verify};
use primitives::field::{F192, g_pow};

/// The lanes `g^j`, two to a cell, against weights `y·g^j`: the result is `Σ_j y·g^2j`, which
/// the program publishes, so the proof verifies only if `DOT` computed it.
#[test]
fn dot_end_to_end() {
    let src = "\
def main():
    weights = HeapBuf(8)
    for j in unroll(0, 8):
        weights[GEN ** j] = f192(0, 1, 0) * GEN ** j
    lanes = StackBuf(4)
    for k in unroll(0, 4):
        lanes[k] = GEN ** (2 * k) + f192(0, 1, 0) * GEN ** (2 * k + 1)
    p = 1
    p[1] = dot(lanes[2:4], weights[4:8], dot(lanes[0:2], weights[0:4], 0))
    p[GEN] = 7
    return
";
    let program = compile(&parse(src).expect("parse"));
    let dots = program.prog.iter().filter(|op| matches!(op, Op::Dot { .. })).count();
    assert_eq!(dots, 2, "one DOT instruction a call");
    let y = F192::new(0, 1, 0);
    let sum = (0..8).fold(F192::ZERO, |s, j| s + y * F192::from(g_pow(2 * j)));
    let want = [sum, F192::new(7, 0, 0)];
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &want, &proof).expect("the DOT program verifies");
}

/// `DOT` addresses its lanes in the frame, so a heap run is refused rather than bridged.
#[test]
#[should_panic(expected = "frame cells")]
fn dot_lanes_must_be_frame_cells() {
    let src = "\
def main():
    weights = HeapBuf(8)
    lanes = HeapBuf(4)
    y = dot(lanes[0:2], weights[0:4], 0)
    return
";
    let _ = compile(&parse(src).expect("parse"));
}
