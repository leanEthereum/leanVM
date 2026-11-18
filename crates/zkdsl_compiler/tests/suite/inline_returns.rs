use crate::common::compile;
use lean_vm_core::cpu::{execute, prove, verify};
use primitives::field::{F64, F128};
use zkdsl_compiler::parse;

const STEP: &str = r#"
@inline
def step(cursor, acc):
    x = cursor[GEN ** 0]
    y = acc * x
    return y, x, cursor * GEN

@inline
def word(a, b, j: Const):
    w = a
    if const(j == 1):
        w = b
    return w

def main():
    public = 1
    seed = public[1]
    b = HeapBuf(8)
    for i in unroll(0, 8):
        b[GEN ** i] = seed * GEN ** i
    cur = b
    acc = seed
    for i in unroll(0, 8):
        BODY
    out = HeapBuf(3)
    out[1] = acc
    out[GEN] = x
    out[GEN ** 2] = WORD
    return
"#;

/// An inlined call's returned names bind as `let`s would: a returned scalar or
/// shifted pointer aliases what the body computed, so the call takes no more
/// cells or instructions than its body written in place.
#[test]
fn inlined_returns_cost_nothing_over_the_body() {
    let call = STEP
        .replace("BODY", "acc, x, cur = step(cur, acc)")
        .replace("WORD", "word(acc, x, 1)");
    let in_place = STEP
        .replace(
            "BODY",
            "x = cur[GEN ** 0]\n        acc = acc * x\n        cur = cur * GEN",
        )
        .replace("WORD", "x");
    let public = [F128::from(F64(0x1234_5678)), F128::ZERO];
    let call = compile(&parse(&call).unwrap());
    let in_place = compile(&parse(&in_place).unwrap());
    let (a, b) = (
        execute(&call, &[], public).unwrap(),
        execute(&in_place, &[], public).unwrap(),
    );
    assert!(a.unconstrained_reads.is_empty());
    assert_eq!(a.mem_used, b.mem_used, "cells: inlined call against the body in place");
    assert_eq!(a.rows(), b.rows(), "rows: inlined call against the body in place");
    let (proof, _) = prove(&call, &[], public, lean_vm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&call, &public, &proof).unwrap();
}
