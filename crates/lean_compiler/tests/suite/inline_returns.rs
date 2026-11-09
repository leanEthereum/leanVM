use lean_compiler::{compile, parse};
use leanvm_core::cpu::{prove, verify};
use primitives::field::{F64, F192};

const STEP: &str = r#"
@inline
def step(cursor, acc):
    x = cursor[GEN ** 0]
    y = acc * x
    return y, x, cursor * GEN

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
    out = HeapBuf(2)
    out[1] = acc
    out[GEN] = x
    return
"#;

/// An inlined call's returned names bind as `let`s would: a returned scalar or
/// shifted pointer aliases what the body computed, so the call takes no more
/// cells or instructions than its body written in place.
#[test]
fn inlined_returns_cost_nothing_over_the_body() {
    leanvm_core::init_prover();
    let call = STEP.replace("BODY", "acc, x, cur = step(cur, acc)");
    let in_place = STEP.replace(
        "BODY",
        "x = cur[GEN ** 0]\n        acc = acc * x\n        cur = cur * GEN",
    );
    let public = [F192::from(F64(0x1234_5678)), F192::ZERO];
    let call = compile(&parse(&call).unwrap());
    let in_place = compile(&parse(&in_place).unwrap());
    let (a, b) = (call.execute(public).unwrap(), in_place.execute(public).unwrap());
    assert!(a.unconstrained_reads.is_empty());
    assert_eq!(a.mem_used, b.mem_used, "cells: inlined call against the body in place");
    assert_eq!(a.rows(), b.rows(), "rows: inlined call against the body in place");
    let (proof, _) = prove(&call, public, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&call, &public, &proof).unwrap();
}
