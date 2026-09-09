//! `@inline` calls in EXPRESSION position: embedded in arithmetic, as a heap
//! store's RHS, or under further ops: must produce the same values as the
//! statement-position form. Regression test for the dropped-RetBind bug: an
//! inlined tail return of a plain var records a g-address alias, which only
//! `let`/tuple bindings used to consume; expression positions read the
//! never-written dst cell (zeros) and left the stale bind to corrupt the next
//! `let`.

use lean_compiler::{compile, parse};
use lean_vm::cpu::{prove, verify};
use primitives::field::{F64, F192};

#[test]
fn inline_call_in_expression_positions() {
    let src = "\
@inline
def wprod(ch, n: Const, idx: Const):
    # eq-tensor weight of compile-time idx over ch[0..n)
    w = GEN ** 0
    for c in unroll(0, n):
        cv = ch[GEN ** c]
        if (idx // (2 ** c)) % 2 == 1:
            w *= cv
        else:
            w *= (1 + cv)
    return w

def main():
    b = HeapBuf(4)
    b[1] = 3
    b[GEN] = 5
    x = wprod(b, 2, 2)
    y = 7 * wprod(b, 2, 1)
    out = HeapBuf(2)
    out[1] = wprod(b, 2, 3)
    p = 1
    p[1] = x
    p[GEN] = y + out[1]
    return
";
    let program = compile(&parse(src).expect("parse"));

    let (f3, f5, f7) = (F64(3), F64(5), F64(7));
    let one = F64::ONE;
    // statement position: idx 2 -> (1+3)·5
    let x = (one + f3) * f5;
    // embedded in a product: idx 1 -> 7·(3·(1+5))
    let y = f7 * (f3 * (one + f5));
    // heap-store RHS: idx 3 -> 3·5
    let o = f3 * f5;
    let want = [F192::from(x), F192::from(y + o)];

    let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
    verify(&program, &want, &proof).expect("expression-position inline calls compute correctly");

    let mut bad = want;
    bad[0] += F192::ONE;
    assert!(
        verify(&program, &bad, &proof).is_err(),
        "wrong published value must be rejected"
    );
}
