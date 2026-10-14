//! `assert a != b`: a proof-enforced inequality. It lowers to `XOR x = a + b`,
//! a hinted `inv = x⁻¹`, `MUL p = x·inv` and `SET p = 1`, the write-once
//! conflict on `p` being the assertion. Sound whatever the hint: `x = 0` forces
//! `p = 0`, which cannot then be set to `1`. Three rows and no `JUMP`.

use lean_compiler::{compile, parse};
use leanvm_core::cpu::{Op, prove, verify};
use primitives::field::{F64, F192, g_pow};

/// Honest inequality over runtime values: prove + verify pass.
#[test]
fn assert_ne_end_to_end() {
    let src = "\
def main():
    x = GEN ** 5
    y = GEN ** 7
    z = x * y
    assert z != x
    assert z != y
    p = 1
    p[1] = z
    p[GEN] = x
    return
";
    let program = compile(&parse(src).expect("parse"));
    let want = [F192::from(g_pow(12)), F192::from(g_pow(5))];
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &want, &proof).expect("inequality program verifies");
}

/// `assert a != b` inside a `mul_range` body: the check is emitted once per
/// compiled body and runs on every iteration, each of which differs from the
/// fixed value, so the honest loop verifies.
#[test]
fn assert_ne_in_loop() {
    let src = "\
def main():
    c = GEN ** 9
    for i in mul_range(1, GEN ** 6):
        assert i != c
    p = 1
    p[1] = 5
    p[GEN] = 7
    return
";
    let program = compile(&parse(src).expect("parse"));
    let want = [F192::from(F64(5)), F192::from(F64(7))];
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &want, &proof).expect("loop inequality verifies");
}

/// A compile-time-equal literal pair (e.g. after `Const`-arg substitution) is a
/// hard compile error: the assertion could never hold, so it is caught early.
#[test]
#[should_panic(expected = "compile-time-equal")]
fn assert_ne_compile_time_equal_rejected() {
    let src = "def main():\n    assert 5 != 5\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// Opcode counts of a body with and without one `assert !=`.
fn opcode_delta(with: &str, without: &str) -> (i64, i64, i64) {
    let count = |src: &str| {
        let p = compile(&parse(src).expect("parse"));
        let (mut xor, mut mul, mut jump) = (0i64, 0i64, 0i64);
        for op in &p.prog {
            match op {
                Op::Xor { .. } => xor += 1,
                Op::Mul { .. } => mul += 1,
                Op::Jump { .. } => jump += 1,
                _ => {}
            }
        }
        (xor, mul, jump)
    };
    let (a, b) = (count(with), count(without));
    (a.0 - b.0, a.1 - b.1, a.2 - b.2)
}

/// The check costs one `XOR`, one `MUL` and, above all, no `JUMP`: a
/// branch-based lowering would put an `E`-valued condition back on the one table
/// that carries constraints. The `SET` that closes the check is not counted,
/// constant materialisation elsewhere moving with the frame layout.
#[test]
fn assert_ne_emits_no_jump() {
    let body = |extra: &str| {
        format!(
            "\
def main():
    x = GEN ** 5
    y = GEN ** 7
{extra}    p = 1
    p[1] = x
    p[GEN] = y
    return
"
        )
    };
    let delta = opcode_delta(&body("    assert x != y\n"), &body(""));
    assert_eq!(delta, (1, 1, 0), "one XOR, one MUL, no JUMP");
}
