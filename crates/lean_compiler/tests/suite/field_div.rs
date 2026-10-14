//! Field division `a / b` (single slash): a runtime `a · b⁻¹`, distinct from
//! the compile-time floor-division `//`. It lowers to a single `MUL` whose
//! quotient operand is left unset: the write-once back-solve fills it with
//! `a · b⁻¹` and the `MUL` constraint `quotient · b == a` binds it, with no
//! prover hint (the same back-solve the range-check gadget already uses). A
//! zero divisor is rejected (the back-solve cannot invert 0).

use lean_compiler::{compile, parse};
use leanvm_core::cpu::{prove, verify};
use primitives::field::{F64, F192, g_pow};

/// `a / b` and `1 / b` over runtime values: the quotient satisfies `q·b == a`,
/// checked by publishing it and reproducing the dividend.
#[test]
fn field_div_end_to_end() {
    let src = "\
def main():
    a = GEN ** 20
    b = GEN ** 7
    q = a / b
    r = 1 / b
    p = 1
    p[1] = q * b
    p[GEN] = r * b
    return
";
    let program = compile(&parse(src).expect("parse"));
    // q·b must reproduce a = g^20; r·b must be 1.
    let want = [F192::from(g_pow(20)), F192::from(F64::ONE)];
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &want, &proof).expect("division program verifies");
}

/// `//` stays compile-time floor division (an index), `/` is the runtime field
/// op: the two must not collide. Here `8 // 2 == 4` picks a stack slot while
/// `x / y` is a field quotient.
#[test]
fn field_div_vs_floordiv() {
    let src = "\
def main():
    x = GEN ** 6
    q = x / (GEN ** 2)
    z = GEN ** (6 // 2)
    p = 1
    p[1] = q
    p[GEN] = z
    return
";
    let program = compile(&parse(src).expect("parse"));
    // q = g^6 / g^2 = g^4 (runtime `/`); z = g^(6//2) = g^3 (compile-time `//`).
    let want = [F192::from(g_pow(4)), F192::from(g_pow(3))];
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &want, &proof).expect("mixed //-and-/ program verifies");
}
