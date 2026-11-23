use crate::common::compile;
use lean_vm_core::cpu::{execute, prove, verify};
use primitives::field::{F64, F128};
use zkdsl_compiler::parse;

#[test]
fn pack64x2_proves_and_verifies() {
    let src = "\
@inline
def pack64x2(a, b):
    assert_in_k(a, b)
    return a + 18446744073709551616 * b

def main():
    ab = StackBuf(2)
    hint_witness(ab, \"ab\")
    packed = pack64x2(ab[0], ab[1])
    p = 1
    p[1] = packed
    p[GEN] = packed
    return
";
    let program = compile(&parse(src).expect("parse"));
    let witness = [("ab".to_string(), vec![vec![F128::from(F64(5)), F128::from(F64(7))]])];
    let want = [F128::new(5, 7), F128::new(5, 7)];
    let (proof, _) = prove(&program, &witness, want, lean_vm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    let counts = execute(&program, &witness, want).unwrap().rows();
    assert_eq!(
        (counts[0], counts[1], counts[4]),
        (1, 1, 2),
        "XOR, MUL and JUMP lowering"
    );
    verify(&program, &want, &proof).expect("pack64x2 program verifies");
}
