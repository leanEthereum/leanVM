//! `print(...)`: a prover-side debug print: must compile, execute during
//! witness generation, and leave proving/verification untouched.

use lean_compiler::{compile, parse};
use lean_vm::cpu::{prove, verify};
use primitives::field::{F64, F192};

#[test]
fn print_is_constraint_free() {
    let src = "\
def main():
    x = 5
    y = x * GEN
    print(y)
    print(\"the product\", y * y)
    b = HeapBuf(2)
    b[1] = 3
    print(b[1])
    p = 1
    p[1] = y
    p[GEN] = b[1]
    return
";
    let program = compile(&parse(src).expect("parse"));
    let want = [F192::from(F64(5) * primitives::field::g_pow(1)), F192::from(F64(3))];
    let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
    verify(&program, &want, &proof).expect("prints must not disturb proving");
}
