//! `lookup(TABLE, x)`: a constant array read at a runtime g-power, from `main` and from a callee.

use crate::common::compile;
use lean_vm_core::cpu::{prove, verify};
use primitives::field::F128;
use zkdsl_compiler::parse;

#[test]
fn lookup_reads_a_constant_array_at_a_runtime_index() {
    let src = "\
TABLE = [5, 7, 11, 13, 17]

def read(x):
    return lookup(TABLE, x) + lookup(TABLE, x, 2)

def main():
    p = 1
    p[1] = read(GEN ** 1)
    p[GEN] = lookup(TABLE, GEN ** 4)
    return
";
    let program = compile(&parse(src).expect("parse"));
    // TABLE[1] + TABLE[3], the sum of two field words, then TABLE[4].
    let want = [F128::new(7 ^ 13, 0), F128::new(17, 0)];
    let (proof, _) = prove(&program, &[], want, lean_vm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &want, &proof).expect("the lookup program verifies");
}
