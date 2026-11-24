//! The jump-table slots that only code behind one of `main`'s runtime-bounded loops reads are
//! written on the loop's entry test, not at pc 0, so a run that skips the loop skips them.

use lean_vm_core::cpu::{execute, prove, verify};
use primitives::field::{F64, F128, g_pow};
use zkdsl_compiler::{compile, parse};

const SOURCE: &str = "\
SMALL = [3, 5, 7, 11]
PAIR = [13, 17]

def pick(k):
    v = match(log(k), range(0, 4), lambda j: SMALL[j])
    return v

def shared(k):
    v = match(log(k), range(0, 2), lambda j: PAIR[j])
    return v

def main():
    public = 1
    n = public[GEN]
    assert log(n) < 5
    acc = HeapBuf(5)
    acc[1] = shared(1)
    for i in mul_range(1, n):
        acc[i * GEN] = acc[i] + pick(i) * shared(GEN)
    assert public[1] == acc[n]
    return
";

/// The `SET`s at pc 0, before `main`.
fn start_writes(src: &str) -> u32 {
    let compiled = compile(&parse(src).expect("parse"));
    (compiled.fn_ranges.iter())
        .find(|(name, ..)| name == "__jump_tables")
        .map_or(0, |&(_, _, len)| len)
}

#[test]
fn a_loop_only_table_is_written_on_the_loop_entry() {
    parallel::init();
    // `pick`'s four slots move behind the loop; `shared`, which `main` calls too, keeps its two at pc 0.
    assert_eq!(start_writes(SOURCE), 2);
    let program: isa::Program = compile(&parse(SOURCE).expect("parse")).into();
    for runs in [0, 1, 4] {
        let mut acc = F64(13);
        for k in 0..runs {
            acc += F64([3, 5, 7, 11][k]) * F64(17);
        }
        let public = [F128::from(acc), F128::from(g_pow(runs))];
        assert!(execute(&program, &[], public).unwrap().unconstrained_reads.is_empty());
        if runs != 1 {
            let (proof, _) = prove(&program, &[], public, lean_vm_core::pcs::TEST_LOG_INV_RATE).unwrap();
            verify(&program, &public, &proof).unwrap();
        }
    }
    // A wrong result still fails when the loop is skipped.
    let wrong = [F128::from(F64(13) + F64(3) * F64(17)), F128::from(g_pow(0))];
    assert!(execute(&program, &[], wrong).is_err());
}

#[test]
fn a_table_main_reads_outside_the_loop_stays_at_the_start() {
    let src = SOURCE.replace("acc[1] = shared(1)", "acc[1] = shared(1) + pick(GEN ** 3) + 11");
    assert_eq!(start_writes(&src), 6);
}
