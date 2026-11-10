use lean_compiler::{compile, parse};
use leanvm_core::cpu::{Stats, prove, verify};
use primitives::field::{F64, F192};

const SRC: &str = r#"
DECORATOR
def walk(buf, a, b, c):
    for i in mul_range(1, GEN ** 8):
        s = StackBuf(2)
        s[0] = a
        s[1] = b * i
        buf[i] = s[0] * s[1] + c
        assert s[0] == a
    return

def main():
    public = 1
    x = public[1]
    buf = HeapBuf(8)
    walk(buf, x, x * x, x * GEN)
    return
"#;

/// `@deref_copies` moves a function's copies, its loops' back edges included, from
/// the MUL table to the DEREF table, copy for copy, saving the `SET` of the `1` they
/// multiplied by.
#[test]
fn deref_copies_move_copies_off_the_mul_table() {
    leanvm_core::init_prover();
    let public = [F192::from(F64(0x1234_5678)), F192::ZERO];
    let plain = compile(&parse(&SRC.replace("DECORATOR", "")).unwrap());
    let moved = compile(&parse(&SRC.replace("DECORATOR", "@deref_copies")).unwrap());
    let (a, b) = (plain.execute(public).unwrap(), moved.execute(public).unwrap());
    assert!(b.unconstrained_reads.is_empty());
    let at = |name| Stats::TABLES.iter().position(|t| *t == name).unwrap();
    let (mul, deref, set) = (at("MUL"), at("DEREF"), at("SET"));
    let (ra, rb) = (a.rows(), b.rows());
    // Per iteration: the counter and the four captured values, the next frame's fp
    // and return target, the store of `a` and the assert.
    assert_eq!(ra[mul] - rb[mul], 8 * (5 + 3 + 2));
    assert_eq!(a.cycles - b.cycles, ra[set] - rb[set]);
    assert!(b.mem_used <= a.mem_used);
    assert_eq!(rb[deref] - ra[deref], ra[mul] - rb[mul]);
    let (proof, _) = prove(&moved, public, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&moved, &public, &proof).unwrap();
    let both = SRC.replace("DECORATOR", "@inline\n@deref_copies");
    assert!(parse(&both).unwrap_err().contains("cannot be `@deref_copies`"));
}
