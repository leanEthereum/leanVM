use lean_compiler::{compile, parse};
use leanvm_core::cpu::{prove, verify};
use primitives::field::{F64, F192, g_pow};

/// A fused `match` builds one frame for whichever arm runs, sized to that arm: a run
/// that only ever takes the small arm never reserves the large arm's frame.
#[test]
fn a_fused_dispatch_frame_is_sized_to_the_arm_taken() {
    leanvm_core::init_prover();
    let source = r#"
def arm(x, k: Const):
    if const(k == 0):
        y = x * x
    else:
        big = StackBuf(4096)
        big[0] = x
        big[4095] = x * GEN
        y = big[0] * big[4095]
    return y

def main():
    public = 1
    x = public[1]
    sel = public[GEN]
    assert log(sel) < 2
    want = x * x * sel
    for i in mul_range(1, GEN ** 8):
        y = match(log(sel), range(0, 2), lambda k: arm(x, k))
        assert y == want
    return
"#;
    let program = compile(&parse(source).unwrap());
    let x = F192::from(F64(0x1234_5678));
    let small = [x, g_pow(0).into()];
    let large = [x, g_pow(1).into()];
    let run_small = program.execute(small).unwrap();
    let run_large = program.execute(large).unwrap();
    assert!(run_small.unconstrained_reads.is_empty());
    assert!(run_large.unconstrained_reads.is_empty());
    assert!(
        run_small.mem_used < 4096,
        "the small arm reserved {} cells",
        run_small.mem_used
    );
    assert!(
        run_large.mem_used >= 8 * 4096,
        "the large arm reserved {} cells",
        run_large.mem_used
    );
    for public in [small, large] {
        let (proof, _) = prove(&program, public, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
        verify(&program, &public, &proof).unwrap();
    }
}
