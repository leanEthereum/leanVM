use lean_compiler::{compile, compile_without_filler, parse};
use lean_vm::cpu::{prove, verify};
use primitives::field::{F64, F192, g_pow};

#[test]
fn loop_frames_preserve_escaped_cells_and_nested_allocations() {
    lean_vm::init_prover_pool();
    let source = r#"
def make_heap(x):
    h = HeapBuf(2)
    h[1] = x
    h[GEN] = x * x
    return h

def run(stop):
    saved = HeapBuf(GEN ** 12)
    heaps = HeapBuf(GEN ** 12)
    nested = HeapBuf(GEN ** 36)
    sums = HeapBuf(GEN ** 13)
    sums[GEN ** 2] = 0
    for x in mul_range(GEN ** 2, stop):
        pair = [x, x * x]
        saved[x] = addr(pair)
        heaps[x] = make_heap(x)
        for y in mul_range(1, GEN ** 3):
            local = [x, y]
            nested[x ** 3 * y] = addr(local)
        sums[x * GEN] = sums[x] + x
    for x in mul_range(GEN ** 2, stop):
        p = saved[x]
        h = heaps[x]
        assert p[1] == x
        assert p[GEN] == x * x
        assert h[1] == x
        assert h[GEN] == x * x
        for y in mul_range(1, GEN ** 3):
            q = nested[x ** 3 * y]
            assert q[1] == x
            assert q[GEN] == y
    return sums[stop]

def main():
    public = 1
    result = run(public[GEN])
    assert result == public[1]
    return
"#;
    let program = compile(&parse(source).unwrap());
    for end in [2, 3, 9] {
        let sum = (2..end).fold(F64::ZERO, |sum, i| sum + g_pow(i));
        let public = [F192::from(sum), F192::from(g_pow(end))];
        assert!(program.execute(public).unconstrained_reads.is_empty());
        if end == 9 {
            let (proof, _) = prove(&program, public, lean_vm::pcs::TEST_LOG_INV_RATE);
            verify(&program, &public, &proof).unwrap();
        }
    }
}

#[test]
fn early_return_does_not_reserve_the_unused_range() {
    let source = r#"
def main():
    out = HeapBuf(1)
    for x in mul_range(1, GEN ** 4294967296):
        if x == 1:
            out[1] = 7
            return
    public = 1
    assert public[1] == out[1]
    return
"#;
    let program = compile_without_filler(&parse(source).unwrap());
    let execution = program.execute([F192::from(F64(7)), F192::ZERO]);
    assert!(execution.unconstrained_reads.is_empty());
}

#[test]
fn runtime_frame_count_uses_the_distance_from_the_start() {
    let source = r#"
def main():
    public = 1
    out = HeapBuf(2)
    for x in mul_range(GEN ** 65535, public[GEN]):
        if x == GEN ** 65535:
            out[1] = x
        else:
            out[GEN] = x
    assert out[GEN] == public[1]
    return
"#;
    let program = compile_without_filler(&parse(source).unwrap());
    assert!(
        program
            .execute([g_pow(65536).into(), g_pow(65537).into()])
            .unconstrained_reads
            .is_empty()
    );
}

#[test]
fn rebound_counter_keeps_incremental_frames() {
    lean_vm::init_prover_pool();
    let source = r#"
def bump(x):
    if x == 1:
        return GEN ** 5
    if x == GEN ** 6:
        return 1
    return x

def main():
    public = 1
    seen = HeapBuf(7)
    for x in mul_range(1, STOP):
        seen[x] = x
        x = bump(x)
    assert seen[GEN ** 6] == GEN ** 6
    assert seen[GEN] == GEN
    return
"#;
    let public = [F192::ZERO, g_pow(2).into()];
    for bound in ["GEN ** 2", "public[GEN]"] {
        let program = compile(&parse(&source.replace("STOP", bound)).unwrap());
        assert!(program.execute(public).unconstrained_reads.is_empty());
        let (proof, _) = prove(&program, public, lean_vm::pcs::TEST_LOG_INV_RATE);
        verify(&program, &public, &proof).unwrap();
    }
}
