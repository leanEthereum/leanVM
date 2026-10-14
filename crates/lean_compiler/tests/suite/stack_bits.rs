//! Computed-advice bit buffers in the frame: `hint_decompose_bits` into a
//! `StackBuf`, and `addr()` naming the run so it can still be indexed through a
//! pointer (at a runtime index, or from a callee).

use lean_compiler::{compile, parse};
use leanvm_core::cpu::{Stats, prove, verify};
use primitives::field::{F64, F192};

const V: u64 = 0b1011_0110;

fn deref_index() -> usize {
    Stats::TABLES.iter().position(|&t| t == "DEREF").expect("a DEREF table")
}

/// The same eight-bit decomposition, once through a `HeapBuf` and once through a
/// `StackBuf`. Every index is compile-time, so the frame run needs no `DEREF` at
/// all where the heap one needs two per bit (the read and the booleanity pin).
#[test]
fn a_frame_bit_buffer_costs_no_deref() {
    let src = |decl: &str, idx: &str| {
        format!(
            "\
def main():
    bits = {decl}
    hint_decompose_bits(bits, {V}, 8)
    acc = 0
    for i in unroll(0, 8):
        b = bits[{idx}]
        bits[{idx}] = b * b
        acc += b * (2 ** i)
    assert acc == {V}
    p = 1
    p[1] = acc
    p[GEN] = 1
    return
"
        )
    };
    let want = [F192::from(F64(V)), F192::from(F64::ONE)];
    let deref = |s: &str| crate::common::mix(s, want)[deref_index()];
    assert_eq!(
        deref(&src("HeapBuf(GEN ** 8)", "GEN ** i")) - deref(&src("StackBuf(8)", "i")),
        16,
        "a frame bit buffer must drop both DEREFs per bit"
    );
}

/// A stack bit run is addressed by CONTIGUITY, so no cell of one may be given
/// away to a duplicate elsewhere: `hint_log2_ceil` reads `fp+base+k` whatever the
/// lowerer decided, so a dropped store would leave it holding nothing. The
/// duplicate `MUL` here comes FIRST, which is the order that would make the store
/// the one dropped.
#[test]
fn a_stack_bit_run_survives_cell_sharing() {
    let src = "\
def main():
    src = StackBuf(4)
    hint_witness(src, \"bits\")
    bits = StackBuf(4)
    for i in unroll(0, 4):
        dup = src[i] * src[i]
        bits[i] = src[i] * src[i]
        assert dup == bits[i]
    g_mu = hint_log2_ceil(bits, 4, 0)
    p = 1
    p[1] = g_mu
    p[GEN] = 1
    return
";
    // bits 1011 = 11, whose ceil-log is 4. Executing is enough: a folded-away
    // store leaves its cell unwritten, and the advice then computed off the hole
    // collides with the published public input.
    let mut program = compile(&parse(src).expect("parse"));
    let bits: Vec<F192> = [1u64, 1, 0, 1].iter().map(|&b| F192::from(F64(b))).collect();
    program.set_witness("bits", vec![bits]);
    let want = [F192::from(primitives::field::g_pow(4)), F192::from(F64::ONE)];
    let exec = program.execute(want).unwrap();
    assert!(
        exec.unconstrained_reads.is_empty(),
        "every cell of the run must still be written"
    );
}

/// `addr(sb)` in a non-`main` function, where naming `fp` costs the two-`DEREF`
/// bounce: the pointer reads the very cells the direct indices wrote, at a
/// compile-time offset and at a runtime one.
#[test]
fn addr_names_the_frame_run() {
    let src = "\
def main():
    w = StackBuf(1)
    hint_witness(w, \"v\")
    out = probe(w[0])
    p = 1
    p[1] = out
    p[GEN] = 1
    return

def probe(v):
    bits = StackBuf(8)
    hint_decompose_bits(bits, v, 8)
    ptr = addr(bits)
    acc = 0
    for i in unroll(0, 8):
        b = bits[i]
        bits[i] = b * b
        acc += b * (2 ** i)
    assert acc == v
    total = 0
    for i in unroll(0, 8):
        total += ptr[GEN ** i] * (2 ** i)
    assert total == v
    for x in mul_range(1, GEN ** 8):
        chk = ptr[x]
        assert chk * chk == chk
    assert addr(bits) == ptr
    return total
";
    let mut program = compile(&parse(src).expect("parse"));
    program.set_witness("v", vec![vec![F192::from(F64(V))]]);
    let want = [F192::from(F64(V)), F192::from(F64::ONE)];
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &want, &proof).expect("the pointer reads the frame run");
}

/// A frame pointer carries the same compile-time bound a `HeapBuf` pointer gets.
/// `check_heap_bound` keys `heap_sizes` by the pointer's own cell, but every
/// `addr()` in a function shares the `fp` cell as its base, so the run has to
/// come from the address's own provenance instead.
#[test]
#[should_panic(expected = "out of bounds")]
fn addr_pointers_are_bounds_checked() {
    let src = "\
def main():
    b = StackBuf(2)
    p = addr(b)
    p[GEN ** 40] = GEN ** 3
    return
";
    compile(&parse(src).expect("parse"));
}
