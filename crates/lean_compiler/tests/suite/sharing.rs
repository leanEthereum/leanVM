//! The lowerer shares one cell between identical pure operations (`FnLower::pure`).
//! These programs pin the cases where a "duplicate" is NOT dead, so sharing it
//! would drop a constraint. They were written against a value-numbering pass that
//! ran after lowering, and they outlived it: the hazard belongs to the sharing,
//! not to where it happens.

use lean_compiler::{compile, parse};
use lean_vm::cpu::{prove, verify};
use primitives::field::{F64, F192, g_pow};

/// A returned value that repeats a constant computed earlier in the same
/// function. The return slot lives in the callee frame and is read by the
/// CALLER, so eliminating that write leaves the caller reading an unwritten
/// (prover-chosen) cell: `walk` in the XMSS guest returned a flag exactly this
/// way, and folding it produced a proof whose caller-side assert failed.
#[test]
fn duplicate_constant_in_a_return_slot_survives() {
    let src = "\
def tag(x):
    # `marker` is the same constant the flag below returns, and it is computed
    # first, so the flag's `SET` is a textual duplicate of it.
    marker = 7
    return x * marker, 7

def main():
    v, flag = tag(GEN ** 3)
    p = 1
    p[1] = v
    p[GEN] = flag
    return
";
    let program = compile(&parse(src).expect("parse"));
    let want = [F192::from(g_pow(3)) * F192::from(F64(7)), F192::from(F64(7))];
    let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
    verify(&program, &want, &proof).expect("returned duplicate constant is preserved");
}

/// An argument slot written with a value that already exists in the caller: the
/// callee reads its arguments out of its own frame, so the store must stay.
#[test]
fn duplicate_argument_value_survives() {
    let src = "\
def add_both(a, b):
    return a + b

def main():
    k = GEN ** 5
    # Both arguments are the same expression, and the sum is computed here too,
    # so every operand the call needs has a duplicate in this frame.
    local = k + k
    s = add_both(k, k)
    p = 1
    p[1] = s + local
    return
";
    let program = compile(&parse(src).expect("parse"));
    // (k + k) + (k + k) == 0 in characteristic two.
    let want = [F192::ZERO, F192::ZERO];
    let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
    verify(&program, &want, &proof).expect("duplicated call arguments are preserved");
}

/// A duplicate on one side of a branch must not be shared with the other side's
/// computation: the cache reverts at a join, so each arm recomputes what it
/// needs. Shared, the arm that runs would read a cell only the untaken arm
/// writes, leaving it unwritten and so prover-chosen.
///
/// The condition is FALSE on purpose, so the arm that runs is the SECOND one
/// emitted. Written the other way the taken arm is the one that mints the cell,
/// any sharing can only redirect the untaken arm, and the test cannot fail: it
/// passed with both caches leaking past the join and with the scope revert
/// deleted outright.
#[test]
fn duplicates_are_not_folded_across_a_branch() {
    let src = "\
def main():
    x = GEN ** 3
    r = HeapBuf(2)
    # The same constant in both arms, and the else arm is the one that runs.
    if x == GEN ** 5:
        r[1] = GEN ** 4
    else:
        r[1] = GEN ** 4
    p = 1
    p[1] = r[1]
    p[GEN] = x
    return
";
    let run = |pi: [F192; 2]| -> bool {
        let program = compile(&parse(src).expect("parse"));
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let (proof, _) = prove(&program, pi, lean_vm::pcs::TEST_LOG_INV_RATE);
            verify(&program, &pi, &proof).is_ok()
        }))
        .unwrap_or(false)
    };
    assert!(
        run([F192::from(g_pow(4)), F192::from(g_pow(3))]),
        "the arm that runs keeps its own constant"
    );
    // The wrong value is the half that bites: a cell only the untaken arm writes
    // is the prover's to choose, and the honest claim would verify anyway.
    assert!(
        !run([F192::from(g_pow(7)), F192::from(g_pow(3))]),
        "the stored constant is pinned by the arm that ran"
    );
}

/// The assert idiom is `XOR fp[t] = a ^ b` into the pooled zero cell, whose
/// second write IS the assertion, so that cell must never be shared and the
/// `XOR` must never be skipped in favour of one computed earlier.
///
/// The operands are HEAP READS on purpose. Written `a = GEN ** 9`, both sides
/// fold and `diff = a + b` emits no `XOR` at all, so the duplicate the test
/// names does not exist and the test cannot fail: skipping the assert on a cache
/// hit then passed the whole suite. Read from a `HeapBuf` the two values are
/// runtime cells, `diff` really does emit `XOR fp[t] = a ^ b`, and the assert's
/// own `XOR` has a genuine duplicate to be folded into.
fn duplicated_comparison(second: u32) -> String {
    format!(
        "\
def main():
    hb = HeapBuf(2)
    hb[1] = GEN ** 9
    hb[GEN] = GEN ** {second}
    a = hb[1]
    b = hb[GEN]
    # The same XOR the assert needs, as a live value.
    diff = a + b
    assert a == b
    p = 1
    p[1] = diff
    p[GEN] = a
    return
"
    )
}

#[test]
fn assert_survives_a_duplicated_comparison() {
    let program = compile(&parse(&duplicated_comparison(9)).expect("parse"));
    let want = [F192::ZERO, F192::from(g_pow(9))];
    let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
    verify(&program, &want, &proof).expect("passing assert still verifies");
}

/// The same shape with the assert failing: it must still panic, which is what
/// says the assertion is really there.
#[test]
#[should_panic(expected = "write-once conflict")]
fn failing_assert_still_conflicts() {
    let program = compile(&parse(&duplicated_comparison(10)).expect("parse"));
    let want = [F192::ZERO, F192::from(g_pow(9))];
    let _ = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
}

/// A hint at the end of a runtime branch is attached to a no-op anchor by the
/// lowerer. Even when that anchor repeats an earlier pure instruction, it has to
/// be emitted: moving the hint to the next textual instruction would move it to
/// the join and execute it when the branch is not taken.
#[test]
fn trailing_branch_hint_stays_in_its_branch() {
    let src = "\
def main():
    flag = StackBuf(1)
    hint_witness(flag, \"flag\")
    data = StackBuf(1)
    if flag[0] == 1:
        print(\"anchor\", flag[0])
        hint_witness(data, \"data\")
    p = 1
    p[1] = flag[0]
    p[GEN] = 0
    return
";
    let mut program = compile(&parse(src).expect("parse"));
    program.set_witness("flag", vec![vec![F192::ZERO]]);
    let want = [F192::ZERO, F192::ZERO];
    let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
    verify(&program, &want, &proof).expect("untaken branch must not consume its witness");
}

/// A BLAKE2s chaining value names a CONSECUTIVE PAIR, so neither half may be
/// folded into a canonical elsewhere and the base may not be rewritten: a
/// substitution speaks for one cell, and redirecting the base silently redirects
/// the second word too. `rewrite_reads` used to map `cv` like any single-cell
/// read, so when the first of the two assembling copies duplicated an earlier
/// copy of the same source, the compression absorbed the OTHER pair's second
/// word. Silent, and a soundness break in a transcript.
///
/// The two compressions here differ in nothing but their chaining value, and
/// their two `cv` pairs share a first word, which is what made the first copy a
/// duplicate. If either pair is rewritten or dropped, the digests coincide and
/// the inequality fails at witness generation.
#[test]
fn a_chaining_value_pair_is_neither_rewritten_nor_dropped() {
    let src = "\
def main():
    hb = HeapBuf(4)
    hb[1] = GEN ** 11
    hb[GEN] = GEN ** 22
    hb[GEN ** 2] = GEN ** 33
    hb[GEN ** 3] = GEN ** 44
    x = hb[1]
    y = hb[GEN]
    z = hb[GEN ** 2]
    w = hb[GEN ** 3]
    msg = StackBuf(4)
    msg[0] = y
    msg[1] = y
    msg[2] = y
    msg[3] = y
    t = StackBuf(2)
    t[0] = x
    t[1] = z
    o1 = StackBuf(2)
    blake2s(msg[0:2], msg[2:4], o1, cv=t, counter=64, final=1)
    s = StackBuf(2)
    s[0] = x
    s[1] = w
    o2 = StackBuf(2)
    blake2s(msg[0:2], msg[2:4], o2, cv=s, counter=64, final=1)
    assert o1[0] != o2[0]
    p = 1
    p[1] = x
    p[GEN] = y
    return
";
    let program = compile(&parse(src).expect("parse"));
    let want = [F192::from(g_pow(11)), F192::from(g_pow(22))];
    let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
    verify(&program, &want, &proof).expect("each compression absorbs its own chaining value");
}

#[test]
fn cached_loads_do_not_cross_branches_or_erase_stores() {
    let source = r#"
def main():
    h = HeapBuf(3)
    hint_witness(h[0:3], "values")
    public = 1
    if public[1] == 0:
        a = h[1] + h[GEN]
    else:
        b = h[1] + h[GEN]
    h[GEN ** 2] = h[1]
    assert h[GEN ** 2] == h[1]
    h[1] = public[GEN]
    return
"#;
    let value = F192::new(17, 31, 43);
    let mut program = compile(&parse(source).unwrap());
    program.set_witness("values", vec![vec![value, F192::ONE, value]]);
    for branch in [F192::ZERO, F192::ONE] {
        assert!(program.execute([branch, value]).unconstrained_reads.is_empty());
        assert!(std::panic::catch_unwind(|| program.execute([branch, value + F192::ONE])).is_err());
    }
}

#[test]
fn cached_loads_resolve_deferred_equalities_before_use() {
    lean_vm::init_prover_pool();
    let source = r#"
def fill(h):
    value = hint_witness("value")
    h[1] = value
    return

def main():
    h = HeapBuf(1)
    TOUCH
    FILL
    out = StackBuf(2)
    out[0] = h[1] * h[1]
    out[1] = h[1]
    public = 1
    assert public[1] == out[0]
    assert public[GEN] == out[1]
    return
"#;
    let value = F192::from(F64(7));
    let public = [value * value, value];
    for touch in ["assert log(h) < 1024", "early = StackBuf(1)\n    early[0] = h[1]"] {
        for fill in ["hint_witness(h[0:1], \"value\")", "fill(h)"] {
            let source = source.replace("TOUCH", touch).replace("FILL", fill);
            let mut program = compile(&parse(&source).unwrap());
            program.set_witness("value", vec![vec![value]]);
            assert!(program.execute(public).unconstrained_reads.is_empty());
            let (proof, _) = prove(&program, public, lean_vm::pcs::TEST_LOG_INV_RATE);
            verify(&program, &public, &proof).unwrap();
            assert!(std::panic::catch_unwind(|| program.execute([public[0] + F192::ONE, value])).is_err());
        }
    }
}

#[test]
fn cached_copies_resolve_deferred_stores() {
    lean_vm::init_prover_pool();
    let source = r#"
def square(h):
    return h[GEN] * h[GEN]

def main():
    h = HeapBuf(2)
    early = StackBuf(1)
    other = StackBuf(1)
    early[0] = h[GEN]
    value = hint_witness("value")
    FILL_DEST
    DEST[0] = h[GEN]
    result = square(h)
    public = 1
    assert public[1] == result
    return
"#;
    let value = F192::from(F64(7));
    let public = [value * value, F192::ZERO];
    for (dest, fill) in [
        ("early", "early[0] = value"),
        ("other", "other[0] = value"),
        ("other", "other[0] = h[GEN]\n    h[GEN] = value"),
    ] {
        let source = source.replace("FILL_DEST", fill).replace("DEST", dest);
        let mut program = compile(&parse(&source).unwrap());
        program.set_witness("value", vec![vec![value]]);
        assert!(program.execute(public).unconstrained_reads.is_empty());
        let (proof, _) = prove(&program, public, lean_vm::pcs::TEST_LOG_INV_RATE);
        verify(&program, &public, &proof).unwrap();
    }
}
