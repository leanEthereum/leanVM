//! Statement forms that used to be accepted and mean something else. Each of
//! these compiled clean before, so the pin is that they are now REJECTED: a
//! diagnostic is the whole fix.

use lean_compiler::{compile, parse};
use leanvm_core::cpu::{prove, verify};
use primitives::field::{F192, g_pow};

/// A name is a plain identifier. Two different mistakes arrive here, and both
/// used to compile: a mis-split statement (`x /= 2` became a binding named
/// `x /`) and a top-level constant reused as a parameter or local. Constants
/// are substituted textually before parsing, so `V = 8` followed by
/// `def scale(V)` gave a parameter literally named `8` and a body reading the
/// constant: `scale(3)` returned 16.
#[test]
fn a_constant_may_not_be_reused_as_a_parameter() {
    let src = "\
V = 8

def scale(V):
    return V * 2

def main():
    p = GEN ** 0
    p[1] = scale(3)
    p[GEN] = scale(3)
    return
";
    let err = parse(src).expect_err("a parameter may not reuse a constant's name");
    assert!(err.contains("not a valid parameter name"), "{err}");
}

/// `/=` and `**=` are not compound assignments here. `split_aug` declined them
/// and `split_assign` then split the bare `=`, leaving a dead binding and the
/// old value in place. `/` being a real runtime field operation is what made
/// `x /= y` look legal.
#[test]
fn an_unsupported_compound_assignment_is_rejected() {
    let body = |stmt: &str| {
        format!(
            "\
def main():
    x = 4
    {stmt}
    p = GEN ** 0
    p[1] = x
    p[GEN] = x
    return
"
        )
    };
    for (stmt, want) in [
        ("x /= 2", "`/=` is not supported"),
        ("x **= 2", "`**=` is not supported"),
    ] {
        let err = parse(&body(stmt)).expect_err(stmt);
        assert!(err.contains(want), "{stmt}: {err}");
    }
    // The five that ARE supported still desugar.
    let ok = body("x += 1\n    x *= 2\n    x //= 2\n    x %= 3\n    x -= 1");
    compile(&parse(&ok).expect("the supported compound assignments parse"));
}

/// A bare comparison is not a statement. `split_assign` used to split `x != y`
/// on its `=` into a binding named `x !`, so an `assert` that lost its keyword
/// to an edit compiled to nothing at all: in a verifier, a deleted check with
/// no diagnostic and no cycle to notice.
#[test]
fn a_bare_comparison_is_rejected() {
    let body = |stmt: &str| {
        format!(
            "\
def main():
    x = 4
    y = 5
    {stmt}
    p = GEN ** 0
    p[1] = x
    p[GEN] = x
    return
"
        )
    };
    for stmt in ["x != y", "x == y", "x <= y", "x >= y", "x < y", "x > y"] {
        let err = parse(&body(stmt)).expect_err(stmt);
        assert!(err.contains("is a comparison, not a statement"), "{stmt}: {err}");
    }
    // The equality forms name the fix; the order forms say they are not predicates.
    assert!(parse(&body("x != y")).unwrap_err().contains("write `assert x != y`"));
    assert!(parse(&body("x < y")).unwrap_err().contains("order facts come from"));
}

/// A stack store whose value IS its own destination recorded `alias[dst] = dst`,
/// and `word_src` chased that forever: a compiler that never returns, with no
/// output at all. Two stores could close the same loop in two steps. Both are
/// now no-ops (write-once makes a second write of the same value one), and the
/// documented swap must keep working.
#[test]
fn a_self_referential_stack_store_terminates() {
    let cases = [
        // one statement
        "    s[0] = s[0]\n",
        // two, closing the cycle
        "    s[0] = s[1]\n    s[1] = s[0]\n",
    ];
    for tail in cases {
        let src = format!(
            "\
def main():
    s = StackBuf(2)
{tail}    p = 1
    p[1] = s[0]
    p[GEN] = s[0]
    return
"
        );
        compile(&parse(&src).expect("parse")).execute([F192::ZERO; 2]).unwrap();
    }
    // `s = [s[1], s[0]]` rebinds to a fresh run and must still swap.
    let swap = "\
def main():
    s = StackBuf(2)
    s[0] = 5
    s[1] = 7
    s = [s[1], s[0]]
    p = 1
    p[1] = s[0]
    p[GEN] = s[1]
    return
";
    let want = [
        F192::from(primitives::field::F64(7)),
        F192::from(primitives::field::F64(5)),
    ];
    compile(&parse(swap).expect("parse")).execute(want).unwrap();
}

/// A `mul_range` stop bound that is a compile-time value but not a power of GEN
/// can never be REACHED: the counter walks by multiplication and exits on
/// equality, so the loop ran forever at witness generation with no diagnostic.
/// The `lo` side was always checked, which made `mul_range(0, GEN ** 3)` a clean
/// parse error while `mul_range(1, 10)` was a hang.
#[test]
fn a_loop_bound_must_be_reachable() {
    let src = "\
def main():
    hb = HeapBuf(8)
    hb[1] = 1
    for i in mul_range(1, 10):
        hb[i * GEN] = hb[i]
    return
";
    let err = parse(src).expect_err("an unreachable stop bound must be rejected");
    assert!(err.contains("is not a power of GEN"), "{err}");

    // A power-of-two literal IS a power of GEN and the walk does reach it, so it
    // must be accepted, and as a compile-time bound rather than a runtime one.
    let ok = src.replace("mul_range(1, 10)", "mul_range(1, 16)");
    compile(&parse(&ok).expect("`16` is `g^4`"));
}

/// A binding made inside one arm of an `if` is local to that arm, so the other
/// arm reads the OUTER binding and the loop must capture it. `free_vars_stmt`
/// threaded one flat set through both arms, so a name rebound anywhere in the
/// body counted as loop-local everywhere and the outer binding was never
/// captured: this legal program failed with `unbound variable`.
#[test]
fn a_branch_local_rebinding_does_not_hide_the_outer_binding() {
    let src = "\
def main():
    hb = HeapBuf(8)
    w = GEN ** 3
    for i in mul_range(1, GEN ** 4):
        if i == GEN:
            w = GEN
            hb[i * GEN] = w
        else:
            hb[i * GEN] = w
    p = GEN ** 0
    p[1] = hb[GEN ** 2]
    p[GEN] = hb[GEN ** 3]
    return
";
    // Cell 2 is written on the taken arm (the branch-local `w = GEN`); cell 3 on
    // the other, from the outer `w`.
    let program = compile(&parse(src).expect("parse"));
    let want = [F192::from(g_pow(1)), F192::from(g_pow(3))];
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &want, &proof).expect("the else arm reads the outer binding");
}

/// `g` is `x`, so a literal `2^k` is `g^k` ONLY while `k < 64`: at and above
/// that the modulus folds the monomial back into the low limb while the
/// literal's bit `k` lands in the next one, the tower coefficient of `y`. The
/// guest's own `Y_TOWER` is exactly `2^64`, machine-generated by `dsl_u128`, so
/// a g-power recognizer without that guard gives one literal two values
/// depending on whether it went through a binding.
#[test]
fn a_power_of_two_literal_is_a_g_power_only_below_two_to_the_64() {
    let src = "\
Y_TOWER = 18446744073709551616

def main():
    yt = Y_TOWER
    a = yt * GEN
    b = Y_TOWER * GEN
    assert a == b
    p = GEN ** 0
    p[1] = a
    p[GEN] = b
    return
";
    let program = compile(&parse(src).expect("parse"));
    // y·x, i.e. the tower coefficient shifted, NOT g^65.
    let want = [F192::new(0, 2, 0); 2];
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &want, &proof).expect("2^64 is the tower element y, not g^64");
}

/// An operator missing a side says which operator and which side.
///
/// Every one of these used to report `cannot parse expression \`\``: the empty
/// operand was handed to the expression parser, which had nothing to name. A
/// leading `-` is the common one, since the language has no unary minus.
#[test]
fn an_operator_missing_an_operand_says_so() {
    for (src, want) in [
        ("-3 + 5", "`-` has no left operand"),
        ("1 +", "`+` has no right operand"),
        ("* 2", "`*` has no left operand"),
        ("4 // ", "`//` has no right operand"),
    ] {
        let err = lean_compiler::parse_const(src).expect_err(src);
        assert!(err.contains(want), "{src}: got `{err}`, wanted `{want}`");
    }
}

/// One hinted value needs no buffer, and costs exactly what the buffer did.
///
/// `hint_witness` fills a destination that already exists, so a single hinted
/// scalar cost a one-cell `StackBuf`, a slice of it, and a read back out. The
/// guest declared thirty such buffers, twenty-eight of them for nothing else.
#[test]
fn one_hinted_value_needs_no_buffer() {
    let body = |bind: &str| {
        format!(
            "def main():
{bind}    assert log m < 8
    p = GEN ** 0
    p[1] = m
    p[GEN] = GEN ** 0
    return
"
        )
    };
    let old = body("    mb = StackBuf(1)\n    hint_witness(mb[0:1], \"m\")\n    m = mb[0]\n");
    let new = body("    m = hint_witness(\"m\")\n");
    let run = |src: &str| {
        let mut program = compile(&parse(src).expect("parse"));
        program.set_witness("m", vec![vec![g_pow(5).into()]]);
        let want = [g_pow(5).into(), g_pow(0).into()];
        let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
        verify(&program, &want, &proof).expect("verifies");
        program.execute(want).unwrap().base_counts.iter().sum::<usize>()
    };
    assert_eq!(run(&old), run(&new), "the sugar must cost what it replaces");

    // It binds inside a loop body too, where substitution walks the statement.
    let looped = "\
def main():
    hb = HeapBuf(4)
    for i in mul_range(1, 8):
        w = hint_witness(\"w\")
        hb[i] = w
    p = GEN ** 0
    p[1] = hb[GEN]
    p[GEN] = GEN ** 0
    return
";
    let mut program = compile(&parse(looped).expect("parse"));
    program.set_witness(
        "w",
        vec![vec![g_pow(1).into()], vec![g_pow(2).into()], vec![g_pow(3).into()]],
    );
    let want = [g_pow(2).into(), g_pow(0).into()];
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    // `mul_range(1, 8)` is g^0..g^3, so THREE iterations and all three entries
    // are popped. With `mul_range(1, 4)` the third would sit unread and mask an
    // off-by-one in that direction.
    verify(&program, &want, &proof).expect("one hint per iteration");
}

/// A trailing factor after a `hint_witness` call may not vanish into the
/// stream name. `call_args` strips the line's LAST `)`, and the string
/// argument then absorbs anything between the call's own `)` and there:
/// `hint_witness(rb[0:1], "a") * f("b")` parsed as a hint for the stream
/// `a") * f("b`, and the rest of the line was gone. Both forms are guarded
/// by `whole_call`; the line then falls through to `parse_expr`, which
/// refuses the string literal, with the line.
#[test]
fn a_hint_call_spans_its_whole_line() {
    let stmt = "\
def main():
    rb = StackBuf(1)
    hint_witness(rb[0:1], \"a\") * f(\"b\")
    return
";
    let expr = "\
def main():
    m = hint_witness(\"a\") * f(\"b\")
    return
";
    for src in [stmt, expr] {
        let err = parse(src).expect_err("a trailing factor must not parse");
        assert!(err.contains("cannot parse expression"), "{err}");
    }
}

/// The scalar hint binds like any other statement that binds.
///
/// Three `StmtKind` walkers have a catch-all arm, and each silently swallowed
/// the new variant: `@inline` rejected a body that is a single tail return,
/// the `for` capture check raised a `StackBuf` false positive, and return-shape
/// inference lost the binding. All three fail closed, so the cost was a
/// diagnostic naming the wrong cause rather than a miscompile, and all three
/// made the sugar not a drop-in for the idiom it replaces.
#[test]
fn the_scalar_hint_binds_like_any_other_binder() {
    let tail = "    p = GEN ** 0\n    p[1] = r\n    p[GEN] = GEN ** 0\n    return\n";
    // `@inline` accepts it: the body IS a single tail return.
    let inlined = format!(
        "@inline\ndef pick():\n    m = hint_witness(\"m\")\n    return m\n\ndef main():\n    r = pick()\n{tail}"
    );
    let mut program = compile(&parse(&inlined).expect("an @inline body may bind a hint"));
    program.set_witness("m", vec![vec![g_pow(5).into()]]);
    let want = [g_pow(5).into(), g_pow(0).into()];
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &want, &proof).expect("the inlined binding fires");

    // A `for` body that shadows an enclosing StackBuf's name from inside an arm
    // is not capturing it, which is what `binds_anywhere` exists to notice.
    let shadowed = "\
def main():
    sb = StackBuf(2)
    sb[0] = GEN ** 1
    sb[1] = GEN ** 2
    hb = HeapBuf(4)
    for i in mul_range(1, 4):
        if i == i:
            sb = hint_witness(\"w\")
            hb[i] = sb
    p = GEN ** 0
    p[1] = sb[0]
    p[GEN] = GEN ** 0
    return
";
    let mut program = compile(&parse(shadowed).expect("shadowing is not capturing"));
    program.set_witness("w", vec![vec![g_pow(7).into()], vec![g_pow(8).into()]]);
    let want = [g_pow(1).into(), g_pow(0).into()];
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &want, &proof).expect("the outer StackBuf is untouched");

    // Return-shape inference, the third walker: rebinding a `StackBuf` name to a
    // scalar hint has to REPLACE the shape, or the callee is inferred to return a
    // run of cells and the caller dies on "StackBuf used as a scalar". Only a
    // rebinding reaches it, which is why the other two cases above do not.
    let rebound = format!(
        "def pick():\n    s = StackBuf(2)\n    s[0] = GEN ** 1\n    s[1] = GEN ** 2\n    s = hint_witness(\"m\")\n    return s\n\ndef main():\n    r = pick()\n{tail}"
    );
    let mut program = compile(&parse(&rebound).expect("a hint may rebind a StackBuf name"));
    program.set_witness("m", vec![vec![g_pow(6).into()]]);
    let want = [g_pow(6).into(), g_pow(0).into()];
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &want, &proof).expect("the rebound name returns as a scalar");
}

/// A bit-decomposition hint checks its heap destination, like its stack one.
///
/// `bits_dest`'s `StackBuf` arm rejected a destination too small for `nbits`;
/// its `HeapBuf` arm checked nothing, so the bits ran on into the next buffer.
/// The same shape as three earlier bugs: one omission beside a checked
/// counterpart. The guest uses the shifted-alias form, so that is checked here
/// too.
#[test]
fn a_bit_decomposition_cannot_overrun_its_heap_destination() {
    let prog = |decl: &str, dest: &str| {
        format!(
            "def main():
    hb = HeapBuf({decl})
    v = GEN ** 5
    hint_decompose_bits_exponent({dest}, v, 8)
    p = GEN ** 0
    p[1] = hb[1]
    p[GEN] = GEN ** 0
    return
"
        )
    };
    for (decl, dest, want) in [("2", "hb", "0:8"), ("8", "hb * GEN ** 4", "4:12")] {
        let ast = parse(&prog(decl, dest)).expect("parses");
        let Err(err) = std::panic::catch_unwind(|| compile(&ast)) else {
            panic!("HeapBuf({decl}) accepted 8 bits at `{dest}`");
        };
        let msg = err.downcast_ref::<String>().map(String::as_str).unwrap_or("");
        assert!(msg.contains(want) && msg.contains("out of bounds"), "got `{msg}`");
    }
    // Both forms still compile where the buffer really does hold the bits.
    compile(&parse(&prog("8", "hb")).expect("parses"));
    compile(&parse(&prog("16", "hb * GEN ** 4")).expect("parses"));
}

/// Four names and calls that used to pick a winner or die without a line.
#[test]
fn a_program_names_what_it_means() {
    let tail = "    p = GEN ** 0\n    p[1] = GEN ** 0\n    p[GEN] = GEN ** 0\n    return\n";
    // Both bodies used to be lowered, and the last definition won.
    let dup = format!("def f(a):\n    return a\n\ndef f(a):\n    return a\n\ndef main():\n{tail}");
    assert!(parse(&dup).expect_err("duplicate def").contains("defined twice"));
    // `f__L1` is what a `Const` specialization of `f` is called, and `__loopN`
    // what a loop helper is called, so a user function of that name took its
    // place and the call ran the wrong body.
    let reserved = format!("def f__L1(a):\n    return a\n\ndef main():\n{tail}");
    assert!(parse(&reserved).expect_err("reserved name").contains("reserved"));

    // A call to something that will never be lowered died in the assembler as a
    // bare `no entry found for key`, with no line.
    for callee in ["nosuchfn(1)", "assert_in_k(GEN ** 1, GEN ** 1)"] {
        let src = format!("def main():\n    x = {callee}\n{tail}");
        let ast = parse(&src).expect("parses");
        let Err(err) = std::panic::catch_unwind(|| compile(&ast)) else {
            panic!("`{callee}` was accepted");
        };
        let msg = err.downcast_ref::<String>().map(String::as_str).unwrap_or("");
        assert!(msg.contains("no function named"), "{callee}: got `{msg}`");
    }

    // A compile-time constant is capturable into a `for` body: the body becomes
    // its own function, so the constant is not in scope there. Dropping it made
    // this "unbound variable", which named neither the cause nor a fix.
    let captured = "\
def main():
    c = 5
    hb = HeapBuf(4)
    for i in mul_range(1, 4):
        hb[i] = c
    p = GEN ** 0
    p[1] = hb[GEN]
    p[GEN] = GEN ** 0
    return
";
    let program = compile(&parse(captured).expect("a constant may be captured"));
    let want = [F192::new(5, 0, 0), g_pow(0).into()];
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &want, &proof).expect("the captured constant reaches the body");
}

/// Three ways a program could read a frame or heap cell it does not own.
///
/// Each compiled clean and left a cell that nothing writes, which the prover
/// then chooses, so an `assert` reading it proved nothing. The first also read
/// the NEXT buffer and its assert passed.
///
/// They are one omission each, in three places that each had a checked
/// counterpart: the store path's `copy_alias` did not bounds-check its stack
/// index although the identical read in expression position did; `lower_call`
/// did not compare a call's argument count against the callee's parameters
/// although `try_inline` did; and a runtime-start heap slice bounds-checked one
/// cell rather than its length although the compile-time-bounds arm beside it
/// checked the whole span.
#[test]
fn a_program_cannot_reach_a_cell_it_does_not_own() {
    let rejected = |src: &str, want: &str| {
        let ast = parse(src).unwrap_or_else(|e| panic!("should parse: {e}"));
        let Err(err) = std::panic::catch_unwind(|| compile(&ast)) else {
            panic!("accepted:\n{src}");
        };
        let msg = err.downcast_ref::<String>().map(String::as_str).unwrap_or("");
        assert!(msg.contains(want), "got `{msg}`, wanted `{want}`");
    };
    let tail = "    p = GEN ** 0\n    p[1] = GEN ** 0\n    p[GEN] = GEN ** 0\n    return\n";

    // A store's RHS, and a list literal element, each index one past the end.
    rejected(
        &format!("def main():\n    a = StackBuf(2)\n    b = StackBuf(2)\n    c = StackBuf(2)\n    c[0] = a[2]\n{tail}"),
        "index 2 out of bounds (StackBuf size 2)",
    );
    rejected(
        &format!("def main():\n    a = StackBuf(2)\n    b = StackBuf(2)\n    lst = [a[2], a[3]]\n{tail}"),
        "index 2 out of bounds (StackBuf size 2)",
    );
    // A call supplying too few arguments, and too many.
    rejected(
        &format!("def check(a, b):\n    assert a == b\n    return\n\ndef main():\n    check(0)\n{tail}"),
        "`check` takes 2 arguments, got 1",
    );
    rejected(
        &format!("def one(a):\n    return a\n\ndef main():\n    r = one(GEN ** 1, GEN ** 2)\n{tail}"),
        "`one` takes 1 argument, got 2",
    );
    // A runtime-start slice whose start folds: the SPAN leaves the buffer.
    rejected(
        &format!(
            "def main():\n    hb = HeapBuf(2)\n    nxt = HeapBuf(2)\n    hint_witness(hb[GEN ** 1:GEN ** 1 + 2], \"w\")\n{tail}"
        ),
        "heap slice 1:3 out of bounds",
    );

    // The in-bounds run of the same shape still compiles and proves.
    let ok = "\
def main():
    hb = HeapBuf(4)
    hint_witness(hb[GEN ** 1:GEN ** 1 + 2], \"w\")
    p = GEN ** 0
    p[1] = hb[GEN]
    p[GEN] = GEN ** 0
    return
";
    let mut program = compile(&parse(ok).expect("parse"));
    program.set_witness("w", vec![vec![F192::new(1234, 0, 0), F192::new(5678, 0, 0)]]);
    let want = [F192::new(1234, 0, 0), g_pow(0).into()];
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &want, &proof).expect("an in-bounds runtime-start slice still works");
}

/// A `for` body that assigns to an enclosing name says why that cannot work.
///
/// The capture set drops every name the body binds, so a body that ASSIGNS to
/// an enclosing name also loses the read that precedes the assignment, and the
/// read arrived at lowering as a bare "unbound variable". That is the loop-carry
/// limitation, not a typo: the tail-recursive helper threads its captures in and
/// never out, so an accumulator cannot come back. The `StackBuf` form of the
/// same limitation already said so; the scalar form did not.
#[test]
fn a_loop_that_cannot_carry_a_value_says_so() {
    let accumulator = "\
def main():
    s = GEN ** 0
    for i in mul_range(1, 8):
        s = s * GEN
    p = GEN ** 0
    p[1] = s
    p[GEN] = GEN ** 0
    return
";
    let ast = parse(accumulator).expect("parses");
    let Err(err) = std::panic::catch_unwind(|| compile(&ast)) else {
        panic!("a loop-carried accumulator was accepted");
    };
    let msg = err.downcast_ref::<String>().map(String::as_str).unwrap_or("");
    assert!(msg.contains("the loop cannot carry it"), "got `{msg}`");

    // A real typo, outside any loop, still gets the plain message.
    let typo = "def main():\n    p = GEN ** 0\n    p[1] = nosuch\n    p[GEN] = GEN ** 0\n    return\n";
    let ast = parse(typo).expect("parses");
    let Err(err) = std::panic::catch_unwind(|| compile(&ast)) else {
        panic!("a typo was accepted");
    };
    let msg = err.downcast_ref::<String>().map(String::as_str).unwrap_or("");
    assert!(
        msg.contains("unbound variable `nosuch`") && !msg.contains("loop"),
        "got `{msg}`"
    );
}

/// A `match` target is a BINDER, and every field of the statement is walked.
///
/// Four facts, none of which was pinned by anything in the crate: a name target
/// is not substituted (a `Const k` used to rewrite the binder into a literal, and
/// the target was then rejected); an INDEX target is, since `sb[k]` needs `k`; the
/// scrutinee and the arms are; and the statement REBINDS its name targets, so
/// substitution stops after it. The last is the dangerous one, being the only
/// mutation of the four that produced a wrong published value rather than a
/// diagnostic.
#[test]
fn a_match_target_binds_and_every_field_is_walked() {
    let two = "def two(i: Const):\n    return GEN ** i, GEN ** i\n\n";
    let publish = "    p = GEN ** 0\n    p[1] = r\n    p[GEN] = GEN ** 0\n    return\n";
    // Arm 1 returns (g, g), so the two returns XOR to zero wherever they are read.
    let want = [F192::ZERO, g_pow(0).into()];
    let verifies = |src: &str, why: &str| {
        let program = compile(&parse(src).unwrap_or_else(|e| panic!("{why}: {e}")));
        let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
        verify(&program, &want, &proof).unwrap_or_else(|e| panic!("{why}: {e:?}"));
    };

    // A `Const` parameter whose name is also a target: the binder survives, and
    // what is read after the statement is the DISPATCH's output, not the constant.
    verifies(
        &format!(
            "{two}def pick(x, k: Const):\n    k, e = match(log(x), range(0, 2), lambda i: two(i))\n    return k + e\n\ndef main():\n    r = pick(GEN ** 1, 7)\n{publish}"
        ),
        "a Const name may also be a target",
    );

    // The scrutinee and the arms ARE substituted: both mention the constant, and a
    // missed field shows up as a `Var` reaching a position that needs an integer.
    verifies(
        &format!(
            "{two}def pick(k: Const):\n    a, b = match(log(GEN ** k), range(0, 2), lambda i: two(i + k))\n    return a + b\n\ndef main():\n    r = pick(1)\n{publish}"
        ),
        "the scrutinee and the arms see the constant",
    );

    // An INDEX target is substituted, so a `Const` index names a cell.
    verifies(
        &format!(
            "{two}def pick(x, k: Const):\n    sb = StackBuf(2)\n    sb[0] = 0\n    sb[k], e = match(log(x), range(0, 2), lambda i: two(i))\n    return sb[1] + e\n\ndef main():\n    r = pick(GEN ** 1, 1)\n{publish}"
        ),
        "a Const index target resolves to its cell",
    );

    // An `unroll` counter as a target name obeys the same rule.
    let counter = format!(
        "{two}def main():\n    for j in unroll(0, 2):\n        j, e = match(log(GEN ** 1), range(0, 2), lambda i: two(i))\n    r = j + e\n{publish}"
    );
    let _ = compile(&parse(&counter).expect("an unroll counter may also be a target"));
}

/// The same construct in a VALUE position, for the same reason. `+` there is
/// XOR, so `lvl + 1` with `lvl = 3` is 2 and not 4, silently: the leanSPHINCS guest
/// could not write a Merkle level into a tweak and carried a generated table of
/// one literal per level to get the integer reading instead.
///
/// `const(e)` reads `e` with integer arithmetic and emits the literal, so one
/// construct means one thing in both positions. The two readings must really
/// differ here, or the test proves nothing.
#[test]
fn a_value_may_ask_for_the_integer_regime() {
    // Parse and compile OUTSIDE the catch, so a negative arm can only fail on the
    // assert. Inside, `!accepted` would also hold if the program stopped parsing.
    let accepted = |expr: &str, want: u64| {
        let src = format!(
            "def main():\n    for i in unroll(3, 4):\n        v = {expr}\n        assert v == {want}\n    return\n"
        );
        let program = compile(&parse(&src).expect("parse"));
        program.execute([F192::ZERO, F192::ZERO]).is_ok()
    };

    // i = 3: the integer reading is 4, the field reading `3 XOR 1` is 2.
    assert!(accepted("const(i + 1)", 4), "const(...) is the integer reading");
    assert!(!accepted("const(i + 1)", 2), "and not the field one");
    assert!(accepted("i + 1", 2), "undeclared, `+` in a value position stays XOR");
    assert!(!accepted("i + 1", 4));

    // Subtraction has no field meaning at all, so it is only reachable this way.
    assert!(accepted("const(i - 1)", 2));

    let rejected = |src: &str, want: &str| {
        let ast = parse(src).expect("parses");
        let Err(err) = std::panic::catch_unwind(|| compile(&ast)) else {
            panic!("accepted: {src}");
        };
        let msg = err.downcast_ref::<String>().map(String::as_str).unwrap_or("");
        assert!(msg.contains(want), "wanted `{want}`, got `{msg}`");
    };
    // A `const(...)` that is not a compile-time integer names itself.
    rejected(
        "def main():\n    w = GEN ** 0\n    v = const(w + 1)\n    return\n",
        "compile-time integer",
    );
    // The wrapper reinterprets its OPERATORS, and cannot reinterpret a leaf, so a
    // leaf whose own two readings diverge is rejected rather than silently read one
    // way: `n = 2 + 3` holds `2 XOR 3` = 1 while its integer reading is 5, and
    // `assert n == 1` and `assert const(n) == 5` both used to pass in one program.
    rejected(
        "def main():\n    n = 2 + 3\n    v = const(n)\n    return\n",
        "cannot reinterpret",
    );
}

/// A `def` may not take a builtin's name. The builtin wins at the call site, so
/// the body is never reached and its constraints silently disappear: `def const(x)`
/// with an `assert` in it was skipped outright by `v = const(4)`, and skipped or
/// not depending on whether the ARGUMENT folded, so one call site had two
/// meanings. True of `f192` before `const` existed, so this is the class, not one
/// name.
#[test]
fn a_function_may_not_shadow_a_builtin() {
    for name in ["const", "f192", "addr", "blake2s", "len", "hint_witness", "StackBuf"] {
        let src = format!("def {name}(x):\n    assert x == 99\n    return x\n\ndef main():\n    return\n");
        let err = parse(&src).expect_err(&format!("`def {name}` must be rejected"));
        assert!(err.contains("is a builtin"), "got `{err}`");
    }
    // A global CONSTANT of that name is rejected too, and for a sharper reason: a
    // scalar constant is substituted textually, so `match = 4` rewrites
    // `v = match(log(x), …)` into `4(log(x), …)`.
    for name in ["match", "blake2s", "len"] {
        let src = format!("{name} = 4\n\ndef main():\n    return\n");
        let err = parse(&src).expect_err(&format!("`{name} = 4` must be rejected"));
        assert!(err.contains("is a builtin"), "got `{err}`");
    }
    // An ordinary name still works, including one that contains a builtin's.
    for name in ["helper", "constant", "addr_of"] {
        let src = format!("def {name}(x):\n    return x\n\ndef main():\n    return\n");
        parse(&src).unwrap_or_else(|e| panic!("`def {name}` must be accepted: {e}"));
    }
}

/// A compile-time branch is decided by a regime the author names.
///
/// The fold decides on the integer reading while the runtime test of the same
/// condition compares field values, so the two contradict each other whenever a
/// side's readings do. `3 + 1` is the integer 4 and the field element
/// `3 XOR 1` = 2, and `if 3 + 1 == 4` used to fold into an arm whose own
/// condition is false as a value; `if K == 4: assert K == 4` compiled clean and
/// died at witness generation.
///
/// Neither reading can win: deciding in the field breaks `if 1 + 1 == 2` and
/// every `if i + 1 == n` in an `unroll`, and cannot read `-`, `//` or `%` at
/// all. So an ambiguous condition is rejected, and `const(...)` is how the
/// author says the integer regime was meant.
#[test]
fn an_ambiguous_compile_time_branch_must_be_declared() {
    let prog = |cond: &str| {
        format!(
            "def main():
    hb = HeapBuf(4)
    if {cond}:
        hb[GEN ** 0] = 5
    else:
        hb[GEN ** 0] = 7
    p = GEN ** 0
    p[1] = hb[GEN ** 0]
    p[GEN] = GEN ** 0
    return
"
        )
    };
    let fold = |cond: &str| {
        let program = compile(&parse(&prog(cond)).unwrap_or_else(|e| panic!("{cond}: {e}")));
        let want = [F192::new(5, 0, 0), g_pow(0).into()];
        let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
        verify(&program, &want, &proof).unwrap_or_else(|e| panic!("`{cond}` did not take the then arm: {e:?}"));
    };
    // Declared, so it folds with integer arithmetic and the arm runs.
    fold("const(3 + 1 == 4)");
    fold("const(1 + 1 == 2)");
    fold("const(1 + 1 == 3 - 1)");
    // Only the field can read these, and `const(...)` decides them too. A plain
    // `if` must not: folding one would rescope its arm.
    fold("const(GEN ** 3 == GEN ** 3)");
    fold("const(2 ** 40 == 2 ** 40)");
    // Undeclared but unambiguous (6 either way), so it folds as it always did.
    fold("2 * 3 == 6");

    // Undeclared and ambiguous: rejected rather than silently decided. The
    // last three are the same condition as the first with the OTHER side
    // written using an operator the field cannot read, which is how the first
    // version of this check let them through: it compared the two sides'
    // verdicts, and `try_field_const` has no arm for `-`, `//` or `%`, so one
    // missing reading disabled the whole guard. The check is per side now.
    for cond in [
        "3 + 1 == 4",
        "1 + 1 == 2",
        "1 + 1 == 3 - 1",
        "1 + 1 == 8 // 4",
        "1 + 1 == 9 % 7",
    ] {
        let src = prog(cond);
        let ast = parse(&src).expect("parses");
        let Err(err) = std::panic::catch_unwind(|| compile(&ast)) else {
            panic!("`{cond}` was accepted");
        };
        let msg = err.downcast_ref::<String>().map(String::as_str).unwrap_or("");
        assert!(msg.contains("where a value is wanted"), "{cond}: got `{msg}`");
    }
    // A near miss of the wrapper says the word, where the ordinary parse error
    // for a malformed condition never would. A condition carrying a comparison of
    // its own is NOT a near miss, since `const(...)` is a value expression too.
    for cond in ["const (a == b)", "const(a == b"] {
        let err = parse(&prog(cond)).expect_err(cond);
        assert!(err.contains("must wrap the WHOLE condition"), "{cond}: got `{err}`");
    }
    // So one side of an ordinary comparison may be a `const(...)`, in either
    // order. Rejecting these made the two operand orders behave differently.
    fold("const(1 + 1) == 2");
    fold("2 == const(1 + 1)");
    // A variable that merely starts with `const` is not a near miss.
    let plain = "def main():\n    const = 4\n    hb = HeapBuf(4)\n    if const == 4:\n        hb[GEN ** 0] = 5\n    else:\n        hb[GEN ** 0] = 7\n    p = GEN ** 0\n    p[1] = hb[GEN ** 0]\n    p[GEN] = GEN ** 0\n    return\n";
    let program = compile(&parse(plain).expect("a name beginning with `const` is an ordinary name"));
    let want = [F192::new(5, 0, 0), g_pow(0).into()];
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &want, &proof).expect("`const == 4` is a comparison, not a wrapper");

    // Declared, but not actually decidable while compiling.
    let src = prog("const(hb == 4)");
    let ast = parse(&src).expect("parses");
    let Err(err) = std::panic::catch_unwind(|| compile(&ast)) else {
        panic!("a runtime `if const(...)` was accepted");
    };
    let msg = err.downcast_ref::<String>().map(String::as_str).unwrap_or("");
    assert!(msg.contains("asks for a compile-time decision"), "got `{msg}`");
}

/// A string literal is one opaque token.
///
/// Two passes used to read structure out of the middle of one. Comments were
/// stripped with `raw.split('#')`, so a `#` in a stream name truncated the line,
/// and the shortened line often still parsed. Bracket depth was counted without
/// any notion of a string, so every top-level splitter (arguments, `+`/`-`,
/// `*`//`/`%`, `**`, augmented assignment, comparisons) read a `,` or a `]`
/// spelled inside the name as structure: this call split into three arguments.
#[test]
fn a_string_literal_is_not_scanned_for_syntax() {
    let src = "\
def main():
    rb = StackBuf(1)
    hint_witness(rb[0:1], \"x,y#z]w\")
    p = GEN ** 0
    p[1] = rb[0]
    p[GEN] = GEN ** 0
    return
";
    let mut program = compile(&parse(src).expect("a `,`, `#` or `]` inside a string is part of the name"));
    program.set_witness("x,y#z]w", vec![vec![F192::new(7, 0, 0)]]);
    let want = [F192::new(7, 0, 0), g_pow(0).into()];
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &want, &proof).expect("the stream name survived parsing intact");
}

/// Naming a constant may not change what it means.
///
/// `K = 3 + 1` folds two ways at once. In the field, where a value expression's
/// constants live, it is `3 XOR 1` = 2 = `g^1`. As a compile-time integer, which
/// is what an index position wants, it is 4. A second g-power recognizer used to
/// match `Expr::Var` against the integer binding and read those bits as an
/// exponent, so `K` was `g^1` as a value and `g^2` as an index: one name, two
/// meanings, in one function. Spelling the constant inline was unaffected, since
/// the integer view only ever reached a *name*.
///
/// The buffer holds a distinct value per cell, so the proof pins which cell the
/// index named rather than merely that it compiled.
#[test]
fn naming_a_constant_does_not_change_which_heap_cell_it_names() {
    let src = "\
def main():
    rb = StackBuf(1)
    hint_witness(rb[0:1], \"r\")
    r = rb[0]
    hb = HeapBuf(16)
    hint_witness(hb[0:4], \"vals\")
    K = 3 + 1
    x = hb[(r * r) * K]
    p = GEN ** 0
    p[1] = x
    p[GEN] = GEN ** 0
    return
";
    let mut program = compile(&parse(src).expect("parse"));
    program.set_witness("r", vec![vec![g_pow(0).into()]]);
    program.set_witness("vals", vec![(10u64..14).map(|v| F192::new(v, 0, 0)).collect()]);
    // `r` is 1, so the index is `K` itself: cell 1, holding 11. Reading the
    // integer view instead would name cell 2, holding 12.
    let want = [F192::new(11, 0, 0), g_pow(0).into()];
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &want, &proof).expect("the index means what the value means");
}

/// A loop body that merely SHADOWS an enclosing `StackBuf` never touches it, so
/// rejecting the program names a capture that is not happening. Scoping the
/// arms took the arm-local binding out of the set the rejection consults, which
/// needs the flat "does the body bind this at all" answer instead.
#[test]
fn a_shadowed_stack_buf_is_not_a_capture() {
    let src = "\
def main():
    sa = StackBuf(2)
    sa[0] = GEN
    sa[1] = GEN ** 2
    hb = HeapBuf(8)
    for i in mul_range(1, GEN ** 3):
        if i == GEN:
            sa = StackBuf(2)
            sa[0] = GEN ** 5
            assert sa[0] == GEN ** 5
        else:
            hb[i] = GEN ** 7
    assert sa[0] == GEN
    return
";
    let exec = compile(&parse(src).expect("parse")).execute([F192::ZERO; 2]).unwrap();
    assert!(exec.unconstrained_reads.is_empty(), "no prover-chosen read");
}

/// `lower_if` FOLDS a compile-time condition and runs the taken branch without a
/// scope, so its bindings persist exactly like an `unroll` body's. Modelling it
/// as scoped over-captured, and the loop's own self-call then evaluated a name
/// the folded arm had rebound to a `StackBuf`.
#[test]
fn a_folded_branch_keeps_its_bindings() {
    let src = "\
def main():
    hb = HeapBuf(64)
    w = HeapBuf(16)
    for i in mul_range(1, GEN ** 3):
        if 1 == 1:
            w = StackBuf(2)
            w[0] = i
            w[1] = i * GEN
        hb[i] = w[1]
    assert hb[1] == GEN
    return
";
    let exec = compile(&parse(src).expect("parse")).execute([F192::ZERO; 2]).unwrap();
    assert!(exec.unconstrained_reads.is_empty(), "no prover-chosen read");
}

/// Every diagnostic names its source line. The line vector used to carry the
/// INDENT, not the source index, and the collection loop skips blanks, comments
/// and imports without counting, so nothing could name one: against a
/// 3,274-line guest an error read `inconsistent indentation` and no more.
#[test]
fn a_parse_error_names_its_source_line() {
    // Counting from 1: blank, comment, constant, blank, blank, def, let, error.
    let src = "\n# a comment\nV = 8\n\n\ndef main():\n    x = 4\n    x != y\n    return\n";
    let err = parse(src).unwrap_err();
    assert!(err.starts_with("line 8:"), "{err}");

    // A constant declaration, above the `def`s and parsed by a different loop.
    let konst = "\nN = 1\n\nM = 1 +\n\ndef main():\n    return\n";
    assert!(parse(konst).unwrap_err().starts_with("line 4:"), "{konst}");

    // Inside a block, past a blank line.
    let block =
        "\n\ndef main():\n    a = StackBuf(2)\n\n    for i in mul_range(1, 10):\n        a[0] = 1\n    return\n";
    assert!(parse(block).unwrap_err().starts_with("line 6:"));
}

/// The four diagnostics raised where no `func`/`stmt` frame is open: those two
/// stamp the line they were ENTERED on, so an enclosing header would be named
/// instead of the line that is wrong. `inconsistent indentation` is the one the
/// whole change exists for, and stamping it from the enclosing frame put it
/// 1,074 lines away from the fault in the real guest.
#[test]
fn an_error_raised_between_frames_still_names_its_line() {
    // 1 blank, 2 def, 3 let, 4 if, 5 body, 6 stray deeper indent.
    let indent = "\ndef main():\n    x = 4\n    if x == 4:\n        x = 5\n          x = 6\n    return\n";
    assert!(parse(indent).unwrap_err().starts_with("line 6:"), "{:?}", parse(indent));

    // 1 blank, 2 @inline, 3 the broken def.
    let deco = "\n@inline\nde f(x):\n    return x\n";
    assert!(parse(deco).unwrap_err().starts_with("line 3:"), "{:?}", parse(deco));

    // 1 blank, 2 def, 3 let, 4 if, 5 body, 6 the broken elif.
    let elif = "\ndef main():\n    x = 4\n    if x == 4:\n        x = 5\n    elif x ~~ 5:\n        x = 6\n    return\n";
    assert!(parse(elif).unwrap_err().starts_with("line 6:"), "{:?}", parse(elif));

    // 1 blank, 2 def, 3 let, 4 the match whose ranges are not contiguous.
    let arms = "\ndef main():\n    x = GEN ** 0\n    v = match(log(x), range(0, 1), lambda j: 5, range(2, 3), lambda j: 6)\n    return\n";
    assert!(parse(arms).unwrap_err().starts_with("line 4:"), "{:?}", parse(arms));
}

/// A replacement carrying a newline shifts every later line, so the numbers
/// above would be wrong and the injected text would land at whatever
/// indentation it fell on. A `#` is the same shape of hazard: it truncates the
/// rest of the line and changes the compiled program with no diagnostic. All
/// 134 of the guest's placeholders are clean; this keeps it that way.
#[test]
fn a_multi_line_placeholder_is_rejected() {
    let mut reps = std::collections::BTreeMap::new();
    let src = "FOO = 1\n\ndef main():\n    return\n";
    for bad in ["1\nz = 9", "1 #"] {
        reps.insert("FOO".to_string(), bad.to_string());
        let err = lean_compiler::parse_with_replacements(src, &reps).unwrap_err();
        assert!(err.contains("would reshape the line"), "{bad}: {err}");
    }
}

/// A lowering error names its line too, not just a parse error. `lower.rs` works
/// in frame cells and program counters, so the statement's line is the last
/// place that knows where the program said it: 30 diagnostics used to print a
/// Rust `Debug` dump of an AST node and nothing else.
#[test]
fn a_lowering_error_names_its_source_line() {
    // 1 blank, 2 def, 3 let, 4 store, 5 blank, 6 let, 7 the unbound read.
    let src = "\ndef main():\n    hb = HeapBuf(4)\n    hb[GEN] = 7\n\n    p = GEN ** 0\n    p[1] = nope\n    return\n";
    let err = std::panic::catch_unwind(|| {
        compile(&parse(src).expect("parse"));
    })
    .expect_err("an unbound variable must abort");
    let msg = err
        .downcast_ref::<String>()
        .cloned()
        .unwrap_or_else(|| err.downcast_ref::<&str>().map(|s| s.to_string()).unwrap_or_default());
    assert!(msg.starts_with("line 7:"), "{msg}");
}

/// And a check that fails at witness generation names it, which is the one that
/// matters day to day: a failed guest `assert` surfaces as a write-once
/// conflict, and `AGENTS.md` used to say to disassemble around the reported pc.
#[test]
fn a_failed_assert_names_its_source_line() {
    // 1 blank, 2 def, 3 let, 4 blank, 5 the assert that cannot hold.
    let src = "\ndef main():\n    x = GEN ** 3\n\n    assert x == GEN ** 4\n    return\n";
    let program = compile(&parse(src).expect("parse"));
    let err = program.execute([F192::ZERO; 2]).err().expect("the assert cannot hold");
    assert!(err.site.contains("line 5"), "{err}");
}

/// An `@inline` body lowers through the CALLER's `FnLower`, so its statements
/// move `cur_line`. Without restoring it, every instruction the caller emitted
/// after the call was blamed on whatever line the callee ended on: a line that
/// cannot fail, reported with confidence.
#[test]
fn an_inline_call_does_not_steal_the_call_site_line() {
    // 1 blank, 2 @inline, 3 def, 4 let, 5 return, 6-7 blank, 8 def main, ... 12 the assert.
    let src = "\n@inline\ndef idf(x):\n    y = x * x\n    return y\n\n\ndef main():\n    hb = HeapBuf(4)\n    hb[GEN] = GEN ** 3\n    a = hb[GEN]\n    assert idf(a) == GEN\n    return\n";
    let program = compile(&parse(src).expect("parse"));
    let err = program.execute([F192::ZERO; 2]).err().expect("the assert cannot hold");
    assert!(
        err.site.contains("line 12"),
        "the call site, not the callee's line 5: {err}"
    );
}

/// The fill blocks are not source code, so they carry the unknown line rather
/// than whatever `main` happened to end on. They are most of a small program's
/// instructions, so blaming them on a real line makes the table mostly wrong.
#[test]
fn fill_blocks_carry_no_source_line() {
    let src = "\ndef main():\n    hb = HeapBuf(4)\n    hb[GEN] = 7\n    return\n";
    let program = compile(&parse(src).expect("parse"));
    let start = program.filler.first().map(|b| b.pc).expect("main carries fill blocks") as usize;
    assert!(
        program.src_lines[start..].iter().all(|&l| l == 0),
        "a fill block must not be attributed to a source line"
    );
    assert!(
        program.src_lines[..start].iter().any(|&l| l != 0),
        "real code keeps its lines"
    );
}

/// A `match` join reads one cell per bound name, so a multi-cell `StackBuf`
/// return would bind only the run's FIRST cell and leave the rest where nothing
/// reads them. The guard must check every return, not all of them at once:
/// testing `all(is not scalar)` rather than `any(is not scalar)` fired only when
/// EVERY return was a buffer, so a `(scalar, StackBuf)` pair walked through.
#[test]
#[should_panic(expected = "StackBuf return cannot cross a match join")]
fn a_mixed_stack_buf_return_cannot_cross_a_match_join() {
    let src = "\
@inline
def f(k: Const):
    s = StackBuf(2)
    s[0] = GEN ** 7
    s[1] = GEN ** 9
    return GEN ** k, s

def main():
    x = GEN
    a, b = match(log(x), range(0, 2), lambda i: f(i))
    assert a == a
    assert b == GEN ** 7
    return
";
    compile(&parse(src).expect("parse"));
}
