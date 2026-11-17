//! Statement forms that used to be accepted and mean something else. Each of
//! these compiled clean before, so the pin is that they are now REJECTED: a
//! diagnostic is the whole fix.

use crate::common::core;
use zkdsl::{expand, parse};

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
    expand(&parse(&ok).expect("the supported compound assignments parse"));
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
    expand(&parse(&ok).expect("`16` is `g^4`"));
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
        let err = zkdsl::parse_const(src).expect_err(src);
        assert!(err.contains(want), "{src}: got `{err}`, wanted `{want}`");
    }
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
        let Err(err) = std::panic::catch_unwind(|| expand(&ast)) else {
            panic!("HeapBuf({decl}) accepted 8 bits at `{dest}`");
        };
        let msg = err.downcast_ref::<String>().map(String::as_str).unwrap_or("");
        assert!(msg.contains(want) && msg.contains("out of bounds"), "got `{msg}`");
    }
    // Both forms still compile where the buffer really does hold the bits.
    expand(&parse(&prog("8", "hb")).expect("parses"));
    expand(&parse(&prog("16", "hb * GEN ** 4")).expect("parses"));
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
        let Err(err) = std::panic::catch_unwind(|| expand(&ast)) else {
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
    expand(&parse(captured).expect("a constant may be captured"));
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
        let Err(err) = std::panic::catch_unwind(|| expand(&ast)) else {
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

    // The in-bounds run of the same shape still expands.
    let ok = "\
def main():
    hb = HeapBuf(4)
    hint_witness(hb[GEN ** 1:GEN ** 1 + 2], \"w\")
    p = GEN ** 0
    p[1] = hb[GEN]
    p[GEN] = GEN ** 0
    return
";
    expand(&parse(ok).expect("parse"));
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
    let Err(err) = std::panic::catch_unwind(|| expand(&ast)) else {
        panic!("a loop-carried accumulator was accepted");
    };
    let msg = err.downcast_ref::<String>().map(String::as_str).unwrap_or("");
    assert!(msg.contains("the loop cannot carry it"), "got `{msg}`");

    // So is a folded `if` that assigns to a captured name: its bindings outlive it.
    let folded = "def main():\n    p = GEN ** 0\n    t = 7\n    for i in mul_range(1, 8):\n        p[i] = t\n        if 2 * 3 == 6:\n            t = 9\n    return\n";
    let ast = parse(folded).expect("parses");
    let Err(err) = std::panic::catch_unwind(|| compile(&ast)) else {
        panic!("a folded `if` carried a value to the next iteration");
    };
    assert!(
        err.downcast_ref::<String>()
            .is_some_and(|m| m.contains("the loop cannot carry it"))
    );

    // A real typo, outside any loop, still gets the plain message.
    let typo = "def main():\n    p = GEN ** 0\n    p[1] = nosuch\n    p[GEN] = GEN ** 0\n    return\n";
    let ast = parse(typo).expect("parses");
    let Err(err) = std::panic::catch_unwind(|| expand(&ast)) else {
        panic!("a typo was accepted");
    };
    let msg = err.downcast_ref::<String>().map(String::as_str).unwrap_or("");
    assert!(
        msg.contains("unbound variable `nosuch`") && !msg.contains("loop"),
        "got `{msg}`"
    );
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
    // `v` stored to the heap, so its value reaches the core IR whatever it folds to.
    let store = |expr: &str| {
        core(&format!(
            "def main():\n    for i in unroll(3, 4):\n        v = {expr}\n        p = GEN ** 0\n        p[1] = v\n    return\n"
        ))
    };
    let accepted = |expr: &str, want: u64| store(expr) == store(&want.to_string());

    // i = 3: the integer reading is 4, the field reading `3 XOR 1` is 2.
    assert!(accepted("const(i + 1)", 4), "const(...) is the integer reading");
    assert!(!accepted("const(i + 1)", 2), "and not the field one");
    assert!(accepted("i + 1", 2), "undeclared, `+` in a value position stays XOR");
    assert!(!accepted("i + 1", 4));

    // Subtraction has no field meaning at all, so it is only reachable this way.
    assert!(accepted("const(i - 1)", 2));

    let rejected = |src: &str, want: &str| {
        let ast = parse(src).expect("parses");
        let Err(err) = std::panic::catch_unwind(|| expand(&ast)) else {
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
/// meanings. This is the class, not one name.
#[test]
fn a_function_may_not_shadow_a_builtin() {
    for name in ["const", "addr", "keccak", "len", "hint_witness", "StackBuf"] {
        let src = format!("def {name}(x):\n    assert x == 99\n    return x\n\ndef main():\n    return\n");
        let err = parse(&src).expect_err(&format!("`def {name}` must be rejected"));
        assert!(err.contains("is a builtin"), "got `{err}`");
    }
    // A global CONSTANT of that name is rejected too, and for a sharper reason: a
    // scalar constant is substituted textually, so `match = 4` rewrites
    // `v = match(log(x), …)` into `4(log(x), …)`.
    for name in ["match", "keccak", "len"] {
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
    // The program with the then arm in place of the `if`: what a fold that takes it expands to.
    let taken = core(
        "def main():\n    hb = HeapBuf(4)\n    hb[GEN ** 0] = 5\n    p = GEN ** 0\n    p[1] = hb[GEN ** 0]\n    p[GEN] = GEN ** 0\n    return\n",
    );
    let fold = |cond: &str| assert_eq!(core(&prog(cond)), taken, "`{cond}` did not fold to the then arm");
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
        let Err(err) = std::panic::catch_unwind(|| expand(&ast)) else {
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
    assert_eq!(core(plain), taken, "`const == 4` is a comparison, not a wrapper");

    // Declared, but not actually decidable while compiling.
    let src = prog("const(hb == 4)");
    let ast = parse(&src).expect("parses");
    let Err(err) = std::panic::catch_unwind(|| expand(&ast)) else {
        panic!("a runtime `if const(...)` was accepted");
    };
    let msg = err.downcast_ref::<String>().map(String::as_str).unwrap_or("");
    assert!(msg.contains("asks for a compile-time decision"), "got `{msg}`");
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
        let err = zkdsl::parse_with_replacements(src, &reps).unwrap_err();
        assert!(err.contains("would reshape the line"), "{bad}: {err}");
    }
}

/// An expansion error names its line too, not just a parse error. The
/// statement's line is the last place that knows where the program said it:
/// 30 diagnostics used to print a Rust `Debug` dump of an AST node and nothing
/// else.
#[test]
fn a_lowering_error_names_its_source_line() {
    // 1 blank, 2 def, 3 let, 4 store, 5 blank, 6 let, 7 the unbound read.
    let src = "\ndef main():\n    hb = HeapBuf(4)\n    hb[GEN] = 7\n\n    p = GEN ** 0\n    p[1] = nope\n    return\n";
    let err = std::panic::catch_unwind(|| {
        expand(&parse(src).expect("parse"));
    })
    .expect_err("an unbound variable must abort");
    let msg = err
        .downcast_ref::<String>()
        .cloned()
        .unwrap_or_else(|| err.downcast_ref::<&str>().map(|s| s.to_string()).unwrap_or_default());
    assert!(msg.starts_with("line 7:"), "{msg}");
}

/// A `match` join reads one cell per bound name, so a multi-cell `StackBuf`
/// return would bind only the run's FIRST cell and leave the rest where nothing
/// reads them. The guard must check every return, not all of them at once:
/// testing `all(is not scalar)` rather than `any(is not scalar)` fired only when
/// EVERY return was a buffer, so a `(scalar, StackBuf)` pair walked through.
#[test]
#[should_panic(expected = "multi-cell StackBuf return needs a `let` binding, not a match join")]
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
    expand(&parse(src).expect("parse"));
}
