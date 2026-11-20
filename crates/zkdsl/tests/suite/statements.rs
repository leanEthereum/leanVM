//! Statement forms that used to be accepted and mean something else. Each of
//! these compiled clean before, so the pin is that they are now REJECTED: a
//! diagnostic is the whole fix.

use zkdsl::parse;

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
    // The five that ARE supported still parse.
    let ok = body("x += 1\n    x *= 2\n    x //= 2\n    x %= 3\n    x -= 1");
    parse(&ok).expect("the supported compound assignments parse");
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
    // must be accepted.
    let ok = src.replace("mul_range(1, 10)", "mul_range(1, 16)");
    parse(&ok).expect("`16` is `g^4`");
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

/// Two names that used to pick a winner.
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

/// A near miss of the `const(...)` wrapper on a condition says the word, where the
/// ordinary parse error for a malformed condition never would.
#[test]
fn a_near_miss_of_a_declared_condition_says_so() {
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
    for cond in ["const (a == b)", "const(a == b"] {
        let err = parse(&prog(cond)).expect_err(cond);
        assert!(err.contains("must wrap the WHOLE condition"), "{cond}: got `{err}`");
    }
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
