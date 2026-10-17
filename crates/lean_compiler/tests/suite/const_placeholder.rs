//! Global constants and compile-time placeholders in the zkDSL.
//!
//! A top-level `NAME = <const-expr>` is a **global constant**: it is evaluated
//! to its field value and substituted (as one literal) everywhere its name
//! appears below: so a constant is usable in every position a literal is,
//! including `StackBuf`/`HeapBuf` sizes, `**` exponents, and `assert log _ < _`
//! bounds. A **placeholder** is any identifier text-replaced before parsing via
//! [`parse_with_replacements`]; the idiom is a placeholder feeding a constant
//! (`V = V_PLACEHOLDER` with `"V_PLACEHOLDER" ↦ "128"`), as in leanVM.

use std::collections::BTreeMap;

use lean_compiler::{compile, parse, parse_with_replacements};
use leanvm_core::cpu::{prove, verify};
use primitives::field::g_pow;

/// A global constant substitutes exactly like writing its value inline: even
/// in a `StackBuf` size, which demands a parse-time literal. The two programs
/// produce identical ASTs.
#[test]
fn const_inlines_like_literal() {
    let with_const = "\
N = 5

def main():
    a = StackBuf(N)
    a[0] = N
    a[1] = N + 2
    assert a[0] == 5
    return
";
    let inlined = "\
def main():
    a = StackBuf(5)
    a[0] = 5
    a[1] = 5 + 2
    assert a[0] == 5
    return
";
    let ac = parse(with_const).expect("const program parses");
    let ai = parse(inlined).expect("inlined program parses");
    assert_eq!(
        crate::common::without_lines(&ac),
        crate::common::without_lines(&ai),
        "constant must inline to its value"
    );
    let _ = compile(&ac); // and it lowers to a real program
}

/// A constant may be used as a `**` exponent and an `assert log _ < _` bound -
/// positions that previously required a bare integer literal.
#[test]
fn const_in_literal_only_positions() {
    let src = "\
LEN = 3
BOUND = 8

def main():
    x = GEN ** LEN
    assert log x < BOUND
    return
";
    let inlined = "\
def main():
    x = GEN ** 3
    assert log x < 8
    return
";
    assert_eq!(
        crate::common::without_lines(&parse(src).unwrap()),
        crate::common::without_lines(&parse(inlined).unwrap()),
    );
    let _ = compile(&parse(src).unwrap());
}

/// A global constant may be a g-power, which is how the ISA writes every
/// address and index.
///
/// The scalar path tried an `f192` literal, then an integer expression, and
/// stopped, so `GEN ** 2` was rejected as "not a compile-time integer constant
/// expression" while `f192(4, 0, 0)` naming the same element was accepted. It
/// now falls back to the field evaluator and renders the value as a decimal
/// wherever it fits the low two limbs, so the constant still works in the
/// positions that demand a literal rather than only as a value.
#[test]
fn a_global_constant_may_be_a_g_power() {
    for (decl, exp) in [("GEN ** 2", 2usize), ("GEN * GEN", 2), ("GEN ** 70", 70)] {
        let src = format!(
            "STEP = {decl}

def main():
    p = GEN ** 0
    p[1] = STEP
    p[GEN] = GEN ** 0
    return
"
        );
        let program = compile(&parse(&src).unwrap_or_else(|e| panic!("`{decl}`: {e}")));
        let want = [g_pow(exp).into(), g_pow(0).into()];
        let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
        verify(&program, &want, &proof).unwrap_or_else(|e| panic!("`{decl}` is not g^{exp}: {e:?}"));
    }
}

/// A constant may reference an earlier constant (chaining). `B = A` gives `B`
/// the value of `A`; both are usable as sizes.
#[test]
fn const_chains() {
    let src = "\
A = 4
B = A

def main():
    p = StackBuf(A)
    q = StackBuf(B)
    return
";
    let inlined = "\
def main():
    p = StackBuf(4)
    q = StackBuf(4)
    return
";
    assert_eq!(
        crate::common::without_lines(&parse(src).unwrap()),
        crate::common::without_lines(&parse(inlined).unwrap()),
    );
    let _ = compile(&parse(src).unwrap());
}

/// Constant expressions use **integer** arithmetic (`+ - * / **`), not runtime
/// field arithmetic, so derived sizes/counts come out right. Filled
/// via placeholders, the whole set of derivations resolves to plain literals.
#[test]
fn const_integer_arithmetic_derivations() {
    let templated = "\
V = V_PLACEHOLDER
W = W_PLACEHOLDER
LOG_LIFETIME = LOG_LIFETIME_PLACEHOLDER
CHAIN_STEPS = W - 1
N_TWEAK_WORDS = 2 + CHAIN_STEPS * V + LOG_LIFETIME
N_TWEAK_BLOCKS = N_TWEAK_WORDS / 2
FIXED_BLOCKS = 1 + N_TWEAK_BLOCKS + LOG_LIFETIME / 2
FIXED_BYTES = FIXED_BLOCKS * 32
N_SIGS_BOUND = 2 ** 16

def main():
    a = StackBuf(N_TWEAK_WORDS)
    x = GEN ** FIXED_BYTES
    assert log x < N_SIGS_BOUND
    for i in unroll(0, N_TWEAK_BLOCKS):
        assert a[0] == W
    return
";
    // V = 42, W = 8, LOG_LIFETIME = 32  → an XMSS-shaped instance.
    let mut repl = BTreeMap::new();
    repl.insert("V_PLACEHOLDER".to_string(), "42".to_string());
    repl.insert("W_PLACEHOLDER".to_string(), "8".to_string());
    repl.insert("LOG_LIFETIME_PLACEHOLDER".to_string(), "32".to_string());
    let filled = parse_with_replacements(templated, &repl).expect("derivations resolve");

    // N_TWEAK_WORDS = 2 + 7*42 + 32 = 328, N_TWEAK_BLOCKS = 164,
    // FIXED_BLOCKS = 1 + 164 + 16 = 181, FIXED_BYTES = 5792, N_SIGS_BOUND = 65536.
    let concrete = "\
def main():
    a = StackBuf(328)
    x = GEN ** 5792
    assert log x < 65536
    for i in unroll(0, 164):
        assert a[0] == 8
    return
";
    assert_eq!(
        crate::common::without_lines(&filled),
        crate::common::without_lines(&parse(concrete).unwrap())
    );
    let _ = compile(&filled);
}

/// `const(...)` is TRANSPARENT in a parse-time position, and the test is that
/// the wrapped and bare spellings parse to the same AST.
///
/// The wrapper means "read this with integer arithmetic". A size, a count, an
/// exponent, a bound and a stack index have no other reading, so it changes
/// nothing there. It was a parse error in a `StackBuf` size, a `log` bound and a
/// top-level constant while being accepted in a `HeapBuf` size, an `unroll` count
/// and a `GEN **` exponent, which made one construct mean two things depending on
/// where it stood.
#[test]
fn const_is_transparent_where_the_reading_is_already_integer() {
    for (wrapped, bare) in [
        ("s = StackBuf(const(2 + 2))", "s = StackBuf(4)"),
        ("h = HeapBuf(const(2 + 2))", "h = HeapBuf(4)"),
        ("x = GEN ** const(1 + 1)", "x = GEN ** 2"),
    ] {
        let src = |b: &str| format!("def main():\n    {b}\n    return\n");
        assert_eq!(
            crate::common::without_lines(&parse(&src(wrapped)).unwrap_or_else(|e| panic!("{wrapped}: {e}"))),
            crate::common::without_lines(&parse(&src(bare)).expect("bare")),
            "`{wrapped}` must parse as `{bare}`"
        );
    }
    // A `log` bound and an `unroll` count, which are their own parse paths.
    let bound = |b: &str| format!("def main():\n    v = GEN ** 2\n    assert log v < {b}\n    return\n");
    assert_eq!(
        crate::common::without_lines(&parse(&bound("const(4 + 4)")).expect("wrapped bound")),
        crate::common::without_lines(&parse(&bound("8")).expect("bare bound")),
    );
    // An `unroll` count keeps its expression for the lowerer to fold, in either
    // spelling, so the baseline is the unwrapped expression rather than a literal.
    let count = |b: &str| format!("def main():\n    for i in unroll(0, {b}):\n        v = 1\n    return\n");
    let unrolled = |b: &str| compile(&parse(&count(b)).unwrap_or_else(|e| panic!("{b}: {e}"))).code_len();
    assert_eq!(
        unrolled("const(1 + 1)"),
        unrolled("1 + 1"),
        "the count must fold the same"
    );
    assert_eq!(unrolled("const(1 + 1)"), unrolled("2"));
    // And a global constant, where the whole declaration is already integer.
    assert_eq!(
        crate::common::without_lines(
            &parse("N = const(3 + 1)\n\ndef main():\n    s = StackBuf(N)\n    return\n").expect("wrapped")
        ),
        crate::common::without_lines(&parse("N = 4\n\ndef main():\n    s = StackBuf(N)\n    return\n").expect("bare")),
    );
    // Transparent means transparent: an illegal value is still illegal, so the
    // wrapper is no route past a bound the bare spelling would fail.
    for b in ["0", "const(0)"] {
        let ast = parse(&bound(b)).expect("parses");
        let Err(err) = std::panic::catch_unwind(|| compile(&ast)) else {
            panic!("`{b}` was accepted as a bound");
        };
        let msg = err.downcast_ref::<String>().map(String::as_str).unwrap_or("");
        assert!(msg.contains("empty set"), "{b}: got `{msg}`");
    }
}

/// A placeholder is text-replaced before parsing; feeding a constant is the
/// idiom. The filled program equals the one written with the value inline.
#[test]
fn placeholder_fills_constant() {
    let templated = "\
V = V_PLACEHOLDER

def main():
    a = StackBuf(V)
    a[0] = V
    assert a[0] == 7
    return
";
    let mut repl = BTreeMap::new();
    repl.insert("V_PLACEHOLDER".to_string(), "7".to_string());
    let filled = parse_with_replacements(templated, &repl).expect("placeholder fills");

    let concrete = "\
def main():
    a = StackBuf(7)
    a[0] = 7
    assert a[0] == 7
    return
";
    assert_eq!(
        crate::common::without_lines(&filled),
        crate::common::without_lines(&parse(concrete).unwrap())
    );
    let _ = compile(&filled);
}

/// Replacement is identifier-bounded: a key does not match a substring of a
/// longer identifier.
#[test]
fn placeholder_is_identifier_bounded() {
    let src = "\
def main():
    FOOBAR = 1
    x = FOOBAR
    assert x == 1
    return
";
    let mut repl = BTreeMap::new();
    repl.insert("FOO".to_string(), "999".to_string());
    // `FOO` must NOT rewrite the `FOO` inside `FOOBAR`.
    assert_eq!(
        crate::common::without_lines(&parse_with_replacements(src, &repl).unwrap()),
        crate::common::without_lines(&parse(src).unwrap()),
    );
}

/// An unfilled placeholder (or an undeclared constant) is a clear error, and a
/// constant may not be declared twice.
#[test]
fn errors() {
    let unfilled = "\
V = V_PLACEHOLDER

def main():
    return
";
    let err = parse(unfilled).expect_err("an unfilled placeholder must fail");
    assert!(
        err.contains("V_PLACEHOLDER"),
        "error should name the placeholder: {err}"
    );

    let dup = "\
N = 1
N = 2

def main():
    return
";
    assert!(parse(dup).is_err(), "a constant declared twice must fail");

    // A top-level line that is neither a `def` nor a `NAME = value` is rejected.
    let junk = "\
1 + 1

def main():
    return
";
    assert!(parse(junk).is_err(), "malformed top-level line must fail");
}
