use crate::common::compile;
use lean_vm_core::cpu::execute;
use primitives::field::{F64, F128};
use zkdsl_compiler::parse;

const STEP: &str = r#"
@inline
def step(cursor, acc):
    x = cursor[GEN ** 0]
    y = acc * x
    return y, x, cursor * GEN

@inline
def word(a, b, j: Const):
    w = a
    if const(j == 1):
        w = b
    return w

def main():
    public = 1
    seed = public[1]
    b = HeapBuf(2)
    for i in unroll(0, 2):
        b[GEN ** i] = seed * GEN ** i
    cur = b
    acc = seed
    for i in unroll(0, 2):
        BODY
    out = HeapBuf(3)
    out[1] = acc
    out[GEN] = x
    out[GEN ** 2] = WORD
    return
"#;

/// An inlined call's returned names bind as `let`s would: a returned scalar or
/// shifted pointer aliases what the body computed, so the call takes no more
/// cells or instructions than its body written in place.
#[test]
fn inlined_returns_cost_nothing_over_the_body() {
    let call = STEP
        .replace("BODY", "acc, x, cur = step(cur, acc)")
        .replace("WORD", "word(acc, x, 1)");
    let in_place = STEP
        .replace(
            "BODY",
            "x = cur[GEN ** 0]\n        acc = acc * x\n        cur = cur * GEN",
        )
        .replace("WORD", "x");
    let public = [F128::from(F64(0x1234_5678)), F128::ZERO];
    let call = compile(&parse(&call).unwrap());
    let in_place = compile(&parse(&in_place).unwrap());
    let (a, b) = (
        execute(&call, &[], public).unwrap(),
        execute(&in_place, &[], public).unwrap(),
    );
    assert!(a.unconstrained_reads.is_empty());
    assert_eq!(a.mem_used, b.mem_used, "cells: inlined call against the body in place");
    assert_eq!(a.rows(), b.rows(), "rows: inlined call against the body in place");
}

/// The `@inline` functions [`inlined_calls_compute_what_real_calls_do`]'s programs call.
const PRELUDE: &str = "
C = [GEN ** 2]

@inline
def five():
    return 5

@inline
def scale(x, k):
    return x * k + 0

@inline
def prod(a, b):
    return a * b

@inline
def first(s: StackBuf(1)):
    return s[0]

@inline
def sq(x):
    x = x * x
    return x

@inline
def rd(b, i):
    return b[i]

@inline
def pick(a, b, k: Const):
    r = five()
    if const(k == 1):
        r = b
    if const(k == 2):
        r = prod(a, b)
    return r

@inline
def pair(a, b, k: Const):
    return pick(a, b, k), a

@inline  # in both builds: only an inlined `StackBuf` return crosses a join
def run(s: StackBuf(1), t: StackBuf(1), k: Const):
    if const(k == 0):
        t = s
    return t
";

/// Each program built with its `@inline` functions expanded and as real calls: on every run, its hinted words `w` and
/// public input, both builds accept exactly when `ok` says, and read no unwritten cell.
#[test]
fn inlined_calls_compute_what_real_calls_do() {
    let n = |v: u64| F64(v);
    let w = |v: &[F64]| v.iter().map(|&x| F128::from(x)).collect::<Vec<_>>();
    let pi = |a: F64, b: F64| [F128::from(a), F128::from(b)];
    let g = |k: u128| F64::G.pow(k);
    let (a, b) = (n(3), n(5));
    let cases = [
        (
            "a constant return",
            "w = hint_witness(\"w\")\n    assert five() == w\n    assert w == five()\n    y = five()\n    \
             p[1] = y\n    p[GEN] = w",
            vec![(w(&[n(5)]), pi(n(5), n(5)), true), (w(&[n(6)]), pi(n(5), n(6)), false)],
        ),
        (
            "a constant argument",
            "w = hint_witness(\"w\")\n    y = scale(w, 1)\n    s = StackBuf(1)\n    s[0] = scale(w, 1)\n    \
             p[1] = y\n    p[GEN] = s[0] * scale(w, GEN)",
            vec![(w(&[n(7)]), pi(n(7), n(7) * n(7) * g(1)), true)],
        ),
        (
            "a constant argument takes its field reading",
            "w = hint_witness(\"w\")\n    k = 7 - 2\n    p[1] = scale(w, 3 + 5) * k\n    p[GEN] = scale(w, 3 * 3)",
            vec![
                (w(&[n(7)]), pi(n(7) * n(6) * n(5), n(7) * n(5)), true),
                (w(&[n(7)]), pi(n(7) * n(8) * n(5), n(7) * n(9)), false),
            ],
        ),
        (
            "a product the caller computes too",
            "a = hint_witness(\"w\")\n    b = hint_witness(\"w\")\n    c = hint_witness(\"w\")\n    \
             assert prod(a, b) == c\n    assert a * b == c\n    y = prod(a, b)\n    p[1] = y\n    p[GEN] = a * b",
            vec![
                (w(&[a, b, a * b]), pi(a * b, a * b), true),
                (w(&[a, b, n(6)]), pi(a * b, a * b), false),
            ],
        ),
        (
            "a returned cell is still write-once",
            "w = hint_witness(\"w\")\n    sb = StackBuf(1)\n    sb[0] = w\n    y = first(sb)\n    sb[0] = 9\n    \
             p[1] = y\n    p[GEN] = first(sb)",
            vec![(w(&[n(9)]), pi(n(9), n(9)), true), (w(&[n(8)]), pi(n(8), n(8)), false)],
        ),
        (
            "match joins",
            "x = hint_witness(\"w\")\n    a = hint_witness(\"w\")\n    b = hint_witness(\"w\")\n    \
             assert log(x) < 3\n    u, v = match(log(x), range(0, 3), lambda i: pair(a, b, i))\n    \
             r = match(log(x), range(0, 3), lambda i: pick(a, b, i))\n    s = [a]\n    t = [b]\n    \
             q = match(log(x), range(0, 3), lambda i: run(s, t, i))\n    p[1] = u * v\n    p[GEN] = r * q",
            vec![
                (w(&[g(0), a, b]), pi(n(5) * a, n(5) * a), true),
                (w(&[g(1), a, b]), pi(b * a, b * b), true),
                (w(&[g(2), a, b]), pi(a * b * a, a * b * b), true),
                (w(&[g(1), a, b]), pi(n(5) * a, n(5) * a), false),
            ],
        ),
        (
            "a g-power and a constant-array index",
            "w = hint_witness(\"w\")\n    b = HeapBuf(4)\n    b[GEN ** 2] = w\n    p[1] = rd(b, GEN ** 2)\n    \
             p[GEN] = rd(b, C[0])",
            vec![(w(&[n(7)]), pi(n(7), n(7)), true)],
        ),
        (
            "a nested call shadowing its argument",
            "x = hint_witness(\"w\")\n    y = sq(sq(x))\n    p[1] = y\n    p[GEN] = x",
            vec![(w(&[a]), pi(a * a * a * a, a), true)],
        ),
    ];
    for (name, main, runs) in cases {
        let src = format!("{PRELUDE}\ndef main():\n    p = GEN ** 0\n    {main}\n    return\n");
        let inlined = compile(&parse(&src).unwrap_or_else(|e| panic!("{name}: {e}")));
        let called = compile(&parse(&src.replace("@inline\n", "")).unwrap_or_else(|e| panic!("{name}: {e}")));
        for (words, public, ok) in runs {
            let witness = [("w".to_string(), words.iter().map(|&x| vec![x]).collect())];
            for (build, program) in [("inlined", &inlined), ("called", &called)] {
                match execute(program, &witness, public) {
                    Ok(run) => {
                        assert!(ok, "{name}, {build}: accepts {words:?}, {public:?}");
                        assert!(
                            run.unconstrained_reads.is_empty(),
                            "{name}, {build}: reads an unwritten cell"
                        );
                    }
                    Err(e) => assert!(!ok, "{name}, {build}: rejects {words:?}, {public:?}: {e}"),
                }
            }
        }
    }
}

/// A constant argument folds in the body, and a call with a destination computes into it: neither takes a cell or a row
/// over the body written in place.
#[test]
fn constant_arguments_and_destinations_cost_nothing() {
    let src = |body: &str| {
        format!(
            "@inline\ndef scale(x, k):\n    return x * k\n\n@inline\ndef prod(a, b):\n    return a * b\n\n\
             def main():\n    public = 1\n    w = public[1]\n    s = StackBuf(1)\n    {body}\n    out = HeapBuf(2)\n    \
             out[1] = y\n    out[GEN] = s[0]\n    return\n"
        )
    };
    let call = compile(&parse(&src("y = w * scale(2, 3)\n    s[0] = prod(w, w)")).unwrap());
    let in_place = compile(&parse(&src("y = w * 6\n    s[0] = w * w")).unwrap());
    let public = [F128::from(F64(0x1234_5678)), F128::ZERO];
    let (a, b) = (
        execute(&call, &[], public).unwrap(),
        execute(&in_place, &[], public).unwrap(),
    );
    assert_eq!(a.mem_used, b.mem_used, "cells");
    assert_eq!(a.rows(), b.rows(), "rows");
}
