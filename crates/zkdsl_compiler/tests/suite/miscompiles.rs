//! Programs that compiled to something other than what they say, or crashed the
//! compiler. Each is now rejected with a diagnostic, or compiled as written.

use crate::common::compile;
use lean_vm_core::cpu::execute;
use primitives::field::{F64, F128, g_pow};
use zkdsl_compiler::parse;

#[test]
fn ambiguous_programs_are_rejected_when_parsed() {
    let main = "\n\ndef main():\n    r = f(3)\n    return\n";
    for (src, want) in [
        // Read as `log(2x) < 8`, where Python reads `2·log x < 8`.
        (
            "def main():\n    x = GEN ** 5\n    assert log(x) * 2 < 8\n    return\n".to_string(),
            "put the whole operand inside `log(…)`",
        ),
        (
            "def main():\n    r = match(log(GEN) * GEN, range(0, 2), lambda i: i)\n    return\n".into(),
            "put the whole operand inside `log(…)`",
        ),
        // The constant was substituted into the parameter, so every arm was `f(2)`.
        (
            "K = 2\n\ndef f(a):\n    return a\n\ndef main():\n    r = match(log(GEN), range(0, 2), lambda K: f(K))\n    return\n"
                .into(),
            "lambda parameter",
        ),
        // Substitution ran past these rebindings, so `return k` returned 3.
        (
            format!("def f(k: Const):\n    if const(k == 3):\n        k = 9\n    return k{main}"),
            "Const parameter",
        ),
        (
            format!("def f(k: Const):\n    for j in unroll(0, 1):\n        k = 9\n    return k{main}"),
            "Const parameter",
        ),
        (
            "def main():\n    for i in unroll(0, 1):\n        if const(i == 0):\n            i = 7\n        print(i)\n    return\n"
                .into(),
            "`unroll` counter",
        ),
        // Truncated to a 4-cell buffer whose bound check still allowed 2^32 + 4.
        (
            "def main():\n    b = HeapBuf(4294967300)\n    return\n".into(),
            "does not fit in u32",
        ),
        // Sliced backwards and panicked.
        ("def f)(:\n    return\n".into(), "needs `)` after `(`"),
        // Substituted into every `GEN ** k`.
        ("GEN = 3\n\ndef main():\n    return\n".into(), "builtin"),
        // Fell back to the field reading, `2^128 - 1 XOR 1`.
        (
            "X = 340282366920938463463374607431768211455 + 1\n\ndef main():\n    return\n".into(),
            "overflows",
        ),
    ] {
        let err = parse(&src).err().unwrap_or_else(|| panic!("accepted:\n{src}"));
        assert!(err.contains(want), "`{err}` does not say `{want}`, for:\n{src}");
    }
}

#[test]
fn ill_formed_calls_are_rejected_when_lowered() {
    for (src, want) in [
        // `main` halts the machine, so the call ended the run with a success.
        (
            "def f():\n    main()\n    return\n\ndef main():\n    f()\n    return\n",
            "`main` is the entry point",
        ),
        // Read the third cell through a two-cell parameter.
        (
            "@inline\ndef f(s: StackBuf(2)):\n    return s[0]\n\ndef main():\n    t = StackBuf(3)\n    t[0] = 1\n    r = f(t)\n    return\n",
            "is a StackBuf(2), got a StackBuf(3)",
        ),
        (
            "def main():\n    b = StackBuf(41)\n    hint_decompose_bits_exponent(b, GEN, 41)\n    return\n",
            "at most 40 bits",
        ),
        // `at + count` wrapped to 1, and the windows were written below the buffer.
        (
            "def main():\n    b = StackBuf(1)\n    hint_windows_exponent(b, GEN, 0, 1, 2, 4294967295)\n    return\n",
            "its StackBuf destination has 1",
        ),
        // `cap=` absorbs with no padding, and ignored `pad_tail=1`.
        (
            "def main():\n    s = StackBuf(13)\n    keccak([0, 0], [0, 0], s)\n    t = StackBuf(4)\n    o = StackBuf(13)\n    keccak([0, 0], [0, 0], o, tail=t, cap=s, pad_tail=1)\n    return\n",
            "takes no len= or pad_tail=",
        ),
    ] {
        let ast = parse(src).unwrap();
        let Err(err) = std::panic::catch_unwind(|| compile(&ast)) else {
            panic!("accepted:\n{src}");
        };
        let msg = err.downcast_ref::<String>().map(String::as_str).unwrap_or("");
        assert!(msg.contains(want), "`{msg}` does not say `{want}`, for:\n{src}");
    }
}

#[test]
fn programs_compile_as_written() {
    let runs = |src: &str, witness: &[(&str, F128)]| {
        let witness: Vec<_> = witness
            .iter()
            .map(|&(name, v)| (name.to_string(), vec![vec![v]]))
            .collect();
        execute(&compile(&parse(src).unwrap()), &witness, [F128::ZERO; 2])
            .unwrap_or_else(|e| panic!("{e:?}, for:\n{src}"));
    };
    // Integers past `u32` were compared as field elements, `2^33 XOR 2^33 = 0`.
    runs(
        "def main():\n    if const(8589934592 + 8589934592 == 17179869184):\n        x = 1\n    else:\n        assert GEN == 1\n    return\n",
        &[],
    );
    // The stream name was substituted too, so the run read stream `8`.
    runs(
        "SEED = 8\n\ndef main():\n    s = StackBuf(1)\n    hint_witness(s, \"SEED\")\n    assert s[0] == 8\n    return\n",
        &[("SEED", F128::from(F64(8)))],
    );
    // Identical builtin arms were taken for a fused dispatch to a function named after the builtin.
    runs(
        "def main():\n    r = match(log(GEN), range(0, 2), lambda j: const(36893488147419103233))\n    assert r == 36893488147419103233\n    return\n",
        &[],
    );
    // A call in a runtime bound ran twice, popping the stream twice.
    runs(
        "def stop():\n    s = hint_witness(\"stop\")\n    assert log(s) < 8\n    return s\n\ndef main():\n    for i in mul_range(1, stop()):\n        x = i\n    return\n",
        &[("stop", g_pow(3).into())],
    );
    // A `HeapBuf` after a branch whose first arm emits nothing was allocated on that arm's exit jump, which a run
    // taking another arm skips: its pointer stayed unwritten. An `if` with an empty fall-through arm, a `match` whose
    // arm 0 is an inline call returning its target, and a chain whose head's arms are only its chain jumps.
    runs(
        "def main():\n    x = hint_witness(\"x\")\n    if x != GEN:\n        y = x * x\n    b = HeapBuf(2)\n    b[1] = 5\n    return\n",
        &[("x", g_pow(2).into())],
    );
    let main = "def main():\n    x = hint_witness(\"x\")\n    s = StackBuf(1)\n    s[0] = 3\n";
    let after = "    b = HeapBuf(2)\n    b[1] = 5\n    return\n";
    runs(
        &format!(
            "@inline\ndef f(z, i: Const):\n    if const(i == 1):\n        w = z * z\n    return z\n\n{main}    s[0] = match(log(x), range(0, 2), lambda i: f(s[0], i))\n{after}"
        ),
        &[("x", g_pow(1).into())],
    );
    runs(
        &format!(
            "@inline\ndef f(z, i: Const, k: Const):\n    if const(k == 1):\n        w = z * z\n    return z\n\n{main}    for k in unroll(0, 2):\n        s[0] = match(log(x), range(0, 2), lambda i: f(s[0], i, k))\n{after}"
        ),
        &[("x", g_pow(0).into())],
    );
    // A `HeapBuf` moved before the statement holding the first call went ahead of one queued just before that
    // statement, so the program was rejected.
    for e in [0, 1] {
        runs(
            "def sq(x):\n    return x * x\n\ndef main():\n    a = hint_witness(\"a\")\n    early = HeapBuf(2)\n    if a == GEN:\n        y = sq(a)\n    late = HeapBuf(2)\n    late[1] = 5\n    early[1] = 5\n    return\n",
            &[("a", g_pow(e).into())],
        );
    }
    // A builtin call as a store's value was looked up as a function.
    compile(
        &parse("def main():\n    bits = StackBuf(4)\n    out = StackBuf(1)\n    out[0] = hint_log2_ceil(bits, 4, 0)\n    return\n")
            .unwrap(),
    );
}

/// A `return` nested in `main` was ignored, the code after it running anyway.
#[test]
#[should_panic(expected = "`return` in `main` is allowed only as its last statement")]
fn nested_return_in_main_is_rejected() {
    let src = "def main():\n    x = 1\n    if x == 1:\n        return\n    assert x == 2\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// The copy-removal pass (`opt.rs`) across branches and dispatch arms: an honest program runs, and one whose assert
/// fails does not. Arms of a `match` share their frame cells, and a branch's join cell has one writer per path.
#[test]
fn copy_removal_keeps_every_path() {
    let run = |src: &str| execute(&compile(&parse(src).unwrap()), &[], [F128::ZERO; 2]);
    let honest = [
        // `x[0]` is 1 on one path only, so `x[0] * w` is no copy of `w`.
        "def f(c, y, w, v):\n    x = StackBuf(1)\n    if c == 0:\n        x[0] = 1\n    else:\n        x[0] = y\n    z = x[0] * w\n    assert z == v\n    return 0\n\ndef main():\n    r = f(GEN, GEN ** 3, GEN ** 5, GEN ** 8)\n    return\n",
        // Arm 0's temporary is retargeted; arm 1 reuses its cell for an unrelated value.
        "def f(x, c, a, b):\n    r = match(log(c), range(0, 2), lambda i: g(x, a, b, i))\n    return r\n\n@inline\ndef g(x, a, b, i: Const):\n    if const(i == 0):\n        t = a * b\n        assert t == x\n        y = 0\n    else:\n        u = a + b\n        y = u * u\n    return y\n\ndef main():\n    r = f(GEN ** 2, GEN, GEN ** 3, GEN ** 4)\n    return\n",
        // The assert on `v`, an argument, runs on one path only: retargeting `t` into `v` must not move it.
        "def f(a, v, c):\n    t = a * a\n    if c == 0:\n        assert t == v\n    return 0\n\ndef main():\n    r = f(GEN, GEN ** 5, GEN)\n    return\n",
        // Each arm jumps through the same cells to its own join, where `t` is still read.
        "def f(c, a, b, p):\n    r = match(log(c), range(0, 2), lambda i: g(a, b, p, i))\n    return r\n\n@inline\ndef g(a, b, p, i: Const):\n    if const(i == 0):\n        t = a * b\n        s = StackBuf(1)\n        s[0] = t\n        if p == 0:\n            print(a)\n        else:\n            print(b)\n        y = t * s[0]\n    else:\n        t2 = a + b\n        s2 = StackBuf(1)\n        s2[0] = t2\n        if p == 0:\n            print(b)\n        else:\n            print(a)\n        y = p * b\n    return y\n\ndef main():\n    r = f(GEN ** 0, GEN ** 3, GEN ** 4, GEN)\n    assert r == GEN ** 14\n    return\n",
    ];
    for src in honest {
        run(src).unwrap_or_else(|e| panic!("{e:?}, for:\n{src}"));
    }
    // `v` is written before the branch and only asserted after it: the assert must survive.
    let failing = "def f(a, b):\n    v = a * b\n    if a == GEN:\n        return 0\n    assert a + b == v\n    return v\n\ndef main():\n    r = f(GEN ** 2, GEN ** 3)\n    return\n";
    assert!(run(failing).is_err(), "an assert that fails was compiled away");
}

/// `x ** 0` never evaluated `x`, dropping the assertion in `one()`.
#[test]
fn zero_power_evaluates_its_base() {
    let src = "def one():\n    x = hint_witness(\"x\")\n    assert x == 1\n    return x\n\ndef main():\n    y = one() ** 0\n    return\n";
    let run = |x: u64| {
        execute(
            &compile(&parse(src).unwrap()),
            &[("x".into(), vec![vec![F128::from(F64(x))]])],
            [F128::ZERO; 2],
        )
    };
    run(1).unwrap();
    assert!(run(2).is_err());
}

/// A fused `match` evaluated the shared arguments before its selector, so the selector's `HeapBuf` was allocated after
/// the arguments' one. Arm `i` returns its argument times `g^(10 i)`, so the relation also pins the arm that ran. The
/// second `match` has distinct arms and does not fuse: both lowerings must agree.
#[test]
fn fused_match_evaluates_its_selector_first() {
    let head = "@inline\ndef sel(saved):\n    first = HeapBuf(1)\n    saved[1] = first\n    return GEN\n\n@inline\ndef arg():\n    second = HeapBuf(1)\n    return second\n\ndef f(p, i: Const):\n    return p * GEN ** (10 * i)\n\ndef main():\n    saved = HeapBuf(1)\n";
    for arms in [
        "range(0, 2), lambda i: f(arg(), i)",
        "range(0, 1), lambda i: f(arg(), i), range(1, 2), lambda i: f(arg() * 1, i)",
    ] {
        let src =
            format!("{head}    r = match(log(sel(saved)), {arms})\n    assert r == saved[1] * GEN ** 11\n    return\n");
        execute(&compile(&parse(&src).unwrap()), &[], [F128::ZERO; 2]).unwrap_or_else(|e| panic!("{e:?}, for:\n{src}"));
    }
}
