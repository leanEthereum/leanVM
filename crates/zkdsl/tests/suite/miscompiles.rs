//! Programs that compiled to something other than what they say, or crashed the
//! compiler. Each is now rejected by the parser with a diagnostic.

use zkdsl::parse;

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
