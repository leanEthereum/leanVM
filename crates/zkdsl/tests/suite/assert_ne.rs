//! `assert a != b`: a proof-enforced inequality. It lowers to `XOR x = a + b`,
//! a hinted `inv = x⁻¹`, `MUL p = x·inv` and `SET p = 1`, the write-once
//! conflict on `p` being the assertion. Sound whatever the hint: `x = 0` forces
//! `p = 0`, which cannot then be set to `1`. Three rows and no `JUMP`.

use zkdsl::{expand, parse};

/// A compile-time-equal literal pair (e.g. after `Const`-arg substitution) is a
/// hard compile error: the assertion could never hold, so it is caught early.
#[test]
#[should_panic(expected = "compile-time-equal")]
fn assert_ne_compile_time_equal_rejected() {
    let src = "def main():\n    assert 5 != 5\n    return\n";
    let _ = expand(&parse(src).expect("parse"));
}
