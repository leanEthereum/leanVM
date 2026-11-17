//! Range checks *in the exponent*: `assert log x < log GEN ** k` (or
//! `assert log x < k`) proves `log_g(x) < k`, i.e. `x ∈ {g^0, g^1, …, g^{k-1}}`,
//! in 3 cycles: `DEREF x` bounds `log(x)` by the memory size, a `MUL` into the
//! write-once constant cell `g^{k-1}` back-solves and binds the complement
//! `y = g^{k-1-log(x)}`, and `DEREF y` bounds the complement. leanVM's DEREF
//! range-check trick, transported to g-powers; the only nondeterminism is the
//! end-of-run resolution of the two touched cells.

use zkdsl::{expand, parse};

/// Bound 0 names the empty set: rejected at compile time.
#[test]
#[should_panic(expected = "names the empty set")]
fn range_check_empty_bound_rejected() {
    let src = "def main():\n    x = 1\n    assert log x < 0\n    return\n";
    let _ = expand(&parse(src).expect("parse"));
}

/// Bounds beyond `2^30`, the largest memory, could never be complete: rejected at
/// compile time.
#[test]
#[should_panic(expected = "exceeds 2^30")]
fn range_check_bound_too_big_rejected() {
    let src = "def main():\n    x = 1\n    assert log x < 1073741825\n    return\n";
    let _ = expand(&parse(src).expect("parse"));
}

/// A `<` assert without `log` is rejected: field elements have no order, only
/// their logs do.
#[test]
#[should_panic(expected = "compares logs")]
fn range_check_without_log_rejected() {
    let src = "def main():\n    x = 1\n    assert x < 8\n    return\n";
    let _ = parse(src).map_err(|e| panic!("{e}"));
}

/// A bound that folds at parse time but is not a power of `GEN` stays a parse
/// error rather than quietly becoming a runtime bound. `log 8` names the field
/// element 8, whose g-log is nothing in particular, so a program meaning `< 8`
/// must not compile into a check that can only fail at witness generation.
#[test]
#[should_panic(expected = "must be a power of GEN")]
fn range_check_folded_non_gpower_bound_rejected() {
    let src = "def main():\n    x = GEN ** 3\n    assert log x < log 5\n    return\n";
    let _ = parse(src).map_err(|e| panic!("{e}"));
}
