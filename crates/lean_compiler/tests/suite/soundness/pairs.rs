//! Layer 2: equivalence. Two spellings the language documents as interchangeable
//! must accept exactly the same trials.
//!
//! This is the layer that finds dropped constraints without anyone having to
//! guess where they went. A dropped store is invisible on its own: the program
//! still runs, and its one honest witness still passes. It becomes visible the
//! moment you have a second spelling of the same intent that *kept* the store,
//! because then one side rejects a witness the other accepts, and the more
//! permissive side is the buggy one.
//!
//! Every pair here is a promise `zkDSL.md` makes. When one fails, quote the
//! promise in the bug report; the `why` field is there to be quoted.

use super::{Pair, Trial, check_pair, g, k};
use primitives::field::F192;

/// One hinted pair of cells, published so the trial's public input pins them.
fn two(a: F192, b: F192) -> Trial {
    Trial::new([a, b]).stream("w", vec![vec![a, b]])
}

/// `@inline` is documented as a pure call-site expansion: "the body is inlined at
/// each call site" with the same semantics as the call. So a function's
/// observable behaviour cannot depend on whether it carries the decorator.
#[test]
fn inline_and_plain_calls_agree() {
    let body = "\
def main():
    v = StackBuf(2)
    hint_witness(v, \"w\")
    assert shift(v[0]) == v[1]
    p = GEN ** 0
    p[1] = v[0]
    p[GEN] = v[1]
    return


@INLINE
def shift(x):
    return x * GEN
";
    check_pair(&Pair {
        name: "inline_and_plain_calls_agree",
        why: "zkDSL.md §`@inline`: inlining is a call-site expansion, not a change of meaning.",
        a: &body.replace("@INLINE\n", "@inline\n"),
        b: &body.replace("@INLINE\n", ""),
        trials: vec![
            two(g(3), g(4)), // shift(g^3) = g^4
            two(g(3), g(5)), // rejected by both
            two(g(0), g(1)),
            two(g(7), g(7)),
        ],
    });
}

/// Write-once memory is the assertion mechanism, so `assert a == b` and two
/// stores of `a` and `b` into one heap cell are the same statement. `zkDSL.md`
/// §Memory: "a second write of the same value is a no-op, of a different value a
/// proof failure. This turns stores into equality assertions".
#[test]
fn assert_eq_and_double_heap_store_agree() {
    check_pair(&Pair {
        name: "assert_eq_and_double_heap_store_agree",
        why: "zkDSL.md §Memory: a store into an already-written cell IS an equality assertion.",
        a: "\
def main():
    v = StackBuf(2)
    hint_witness(v, \"w\")
    assert v[0] == v[1]
    p = GEN ** 0
    p[1] = v[0]
    p[GEN] = v[1]
    return
",
        b: "\
def main():
    v = StackBuf(2)
    hint_witness(v, \"w\")
    h = HeapBuf(1)
    h[1] = v[0]
    h[1] = v[1]
    p = GEN ** 0
    p[1] = v[0]
    p[GEN] = v[1]
    return
",
        trials: vec![
            two(g(3), g(3)),
            two(g(3), g(4)),
            two(F192::ZERO, F192::ZERO),
            two(F192::ZERO, k(1)),
        ],
    });
}

/// `zkDSL.md` §field: "`/` is runtime field division … the compiler leaves the
/// quotient cell unset and emits the checked relation `quotient · b == a`". So
/// dividing and then comparing must equal comparing the product, wherever the
/// divisor is nonzero (division by zero is documented undefined, so no trial
/// takes it there).
#[test]
fn division_and_checked_product_agree() {
    check_pair(&Pair {
        name: "division_and_checked_product_agree",
        why: "zkDSL.md §field: `a / b` emits exactly the relation `quotient · b == a`.",
        a: "\
def main():
    v = StackBuf(3)
    hint_witness(v, \"w\")
    q = v[1] / v[0]
    assert q == v[2]
    p = GEN ** 0
    p[1] = v[0]
    p[GEN] = v[2]
    return
",
        b: "\
def main():
    v = StackBuf(3)
    hint_witness(v, \"w\")
    assert v[2] * v[0] == v[1]
    p = GEN ** 0
    p[1] = v[0]
    p[GEN] = v[2]
    return
",
        trials: vec![
            three(g(3), g(8), g(5)), // g^8 / g^3 = g^5
            three(g(3), g(8), g(6)), // rejected by both
            three(k(1), g(9), g(9)),
            three(g(2), g(2), g(0)),
        ],
    });
}

fn three(a: F192, b: F192, c: F192) -> Trial {
    Trial::new([a, c]).stream("w", vec![vec![a, b, c]])
}

/// `unroll` is documented as compile-time unrolling, so a loop and its expansion
/// are the same program. A structural pair: it pins the loop machinery itself
/// rather than any one assertion, which is what catches a lowering that
/// mis-addresses one iteration.
#[test]
fn unroll_and_expansion_agree() {
    check_pair(&Pair {
        name: "unroll_and_expansion_agree",
        why: "zkDSL.md §unroll: the loop is expanded at compile time, so it IS the expansion.",
        a: "\
def main():
    v = StackBuf(1)
    hint_witness(v, \"w\")
    a = HeapBuf(4)
    a[1] = v[0]
    for i in unroll(0, 3):
        a[GEN ** (i + 1)] = a[GEN ** i] * GEN
    p = GEN ** 0
    p[1] = a[GEN ** 3]
    p[GEN] = v[0]
    return
",
        b: "\
def main():
    v = StackBuf(1)
    hint_witness(v, \"w\")
    a = HeapBuf(4)
    a[1] = v[0]
    a[GEN] = a[1] * GEN
    a[GEN ** 2] = a[GEN] * GEN
    a[GEN ** 3] = a[GEN ** 2] * GEN
    p = GEN ** 0
    p[1] = a[GEN ** 3]
    p[GEN] = v[0]
    return
",
        trials: vec![
            one(g(3), g(0)), // a[3] = g^0·g^3
            one(g(4), g(0)), // rejected by both
            one(g(8), g(5)),
            one(g(5), g(5)),
        ],
    });
}

/// A published pair whose first word is the claim and whose second is the hint.
fn one(published: F192, hint: F192) -> Trial {
    Trial::new([published, hint]).stream("w", vec![vec![hint]])
}

/// An `@inline` function returning a one-cell `StackBuf`, used in expression
/// position, must hold the value its body stored. `zkDSL.md` §`@inline` makes the
/// decorator a call-site expansion, and §StackBuf makes `s[0]` the cell the body
/// wrote, so binding the call with `let` and using it inline are the same program.
///
/// Regression test: `take_inline_ret_cell` used to hand back the raw frame cell
/// rather than following the deferred-copy alias, so the caller read a cell no
/// instruction ever wrote. The `assert` then compared that cell instead of the
/// value, which made it vacuous, and the honest runner back-solved the cell to
/// whatever the public statement demanded.
#[test]
fn inline_stackbuf_return_in_expression_position() {
    let body = "\
def main():
    v = StackBuf(2)
    hint_witness(v, \"w\")
    ASSERTION
    p = GEN ** 0
    p[1] = v[0]
    p[GEN] = v[1]
    return


@inline
def pick(x):
    s = StackBuf(1)
    s[0] = x
    return s
";
    check_pair(&Pair {
        name: "inline_stackbuf_return_in_expression_position",
        why: "zkDSL.md §`@inline` + §StackBuf: `pick(x)[0]` is the cell the body stored `x` into, \
              whether the caller binds the call or writes it inline.",
        a: &body.replace("ASSERTION", "assert pick(v[0]) != v[1]"),
        b: &body.replace("ASSERTION", "r = pick(v[0])\n    assert r[0] != v[1]"),
        trials: vec![
            two(g(3), g(5)), // distinct: accepted by both
            two(g(3), g(3)), // equal and nonzero: the inequality must fail for both
            two(k(1), k(1)),
            two(g(7), g(2)),
        ],
    });
}

/// A store into a cell something already gave a value to is the write-once
/// equality assertion of `zkDSL.md` §Memory ("a second write ... of a different
/// value a proof failure. This turns stores into equality assertions"), whether
/// the cell is a `StackBuf` cell or a `HeapBuf` cell.
///
/// Regression test: `stack_store` deferred a copy-or-constant RHS as an alias
/// unconditionally, so a `StackBuf` store never pinned a hint. `hint_witness`
/// named the raw cells while every read forwarded past them, and the check the
/// author wrote was applied to nothing.
#[test]
fn stack_store_pins_a_hint_like_a_heap_store() {
    check_pair(&Pair {
        name: "stack_store_pins_a_hint_like_a_heap_store",
        why: "zkDSL.md §Memory: a store into an already-written cell IS an equality assertion, \
              and §Hints: `s[k] = <checked value>` is how a program pins prover advice.",
        a: "\
def main():
    s = StackBuf(2)
    hint_witness(s, \"w\")
    s[0] = GEN ** 3
    p = GEN ** 0
    p[1] = s[0]
    p[GEN] = s[1]
    return
",
        b: "\
def main():
    s = StackBuf(2)
    hint_witness(s, \"w\")
    h = HeapBuf(1)
    h[1] = s[0]
    h[1] = GEN ** 3
    p = GEN ** 0
    p[1] = s[0]
    p[GEN] = s[1]
    return
",
        trials: vec![
            pinned(g(3), g(9)), // the hint agrees with the pin
            pinned(g(4), g(9)), // it does not: both must reject
            pinned(F192::ZERO, g(1)),
            pinned(g(2), g(3)),
        ],
    });
}

/// A trial for the pinning pair above: the public input carries the PIN, not the
/// hint. Publishing the hint would hide a dropped pin, since the publication then
/// forwards through the very alias that dropped it and both spellings agree by
/// accident. Publishing the pin makes a dropped pin visible as a program that
/// accepts every hint.
fn pinned(hint0: F192, hint1: F192) -> Trial {
    Trial::new([g(3), hint1]).stream("w", vec![vec![hint0, hint1]])
}

/// `zkDSL.md` §SHA3: "If `out` was already written, the statement *asserts*
/// the digest equals it, write-once turning the hash into a verification, which
/// is exactly what a signature verifier wants." That has to hold for a `StackBuf`
/// `out` as much as for a `HeapBuf` one, since the doc recommends the idiom
/// without qualifying which.
///
/// Regression test: the hash output arm named the raw run, so a `StackBuf`
/// `out` whose cells had been pre-written by copies or constants had its digest
/// written where nothing read it. The "verification" checked nothing, and the
/// prover could put any message under the hash.
#[test]
fn prewritten_sha3_out_asserts_the_digest() {
    check_pair(&Pair {
        name: "prewritten_sha3_out_asserts_the_digest",
        why: "zkDSL.md §SHA3: a pre-written `out` turns the hash into a verification.",
        a: "\
def main():
    v = StackBuf(2)
    hint_witness(v, \"w\")
    m = StackBuf(4)
    m[0] = 5
    m[1] = 7
    m[2] = 0
    m[3] = 0
    d = StackBuf(2)
    d[0] = v[0]
    d[1] = v[1]
    sha3(m[0:2], m[2:4], d)
    p = GEN ** 0
    p[1] = v[0]
    p[GEN] = v[1]
    return
",
        b: "\
def main():
    v = StackBuf(2)
    hint_witness(v, \"w\")
    m = StackBuf(4)
    m[0] = 5
    m[1] = 7
    m[2] = 0
    m[3] = 0
    d = HeapBuf(2)
    d[1] = v[0]
    d[GEN] = v[1]
    sha3(m[0:2], m[2:4], d[0:2])
    p = GEN ** 0
    p[1] = v[0]
    p[GEN] = v[1]
    return
",
        trials: vec![
            // The real digest of the block whose cells are (5, 7, 0, 0).
            two(super::cases::DIGEST_5_7[0], super::cases::DIGEST_5_7[1]),
            // Anything else must be rejected by both spellings.
            two(F192::ZERO, F192::ZERO),
            two(super::cases::DIGEST_5_7[0], F192::ZERO),
            two(g(3), g(5)),
        ],
    });
}

/// `zkDSL.md` §BLAKE2s: "If `out` was already written, the statement *asserts*
/// the digest equals it, write-once turning the hash into a verification, which
/// is exactly what a signature verifier wants." That has to hold for a `StackBuf`
/// `out` as much as for a `HeapBuf` one, since the doc recommends the idiom
/// without qualifying which.
///
/// Regression test: the `BLAKE2s` output arm named the raw run, so a `StackBuf`
/// `out` whose cells had been pre-written by copies or constants had its digest
/// written where nothing read it. The "verification" checked nothing, and the
/// prover could put any message under the hash.
#[test]
fn prewritten_blake2s_out_asserts_the_digest() {
    check_pair(&Pair {
        name: "prewritten_blake2s_out_asserts_the_digest",
        why: "zkDSL.md §BLAKE2s: a pre-written `out` turns the hash into a verification.",
        a: "\
def main():
    v = StackBuf(2)
    hint_witness(v, \"w\")
    m = StackBuf(4)
    m[0] = 5
    m[1] = 7
    m[2] = 0
    m[3] = 0
    d = StackBuf(2)
    d[0] = v[0]
    d[1] = v[1]
    blake2s(m[0:2], m[2:4], d)
    p = GEN ** 0
    p[1] = v[0]
    p[GEN] = v[1]
    return
",
        b: "\
def main():
    v = StackBuf(2)
    hint_witness(v, \"w\")
    m = StackBuf(4)
    m[0] = 5
    m[1] = 7
    m[2] = 0
    m[3] = 0
    d = HeapBuf(2)
    d[1] = v[0]
    d[GEN] = v[1]
    blake2s(m[0:2], m[2:4], d[0:2])
    p = GEN ** 0
    p[1] = v[0]
    p[GEN] = v[1]
    return
",
        trials: vec![
            // The real digest of the block whose cells are (5, 7, 0, 0).
            two(super::cases::BLAKE2S_DIGEST_5_7[0], super::cases::BLAKE2S_DIGEST_5_7[1]),
            // Anything else must be rejected by both spellings.
            two(F192::ZERO, F192::ZERO),
            two(super::cases::BLAKE2S_DIGEST_5_7[0], F192::ZERO),
            two(g(3), g(5)),
        ],
    });
}

/// Two stores of different values into one cell is the write-once equality
/// assertion of `zkDSL.md` §Memory, on a `StackBuf` cell as much as on a `HeapBuf`
/// cell. The doc draws no distinction, and the whole "stores are assertions"
/// promise rests on there being none.
#[test]
fn two_stack_stores_to_one_cell_assert_equality() {
    check_pair(&Pair {
        name: "two_stack_stores_to_one_cell_assert_equality",
        why: "zkDSL.md §Memory: a second write of a different value is a proof failure.",
        a: "\
def main():
    v = StackBuf(2)
    hint_witness(v, \"w\")
    s = StackBuf(1)
    s[0] = v[0]
    s[0] = v[1]
    p = GEN ** 0
    p[1] = v[0]
    p[GEN] = v[1]
    return
",
        b: "\
def main():
    v = StackBuf(2)
    hint_witness(v, \"w\")
    h = HeapBuf(1)
    h[1] = v[0]
    h[1] = v[1]
    p = GEN ** 0
    p[1] = v[0]
    p[GEN] = v[1]
    return
",
        trials: vec![two(g(3), g(3)), two(g(3), g(4)), two(g(0), g(0)), two(g(5), g(9))],
    });
}

/// A store made inside a runtime branch into a cell that already carried a value
/// from before the branch is the same assertion whether the cell is a `StackBuf`
/// cell or a `HeapBuf` cell. `zkDSL.md` §`if`: "branches communicate through
/// write-once cells: only one branch executes, so both may write the *same* cell",
/// and §Memory makes a second write of a different value a failure.
///
/// Regression test: `scoped` materialized the branch's value into the cell and
/// then restored the pre-branch alias over it, so post-join reads forwarded to the
/// pre-branch source on every path and the materialized write was orphaned. The
/// published value was the pre-branch one whichever arm ran.
#[test]
fn store_inside_a_branch_asserts_against_the_pre_branch_value() {
    check_pair(&Pair {
        name: "store_inside_a_branch_asserts_against_the_pre_branch_value",
        why: "zkDSL.md §`if` + §Memory: both arms may write one cell, and a second write \
              of a different value is a proof failure.",
        a: "\
def main():
    v = StackBuf(3)
    hint_witness(v, \"w\")
    s = StackBuf(1)
    s[0] = v[0]
    if v[1] == v[2]:
        s[0] = v[1]
    else:
        s[0] = v[2]
    p = GEN ** 0
    p[1] = s[0]
    p[GEN] = v[0]
    return
",
        b: "\
def main():
    v = StackBuf(3)
    hint_witness(v, \"w\")
    h = HeapBuf(1)
    h[1] = v[0]
    if v[1] == v[2]:
        h[1] = v[1]
    else:
        h[1] = v[2]
    p = GEN ** 0
    p[1] = h[1]
    p[GEN] = v[0]
    return
",
        trials: vec![
            // else arm, and v[0] != v[2]: the assertion must fail for both.
            branch3(g(1), g(2), g(3)),
            // else arm, and v[0] == v[2]: accepted by both.
            branch3(g(1), g(2), g(1)),
            // then arm, and v[0] == v[1]: accepted by both.
            branch3(g(1), g(1), g(1)),
            // then arm, and v[0] != v[1] (v[1] == v[2] picks it): must fail.
            branch3(g(1), g(4), g(4)),
        ],
    });
}

/// A trial for the branch pair: publishes `s[0]` and `v[0]`, which the assertion
/// makes equal on every accepting path.
fn branch3(a: F192, b: F192, c: F192) -> Trial {
    Trial::new([a, a]).stream("w", vec![vec![a, b, c]])
}

/// A multi-value target may be a `StackBuf` element, and `zkDSL.md` §match
/// says the arms then write straight into it. That is only a saved copy, so it
/// must accept exactly what the name-plus-store spelling accepts. The bug this
/// guards is the arms writing PAST the buffer: the target cell is the callee's
/// return slot now, so an unchecked index puts a return into the next buffer,
/// which is the shape `copy_alias` had before its bounds check was added.
#[test]
fn a_stackbuf_target_and_a_name_plus_store_agree() {
    let body = "\
def pick(x, i: Const):
    return x * GEN ** i, GEN ** i

def main():
    v = StackBuf(2)
    hint_witness(v, \"w\")
    sb = StackBuf(2)
    sb[1] = 0
    TARGET
    p = GEN ** 0
    p[1] = sb[0]
    p[GEN] = e
    return
";
    check_pair(&Pair {
        name: "a_stackbuf_target_and_a_name_plus_store_agree",
        why: "zkDSL.md §match: a target may be a name or a StackBuf element; the element form \
              only saves the copy.",
        a: &body.replace(
            "TARGET",
            "sb[0], e = match(log(v[0]), range(0, 2), lambda i: pick(v[1], i))",
        ),
        b: &body.replace(
            "TARGET",
            "t, e = match(log(v[0]), range(0, 2), lambda i: pick(v[1], i))\n    sb[0] = t",
        ),
        trials: vec![
            Trial::new([g(4), g(0)]).stream("w", vec![vec![g(0), g(4)]]),
            Trial::new([g(5), g(1)]).stream("w", vec![vec![g(1), g(4)]]),
            Trial::new([g(4), g(1)]).stream("w", vec![vec![g(1), g(4)]]),
            Trial::new([g(9), g(0)]).stream("w", vec![vec![g(0), g(4)]]),
        ],
    });
}
