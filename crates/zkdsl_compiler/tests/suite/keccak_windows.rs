//! `KECCAK` blocks no layout puts in one window: a `StackBuf` parameter at a fixed offset, a frame an `addr()` fixes,
//! overlapping slices of one buffer. The compiler copies such a block to a fresh run (an output back after the
//! instruction), and each program checks the hash against one computed from a freely laid out block.

use crate::common::compile;
use lean_vm_core::cpu::{Fault, execute};
use primitives::field::F128;
use zkdsl_compiler::parse;

fn run(src: &str) -> Result<(), Fault> {
    let program = compile(&parse(src).expect("parse"));
    execute(&program, &[], [F128::ZERO; 2]).map(|_| ()).map_err(|e| e.fault)
}

/// `tail=` and `state=` read from parameters after `k` cells of others, at every offset modulo the window.
#[test]
fn parameter_inputs() {
    for k in 1..=16 {
        let src = format!(
            "\
def h(p: StackBuf({k}), t: StackBuf(4), st: StackBuf(13)):
    a = StackBuf(2)
    keccak([p[0], p[0]], [p[0], p[0]], a, tail=t)
    b = StackBuf(2)
    keccak_cells([p[0]], b, state=st)
    return a[0] + b[1]

def main():
    p = StackBuf({k})
    for i in unroll(0, {k}):
        p[i] = const(i + 1)
    t = StackBuf(4)
    for i in unroll(0, 4):
        t[i] = const(i + 7)
    st = StackBuf(13)
    keccak([1, 2], [3, 4], st)
    a = StackBuf(2)
    keccak([p[0], p[0]], [p[0], p[0]], a, tail=t)
    b = StackBuf(2)
    keccak_cells([p[0]], b, state=st)
    x = h(p, t, st)
    assert x == a[0] + b[1]
    return
"
        );
        assert_eq!(run(&src), Ok(()), "k = {k}");
    }
}

/// Outputs into parameters after `k` cells of others, a digest and a whole state: the hashes check the caller's
/// cells, and a wrong cell in either fails.
#[test]
fn parameter_outputs() {
    for k in 1..=16 {
        for wrong in ["", "d", "s"] {
            let fill = |name: &str, n: usize| {
                if name == wrong {
                    format!("    for i in unroll(0, {n}):\n        {name}[i] = 0\n")
                } else {
                    format!("    keccak([5, 6], [7, 8], {name})\n")
                }
            };
            let src = format!(
                "\
def check(p: StackBuf({k}), d: StackBuf(2), s: StackBuf(13)):
    keccak([p[0], 6], [7, 8], d)
    keccak([p[0], 6], [7, 8], s)
    return

def main():
    p = StackBuf({k})
    for i in unroll(0, {k}):
        p[i] = 5
    d = StackBuf(2)
{}    s = StackBuf(13)
{}    check(p, d, s)
    return
",
                fill("d", 2),
                fill("s", 13),
            );
            let result = run(&src);
            if wrong.is_empty() {
                assert_eq!(result, Ok(()), "k = {k}");
            } else {
                assert!(
                    matches!(result, Err(Fault::Conflict { .. })),
                    "k = {k}, {wrong}: {result:?}"
                );
            }
        }
    }
}

/// A frame an `addr()` fixes, with a tail and a state output after `n` cells, at every offset modulo the window.
#[test]
fn fixed_frame() {
    for n in 1..=17 {
        let src = format!(
            "\
def fixed(x):
    pad = StackBuf({n})
    for k in unroll(0, {n}):
        pad[k] = x
    a = StackBuf(4)
    for k in unroll(0, 4):
        a[k] = x
    q = addr(pad)
    assert q[1] == x
    h = StackBuf(13)
    keccak([x, x], [x, x], h, tail=a)
    return h[0] + h[12]

def free(x):
    a = StackBuf(4)
    for k in unroll(0, 4):
        a[k] = x
    h = StackBuf(13)
    keccak([x, x], [x, x], h, tail=a)
    return h[0] + h[12]

def main():
    y = fixed(5)
    assert y == free(5)
    return
"
        );
        assert_eq!(run(&src), Ok(()), "n = {n}");
    }
}

/// A frame an `addr()` fixes, with several blocks to copy after `n` cells (tails, a state, two- and thirteen-cell
/// outputs), at every offset modulo the window. The fresh runs are each laid out in a window, so one copy puts every
/// block in one: the compiler asserts it, panicking on a block still across a window after the copy.
#[test]
fn fixed_frame_with_several_blocks() {
    let body = "    a = StackBuf(4)
    for k in unroll(0, 4):
        a[k] = x
    h = StackBuf(13)
    keccak([x, x], [x, x], h, tail=a)
    d = StackBuf(2)
    keccak([h[0], x], [x, h[1]], d, tail=a)
    e = StackBuf(13)
    keccak_cells([d[0]], e, state=h)
    f = StackBuf(2)
    keccak([e[0], e[1]], [d[1], x], f, tail=a)
    return e[0] + e[12] + f[1]
";
    for n in 1..=17 {
        let src = format!(
            "\
def fixed(x):
    pad = StackBuf({n})
    for k in unroll(0, {n}):
        pad[k] = x
    q = addr(pad)
    assert q[1] == x
{body}
def free(x):
{body}
def main():
    y = fixed(5)
    assert y == free(5)
    return
"
        );
        assert_eq!(run(&src), Ok(()), "n = {n}");
    }
}

/// Tails sliding one cell at a time over one buffer: no offset puts them all in windows.
#[test]
fn sliding_tails() {
    let mut src = String::from(
        "\
def free(a, b, c, d):
    t = StackBuf(4)
    t[0] = a
    t[1] = b
    t[2] = c
    t[3] = d
    h = StackBuf(2)
    keccak([1, 2], [3, 4], h, tail=t)
    return h[0]

def main():
    m = StackBuf(17)
    for i in unroll(0, 17):
        m[i] = const(i + 1)
",
    );
    for i in 0..14 {
        src += &format!(
            "    h{i} = StackBuf(2)\n    keccak([1, 2], [3, 4], h{i}, tail=m[{i}:{i} + 4])\n    \
             assert h{i}[0] == free(m[{i}], m[{i} + 1], m[{i} + 2], m[{i} + 3])\n"
        );
    }
    src += "    return\n";
    assert_eq!(run(&src), Ok(()));
}
