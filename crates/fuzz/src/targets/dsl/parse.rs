//! `dsl-parse`: raw bytes and grammar-shaped garbage into `parse` and `parse_const`, which return `Result` and so
//! must never panic, hang or overflow the stack (a stack overflow kills the worker, which the supervisor records).

use crate::{Ctx, Finding, Outcome, Source, catch};
use lean_compiler::{parse, parse_const, parse_with_replacements};
use std::collections::BTreeMap;

const ATOMS: &[&str] = &[
    "x",
    "y",
    "GEN",
    "0",
    "1",
    "5",
    "340282366920938463463374607431768211455",
    "340282366920938463463374607431768211456",
    "18446744073709551616",
    "99999999999999999999999999999999999999999999",
    "f192(1, 2, 3)",
    "f192(18446744073709551616, 0, 0)",
    "const(3 - 5)",
    "const(1 // 0)",
    "const(2 ** 200)",
    "len(T)",
    "T[0]",
    "T[99]",
    "sb[0]",
    "hb[GEN]",
    "hb[x:x + 2]",
    "sb[1:0]",
    "hint_witness(\"s\")",
    "log(x)",
    "addr(sb)",
    "f(x)",
    "main()",
    "StackBuf(4294967296)",
    "HeapBuf(0)",
    "[x, y]",
    "[]",
    "[x for k in unroll(0, 3)]",
    "match(log(x), range(0, 2), lambda j: j)",
    "\"str\"",
    "'q'",
    "é",
    "\u{0}",
    "∑",
    "x.y",
    "-1",
    "+",
    "**",
    "()",
];
const OPS: &[&str] = &[
    " + ", " * ", " / ", " // ", " % ", " - ", " ** ", " == ", " != ", " < ", ", ", ":", " = ", ".",
];
const HEADS: &[&str] = &[
    "x = ",
    "assert ",
    "assert log(",
    "return ",
    "if ",
    "elif ",
    "else:",
    "for i in mul_range(1, ",
    "for i in unroll(0, ",
    "keccak(",
    "keccak_cells(",
    "hint_witness(",
    "print(",
    "match(",
    "a, b = ",
    "sb[0] = ",
    "hb[1] = ",
    "@inline",
    "def f(",
    "def main(",
    "x += ",
    "x //= ",
    "while x:",
    "import os",
    "from snark_lib import *",
    "N = ",
    "T = [",
    "lambda j: ",
    "pass",
    "assert_in_k(",
];

pub fn run(src: &mut Source, _ctx: &Ctx) -> Outcome {
    let text = match src.below(8) {
        0 => {
            let n = src.size(512);
            String::from_utf8_lossy(&src.bytes(n)).into_owned()
        }
        1 => nesting(src),
        2 => tower(src),
        _ => shaped(src),
    };
    _ctx.note(format!(
        "shape {}",
        text.len().min(1 << 20).next_power_of_two().trailing_zeros()
    ));
    check(&text)
}

/// Parse `text` every way the front end offers; a panic is the finding.
pub fn check(text: &str) -> Outcome {
    let trimmed: String = text.chars().take(4096).collect();
    if let Err((message, location)) = catch(|| parse(text).map(drop)) {
        return Err(Finding::panic(&message, &location).in_context("dsl-parse: parse"));
    }
    if let Err((message, location)) = catch(|| parse_const(&trimmed).map(drop)) {
        return Err(Finding::panic(&message, &location).in_context("dsl-parse: parse_const"));
    }
    // A placeholder filled with the text itself, where the substitution allows it.
    let mut map = BTreeMap::new();
    map.insert("PH".to_string(), trimmed.lines().next().unwrap_or("").to_string());
    let host = "X = PH\n\ndef main():\n    y = PH\n    return\n";
    if let Err((message, location)) = catch(|| parse_with_replacements(host, &map).map(drop)) {
        return Err(Finding::panic(&message, &location).in_context("dsl-parse: placeholder"));
    }
    Ok(())
}

fn expr(src: &mut Source, depth: usize) -> String {
    if depth == 0 || src.chance(1, 3) {
        return src.pick(ATOMS).to_string();
    }
    match src.below(5) {
        0 => format!("({})", expr(src, depth - 1)),
        1 => format!(
            "{}({})",
            src.pick(&["f", "log", "const", "GEN", "HeapBuf", "len", "f192"]),
            expr(src, depth - 1)
        ),
        2 => format!("[{}]", expr(src, depth - 1)),
        _ => format!("{}{}{}", expr(src, depth - 1), src.pick(OPS), expr(src, depth - 1)),
    }
}

/// Lines of statement heads and expressions, at drifting indentation, with the odd unbalanced bracket.
fn shaped(src: &mut Source) -> String {
    let mut out = String::new();
    if src.bool() {
        out.push_str("def main():\n");
    }
    for _ in 0..src.size(40) {
        let indent = match src.below(6) {
            0 => "\t".to_string(),
            1 => " ".repeat(src.below(9)),
            2 => " \t ".to_string(),
            _ => "    ".repeat(src.range(1, 3)),
        };
        let mut line = format!("{indent}{}{}", src.pick(HEADS), expr(src, 4));
        match src.below(8) {
            0 => line.push(':'),
            1 => line.push(')'),
            2 => line.push_str(" # c \" ]"),
            3 => {
                let at = src.below(line.len() + 1);
                if line.is_char_boundary(at) {
                    line.insert(at, *src.pick(&['(', ')', '[', ']', '"', '#', '\0', '\r', ':', '=']));
                }
            }
            _ => {}
        }
        out.push_str(&line);
        out.push(if src.chance(1, 20) { '\r' } else { '\n' });
    }
    if src.chance(1, 4) {
        out.push_str(&"x".repeat(src.size(1 << 16)));
    }
    out
}

/// Deep nesting of one bracket kind, usually inside a statement.
fn nesting(src: &mut Source) -> String {
    let depth = match src.below(8) {
        0 => src.range(1000, 20000),
        _ => src.size(300),
    };
    let (open, close) = *src.pick(&[("(", ")"), ("[", "]"), ("f(", ")"), ("log(", ")"), ("const(", ")")]);
    let balanced = src.chance(3, 4);
    let mut e = open.repeat(depth);
    e.push('x');
    e.push_str(&close.repeat(if balanced { depth } else { depth.saturating_sub(1) }));
    match src.below(4) {
        0 => e,
        1 => format!("def main():\n    assert {e} == 1\n    return\n"),
        2 => format!("N = {e}\n\ndef main():\n    return\n"),
        _ => format!("def main():\n    y = {e}\n    return\n"),
    }
}

/// `**` towers and long operator chains.
fn tower(src: &mut Source) -> String {
    let n = match src.below(6) {
        0 => src.range(500, 5000),
        _ => src.size(64),
    };
    let op = *src.pick(&[" ** ", " + ", " * ", " // ", " - ", " % "]);
    let atom = *src.pick(&["2", "GEN", "x", "340282366920938463463374607431768211455", "0"]);
    let e = vec![atom; n.max(1)].join(op);
    match src.below(3) {
        0 => e,
        1 => format!("N = {e}\n\ndef main():\n    return\n"),
        _ => format!("def main():\n    x = GEN\n    y = {e}\n    return\n"),
    }
}
