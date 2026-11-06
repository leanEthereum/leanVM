//! Helpers shared by the integration tests, reached as `crate::common::…`.
#![allow(dead_code)]

use lean_compiler::{compile, parse};
use primitives::field::F192;

/// The program's own instruction mix: executed but not proven.
pub fn mix(src: &str, pi: [F192; 2]) -> [usize; leanvm_core::cpu::Stats::TABLES.len()] {
    compile(&parse(src).expect("parse")).execute(pi).unwrap().rows()
}

/// An AST's shape with source lines stripped. Two spellings of the same program
/// (a constant against its substituted value, a placeholder against the filled
/// text) are the same program but rarely occupy the same lines, so comparing
/// them by `Debug` has to ignore that field.
pub fn without_lines(ast: &lean_compiler::Ast) -> String {
    let d = format!("{ast:?}");
    let (mut out, mut rest) = (String::with_capacity(d.len()), d.as_str());
    while let Some(i) = rest.find("line: ") {
        out.push_str(&rest[..i]);
        let after = &rest[i + "line: ".len()..];
        rest = &after[after.find(", ").expect("`line` is followed by another field") + 2..];
    }
    out.push_str(rest);
    out
}
