//! Helpers shared by the integration tests, reached as `crate::common::…`.
#![allow(dead_code)]

use lean_compiler::parse;
use primitives::field::F128;

/// The shared compiler's output, assembled for the stable prover.
pub fn compile(ast: &lean_compiler::Ast) -> leanvm_core::cpu::Program {
    lean_compiler::compile(ast).into()
}

/// [`lean_compiler::f128_literal`] of a prover word.
pub fn f128_literal(x: F128) -> String {
    lean_compiler::f128_literal(leanvm_core::cpu::to_scalar(&x))
}

/// [`lean_compiler::parse_const`], as a prover word.
pub fn parse_const(s: &str) -> Result<F128, String> {
    lean_compiler::parse_const(s).map(leanvm_core::cpu::from_scalar)
}

/// The program's own instruction mix: executed but not proven.
pub fn mix(src: &str, pi: [F128; 2]) -> [usize; leanvm_core::cpu::Stats::TABLES.len()] {
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
