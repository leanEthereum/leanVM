//! Helpers shared by the integration tests, reached as `crate::common::…`.

use primitives::field::F128;
use zkdsl_compiler::parse;

/// `ast` compiled into the `isa::Program` the provers take.
pub fn compile(ast: &zkdsl_compiler::Ast) -> isa::Program {
    zkdsl_compiler::compile(ast).into()
}

/// [`zkdsl_compiler::f128_literal`] of a prover word.
pub fn f128_literal(x: F128) -> String {
    zkdsl_compiler::f128_literal(lean_vm_core::cpu::to_scalar(&x))
}

/// The program's own instruction mix: executed but not proven.
pub fn mix(src: &str, pi: [F128; 2]) -> [usize; lean_vm_core::cpu::Stats::TABLES.len()] {
    lean_vm_core::cpu::execute(&compile(&parse(src).expect("parse")), &[], pi)
        .unwrap()
        .rows()
}

/// An AST's shape with source lines stripped. Two spellings of the same program
/// (a constant against its substituted value, a placeholder against the filled
/// text) are the same program but rarely occupy the same lines, so comparing
/// them by `Debug` has to ignore that field.
pub fn without_lines(ast: &zkdsl_compiler::Ast) -> String {
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
