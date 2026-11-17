//! Helpers shared by the integration tests, reached as `crate::common::…`.

use primitives::field::F128;
use zkdsl::parse;

/// `ast` compiled into the `isa::Program` the provers take.
pub fn compile(ast: &zkdsl::Ast) -> isa::Program {
    zkdsl::compile(ast).into()
}

/// [`zkdsl::f128_literal`] of a prover word.
pub fn f128_literal(x: F128) -> String {
    zkdsl::f128_literal(lean_vm_core::cpu::to_scalar(&x))
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
pub fn without_lines(ast: &zkdsl::Ast) -> String {
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
