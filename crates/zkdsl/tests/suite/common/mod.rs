//! Helpers shared by the integration tests, reached as `crate::common::…`.

use zkdsl::parse;

/// `tests/compiled/<name>.txt`: a program as the Lean back end compiled it (`lake exe guest-backend export programs`).
pub fn compiled(name: &str) -> isa::Program {
    let path = format!("{}/tests/compiled/{name}.txt", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    isa::Program::__from_text(&text).unwrap_or_else(|e| panic!("{path}: {e}"))
}

/// The core IR the front end expands `src` to, as `scripts/frontend-diff` prints it.
pub fn core(src: &str) -> String {
    zkdsl::core_ir::render(&zkdsl::expand(&parse(src).expect("parse")))
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
