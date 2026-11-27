//! `Program::to_bytes` and `from_bytes` on every program in `tests/programs/`: the decoded program encodes to the same
//! bytes, so every field survives, and has the same stacked bytecode; a cut encoding is refused.

use crate::common::compile;
use isa::Program;
use std::fs;
use zkdsl_compiler::parse;

#[test]
fn every_program_survives_its_bytes() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    for entry in fs::read_dir(dir).expect("tests/programs") {
        let path = entry.expect("dir entry").path();
        if path.extension().is_none_or(|x| x != "py") {
            continue;
        }
        let name = path.display();
        let program = compile(&parse(&fs::read_to_string(&path).expect("read")).expect("parse"));
        let bytes = program.to_bytes();
        let decoded = Program::from_bytes(&bytes).expect("decodes");
        assert!(decoded.to_bytes() == bytes, "{name}");
        assert!(decoded.stacked_bytecode() == program.stacked_bytecode(), "{name}");
        assert!(Program::from_bytes(&bytes[..bytes.len() - 1]).is_none(), "{name}");
    }
}
