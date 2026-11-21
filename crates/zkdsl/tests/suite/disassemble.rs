//! `disassemble` must render every one of the six opcodes without panicking,
//! so it stays usable for the `DBG_DISASM` workflow (a failed guest `assert`
//! surfaces as a write-once conflict, and the pc is all you get).

use isa::Program;
use zkdsl::disassemble;

/// Every Lean-compiled program in `tests/compiled`, one line per instruction, and the six opcodes among them.
#[test]
fn disassemble_covers_every_opcode() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/compiled");
    let mut text = String::new();
    for entry in std::fs::read_dir(dir).expect("tests/compiled") {
        let path = entry.expect("dir entry").path();
        let program = Program::__from_text(&std::fs::read_to_string(&path).unwrap())
            .unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        let listing = disassemble(&program.prog);
        assert_eq!(listing.lines().count(), program.prog.len(), "{}", path.display());
        text += &listing;
    }
    for mnemonic in ["SET", "XOR", "MUL", "DEREF", "JUMP", "KECCAK"] {
        assert!(text.contains(mnemonic), "disassembly is missing {mnemonic}");
    }
}
