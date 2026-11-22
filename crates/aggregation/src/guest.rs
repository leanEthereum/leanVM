//! Compiling the guest to a fixed point on its own size, and what every prover and verifier derives from it once.

use super::placeholders::placeholder_map;
use fiat_shamir_prover::merkle::hash_to_scalars;
use isa::{CompiledProgram, Program};
use primitives::field::F128;
use std::sync::OnceLock;
use zkdsl_compiler::{compile, parse_with_constants};

/// The aggregation guest's zkDSL source.
pub(super) const GUEST_SOURCE: &str =
    include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../guests/lean_ethereum.py"));

/// The aggregation bytecode, compiled to a fixed point on its own size: the one fixed program every node proves, and
/// whose stacked bytecode every node's bytecode claims are about.
///
/// The recursion placeholders are a function of the inner bytecode's log size,
/// and here the inner bytecode is this one, so the size has to agree with
/// itself. The guess converges in one or two rounds because the map's only
/// size-dependent part is a handful of unrolled sumcheck rounds.
pub fn unified_guest() -> &'static Program {
    &guest().0
}

/// The unified guest, with its global scalar constants as the compiler substitutes them.
fn guest() -> &'static (Program, Vec<(String, String)>) {
    static GUEST: OnceLock<(Program, Vec<(String, String)>)> = OnceLock::new();
    GUEST.get_or_init(|| {
        // A guess at the guest's own size: right, it compiles once; wrong, one more round.
        let mut guess = 19;
        for _ in 0..8 {
            let (guest, constants) = compile_guest(guess);
            let actual = guest.prog.len().trailing_zeros() as usize;
            if actual == guess {
                return (Program::from(guest), constants);
            }
            guess = actual;
        }
        panic!("the aggregation bytecode's self-referential compile did not converge");
    })
}

/// The guest's Fiat-Shamir IV as the two words a statement carries it in.
pub(super) fn fs_seed() -> [F128; 2] {
    hash_to_scalars(&unified_guest().bytecode().fiat_shamir_iv())
}

/// A global constant of the guest, at its deployed size, as the compiler substitutes it: what the host reads
/// rather than restates.
pub(super) fn guest_constant(name: &str) -> usize {
    let (_, value) = (guest().1.iter().find(|(n, _)| n == name)).unwrap_or_else(|| panic!("no guest constant {name}"));
    value
        .parse()
        .unwrap_or_else(|_| panic!("the guest constant {name} is no count"))
}

/// The guest compiled for an inner bytecode of `2^kbc` slots, and its global scalar constants.
pub(super) fn compile_guest(kbc: usize) -> (CompiledProgram, Vec<(String, String)>) {
    let replacements = placeholder_map(kbc);
    // `DBG_PLACEHOLDERS=path`: dump the baked guest constants, to read alongside
    // a `DBG_PROF_DUMP` profile (the guest's shape is entirely in these).
    if let Ok(path) = std::env::var("DBG_PLACEHOLDERS") {
        let dump: String = replacements.iter().map(|(k, v)| format!("{k} = {v}\n")).collect();
        std::fs::write(&path, dump).expect("write DBG_PLACEHOLDERS");
    }
    let (ast, constants) =
        parse_with_constants(GUEST_SOURCE, &replacements).expect("the repository aggregation guest must parse");
    let guest = compile(&ast);
    // `DBG_DISASM=path`: dump the guest's disassembly, to read alongside a
    // `DBG_PROF_DUMP` per-pc profile. Function boundaries lead the dump, so the
    // pc a failed guest check reports can be resolved to a source function
    // without re-deriving the layout by hand.
    if let Ok(path) = std::env::var("DBG_DISASM") {
        let mut ranges: Vec<_> = guest.fn_ranges.iter().collect();
        ranges.sort_by_key(|(_, entry, _)| *entry);
        let mut dump = String::new();
        for (name, entry, len) in ranges {
            dump += &format!("# fn {entry:>7}..{:<7} {name}\n", entry + len);
        }
        dump += &zkdsl_compiler::disassemble(&guest.prog);
        std::fs::write(&path, dump).expect("write DBG_DISASM");
    }
    (guest, constants)
}
