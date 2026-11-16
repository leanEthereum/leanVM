//! The guest's bytecode as the Lean back end compiled it, checked against what it was compiled from, and what every
//! prover and verifier derives from it once.

use super::placeholders::placeholder_map;
use fiat_shamir_prover::merkle::hash_to_scalars;
use isa::Program;
use keccak256::{hash, hash_pair};
use primitives::field::F128;
use std::collections::BTreeMap;
use std::fmt::Write;
use std::sync::LazyLock;

/// The aggregation guest's zkDSL source.
pub(super) const GUEST_SOURCE: &str = include_str!("../../../guests/lean_ethereum.py");

/// The guest compiled by the back end written in Lean (`formal/lean_vm/LeanVM/Guest/Backend`), at the fixed point on
/// its own size: an `input` line (the [`input_digest`] it was compiled from), an `iv` line (its Fiat-Shamir IV), then
/// the program in `isa`'s line format, source lines included, which a failure report names.
/// `formal/lean_vm/scripts/guest-artifact` writes it.
pub(super) const ARTIFACT: &str = include_str!("../../../guests/lean_ethereum.compiled");

/// The aggregation bytecode: the one fixed program every node proves, and whose stacked bytecode every node's
/// bytecode claims are about.
///
/// The recursion placeholders are a function of the inner bytecode's log size, and here the inner bytecode is this
/// one, so the guest is compiled at the size it has: the artefact's `input` line is the digest of the source and the
/// placeholders at its own size.
///
/// # Panics
///
/// If the artefact is stale: the guest's source or its placeholders changed since it was written.
pub fn unified_guest() -> &'static Program {
    static GUEST: LazyLock<Program> =
        LazyLock::new(|| load(ARTIFACT).unwrap_or_else(|e| panic!("guests/lean_ethereum.compiled: {e}")));
    &GUEST
}

/// The guest's Fiat-Shamir IV as the two words a statement carries it in.
pub(super) fn fs_seed() -> [F128; 2] {
    hash_to_scalars(&unified_guest().bytecode().fiat_shamir_iv())
}

/// What the guest is compiled from under `replacements` (`placeholder_map` at some size): Keccak-256 of its source's
/// digest and its placeholders'.
pub(super) fn input_digest(replacements: &BTreeMap<String, String>) -> [u8; 32] {
    hash_pair(
        &hash(GUEST_SOURCE.as_bytes()),
        &hash(placeholder_lines(replacements).as_bytes()),
    )
}

/// The placeholders, a line `NAME = value` each.
fn placeholder_lines(replacements: &BTreeMap<String, String>) -> String {
    replacements.iter().map(|(k, v)| format!("{k} = {v}\n")).collect()
}

pub(super) fn hex(bytes: &[u8]) -> String {
    bytes.iter().fold(String::new(), |mut s, b| {
        write!(s, "{b:02x}").unwrap();
        s
    })
}

/// The program an artefact describes, once its `input` line is the guest's at the program's size and its `iv` line
/// is its bytecode's.
pub(super) fn load(text: &str) -> Result<Program, String> {
    let mut lines = text.splitn(3, '\n');
    let mut header = |tag: &str| {
        lines
            .next()
            .and_then(|line| line.strip_prefix(tag)?.strip_prefix(' '))
            .map(str::to_string)
            .ok_or_else(|| format!("no `{tag}` line"))
    };
    let (input, iv) = (header("input")?, header("iv")?);
    let program = Program::__from_text(lines.next().unwrap_or(""))?;
    let kbc = program.prog.len().trailing_zeros() as usize;
    let replacements = placeholder_map(kbc);
    // `DBG_PLACEHOLDERS=path`: dump the baked guest constants, to read alongside
    // a `DBG_PROF_DUMP` profile (the guest's shape is entirely in these).
    if let Ok(path) = std::env::var("DBG_PLACEHOLDERS") {
        std::fs::write(&path, placeholder_lines(&replacements)).expect("write DBG_PLACEHOLDERS");
    }
    if input != hex(&input_digest(&replacements)) {
        return Err(format!(
            "stale: not compiled from the guest's source and placeholders at 2^{kbc}; \
             regenerate it with `formal/lean_vm/scripts/guest-artifact`"
        ));
    }
    if iv != hex(&program.bytecode().fiat_shamir_iv()) {
        return Err("its `iv` line is not its bytecode's Fiat-Shamir IV".into());
    }
    // `DBG_DISASM=path`: dump the guest's disassembly, to read alongside a
    // `DBG_PROF_DUMP` per-pc profile. Function boundaries lead the dump, so the
    // pc a failed guest check reports can be resolved to a source function
    // without re-deriving the layout by hand.
    if let Ok(path) = std::env::var("DBG_DISASM") {
        let mut ranges: Vec<_> = program.fn_ranges.iter().collect();
        ranges.sort_by_key(|(_, entry, _)| *entry);
        let mut dump = String::new();
        for (name, entry, len) in ranges {
            dump += &format!("# fn {entry:>7}..{:<7} {name}\n", entry + len);
        }
        dump += &zkdsl_compiler::disassemble(&program.prog);
        std::fs::write(&path, dump).expect("write DBG_DISASM");
    }
    Ok(program)
}
