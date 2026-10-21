//! One source compiles to one program, always, and the same program it compiled
//! to yesterday.
//!
//! The bytecode digest leads the Fiat--Shamir transcript, so two builds of one
//! source that disagree are two incompatible proof systems, and the symptom is a
//! proof that stops verifying rather than a crash.
//!
//! Two different properties, and only the first is about determinism:
//!
//! * *Within a process*, compiling twice is a real perturbation rather than a
//!   repeat, since `RandomState` bumps its seed once per map, so the second
//!   compilation hashes with different keys than the first.
//! * *Across commits*, `GOLDEN` is a SNAPSHOT of the compiler's output. It does
//!   not prove determinism (nothing iterating a hash container reaches the
//!   bytecode today, and deliberately reversing the branch-output order at a join
//!   moves no digest). It earns its place a different way: a codegen change that
//!   was not intended shows up here and nowhere else, and every entry that moved
//!   this far was a change someone then had to justify.
//!
//! So a moved digest is a question, not a chore: update `GOLDEN` in the same
//! commit and say in the message which change moved it.

use std::collections::BTreeMap;
use std::fs;

use lean_compiler::{compile, parse};
use leanvm_core::cpu::Program;

/// `tests/programs/<name>.py` against the digest of the bytecode it compiles to.
/// The list is closed: a new program must be added here, so one cannot be added
/// without a digest.
#[rustfmt::skip]
const GOLDEN: &[(&str, &str)] = &[
    ("conditionals", "4f88f144b73dfb5e6453c12fb3f1b20bbc99835d2b7e8b30c0b80a8c4d558c40"),
    ("const_params", "f28aa76ef2b1415821a2573704d2590e8ac85e87d47c795b270a6fa7ff6625bb"),
    ("fibonacci", "edb68f2529e0a1cb12169b8f629eae2e196a26151917af0d8d8572ded22b3a64"),
    ("hash_heap_chain", "309365f5b90a6cf1fadde436e9df7d6022398b243cdd17f46c1b672044a63bdf"),
    ("hash_slices", "b8f40cefc0466e7be412e27be0fa513ff02bab648dd1c55fcad8b15a8983b5d6"),
    ("heapbuf_dyn", "95e1a69f54106145fc4f845e9076117ba3e891305dc30e20de6e2aa989ecb8e7"),
    ("hint", "ac78fc8dfcef7129fd40c591da640ed26c1798b4ca435fabe9994571c8fb0bcc"),
    ("identities", "6b5cdc55c458e318c8ea5b87f7cd212135e44698a0fd397bae5d835fa84b815a"),
    ("match", "9b83c42ba7b54d9ff0ed65a070f25ec36c969c3e1f4da050de2d8fa07cd9648e"),
    ("match_arms", "8a3e18fafab508ce3254c0a05d85a659605bb95d7620dce41e26a88dddbea3d4"),
    ("nested", "fa19f657b534a8bdaf894854617f65d46f35cfd49f0d19e93d2dda7a1f2b1b01"),
    ("runtime_loop", "187513c18352d40beae1bd224cac7140b9a9c0bf2847a0b4fe86f5982c741757"),
    ("scoping", "c680d0661bd5b8417ff6615c3b53dde83b15bb6554790429f68e8ed823699587"),
    ("unroll", "26d5455233a7e92a04dcee57798b2e8091dfd08bfcab9667952431ec20cf5252"),
    ("wots_walk", "f497f7276970efe06306bb21a324626d615e91ec78fc1d8fd7f9e74c383d4d12"),
];

fn digest(p: &Program) -> String {
    primitives::hash::hash(format!("{:?}", p.prog).as_bytes())
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// Every program in `tests/programs/`, compiled twice.
#[test]
fn bytecode_is_reproducible() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let mut paths: Vec<_> = fs::read_dir(dir)
        .expect("tests/programs")
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "py"))
        .collect();
    paths.sort();
    assert!(!paths.is_empty(), "no .py programs found");

    let mut actual: Vec<(String, String)> = Vec::new();
    for path in &paths {
        let name = path.file_stem().expect("file stem").to_string_lossy().into_owned();
        let src = fs::read_to_string(path).unwrap_or_else(|e| panic!("{name}: read: {e}"));
        let one = compile(&parse(&src).unwrap_or_else(|e| panic!("{name}: parse: {e}")));
        let two = compile(&parse(&src).unwrap_or_else(|e| panic!("{name}: parse: {e}")));
        assert_eq!(
            digest(&one),
            digest(&two),
            "{name}: two compilations of one source produced different bytecode, \
             so the compiler is reading a hash seed"
        );
        actual.push((name, digest(&one)));
    }

    let want: BTreeMap<&str, &str> = GOLDEN.iter().copied().collect();
    let moved: Vec<&str> = actual
        .iter()
        .filter(|(n, d)| want.get(n.as_str()) != Some(&d.as_str()))
        .map(|(n, _)| n.as_str())
        .collect();
    let dropped: Vec<&str> = want
        .keys()
        .copied()
        .filter(|n| !actual.iter().any(|(a, _)| a == n))
        .collect();
    assert!(
        dropped.is_empty(),
        "GOLDEN names a program that no longer exists: {dropped:?}"
    );
    if !moved.is_empty() {
        let table: String = actual
            .iter()
            .map(|(n, d)| format!("    (\"{n}\", \"{d}\"),\n"))
            .collect();
        panic!("bytecode changed for {moved:?}\n\nif that was intended, GOLDEN is now:\n{table}");
    }
}
