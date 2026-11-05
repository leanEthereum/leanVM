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
    ("fibonacci", "184585c370a069f11d2e151a2ed31514f48a7b52afb1c49d2d4601aeca245a05"),
    ("hash_heap_chain", "309365f5b90a6cf1fadde436e9df7d6022398b243cdd17f46c1b672044a63bdf"),
    ("hash_slices", "b8f40cefc0466e7be412e27be0fa513ff02bab648dd1c55fcad8b15a8983b5d6"),
    ("heapbuf_dyn", "95e1a69f54106145fc4f845e9076117ba3e891305dc30e20de6e2aa989ecb8e7"),
    ("hint", "4a4e977531e9603a9b2c5c4006c5f9289875caf9326d300e6cda53cf581764d9"),
    ("identities", "622b2661ca39c90b107b0364678a35daff1a2e52d149dd2d7c89160142397a92"),
    ("match", "869d6274e30949c7328c14ab98bcd5533194e929b31c6d12a3b2cf0267d8a2af"),
    ("match_arms", "253d6694f92e36ec53923921bea01a2c10fdc04c640b042740c3ad55ef3f6b30"),
    ("nested", "fa19f657b534a8bdaf894854617f65d46f35cfd49f0d19e93d2dda7a1f2b1b01"),
    ("runtime_loop", "69cc2dec0f66714ecc481a061f1c0635877210068e0618be48af085275ba9a95"),
    ("scoping", "15adff655932818f7ce52bd225e975fa9d38960a268aeda7af87e0272e75e1cf"),
    ("unroll", "6d4910546e117da89cb07a53851629341f632490d66c79213aa772ed83cfa191"),
    ("wots_walk", "af45309de7c7077092da609bc25b60a42dc3b5ac52a39281ffdc0c1198221934"),
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
