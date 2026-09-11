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
use lean_vm::cpu::Program;

/// `tests/programs/<name>.py` against the digest of the bytecode it compiles to.
/// The list is closed: a new program must be added here, so one cannot be added
/// without a digest.
#[rustfmt::skip]
const GOLDEN: &[(&str, &str)] = &[
    ("conditionals", "e8df2b807d3eed366d83843e207f0a9441c1e2014ee0add958a399af562a761c"),
    ("const_params", "f54f8df2c2259de3452565448aa2ae51b3dc3516ce21e04ba6d4a092848f9da3"),
    ("fibonacci", "1419063250d0c54fa808499fdca691748dfb91f84f1007c6f0e939d5ef6779b6"),
    ("hash_heap_chain", "9d8735c8393dd6cde7e07a71277a52435ca903186c6a984161b2b8821d6b552d"),
    ("hash_slices", "99b3de0af47b797b51b8f38f37b5ccb7ff64d3f5acd9ba23bdd1ff4cfc47e9c3"),
    ("heapbuf_dyn", "9e570732cf9258379eec6caf1efb2bd2d8ed484b5aa8c7b7da5360d2a79103ef"),
    ("hint", "d9601df070184a3f1a5702d769e3897013c17a264889161df8ae7efe0daecc13"),
    ("identities", "49a2bbd6bf785786f2ce8bf8f63a57a21bb6c547eae0c0f245f20a5222ac1c7a"),
    ("match", "803e3a09e25825144dca768065f8acf69fa06a6ffb49c2b26e09f91849ae004b"),
    ("match_arms", "00dcb9eff4ae060c20316f2567516c79d78fd0402abbefe35fbf3b62eee7bbb6"),
    ("nested", "ae5e3556925b1ce14a0e7b6000fb5dc4a8909a7788e19f70c90dba418be56951"),
    ("runtime_loop", "f33c6b5b82ed8ade198fb8978ba443554fc8714082a98dc784dbabdcee92e0fe"),
    ("scoping", "c466babcc1af1deba56dda628e730d815d2fdffe065d695f9118167e0bb8669f"),
    ("unroll", "08ebe1f4b51d862c6335b90694cf60d2fd2841d3a9913f6400cb53322117d309"),
    ("wots_walk", "060605d64f78c7574598f40b0b060a58059a2122bfdcb79eb9ab3d317530d9d7"),
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
