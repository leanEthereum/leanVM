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

use crate::common::compile;
use lean_compiler::parse;
use leanvm_core::cpu::Program;

/// `tests/programs/<name>.py` against the digest of the bytecode it compiles to.
/// The list is closed: a new program must be added here, so one cannot be added
/// without a digest.
#[rustfmt::skip]
const GOLDEN: &[(&str, &str)] = &[
    ("conditionals", "8f0e736626c5c469ce288efada5553b31f672a2b0471872dc3e609d431d5f0eb"),
    ("const_params", "7fad4f0d6d49a8bff110a359ab9d1e953e8c3b4c38fe8568f892833a050ff015"),
    ("fibonacci", "ca3f253dc505e0acbd0dfdd71e1a33318c3e3271cd1902ae4fdb40f3d4353719"),
    ("hash_heap_chain", "8e13b562bce9fa8b9db445836449714beaf410507dc1ecaaffd2efc78e62174f"),
    ("hash_slices", "c9818c5ba6a031fa90ac299ce3ecce1ef6e3d2492da37750b5c2b27ada6e588a"),
    ("heapbuf_dyn", "e231b6a7270b4373c451be0fa975dae321be5355d63d74033dcbfdc3e2529670"),
    ("hint", "bb3aef8ceb73116663a3b2bb23f11515c375a42a9ee3344d87a6f5f04ff89b42"),
    ("identities", "6e03baffeb9abbcc827722fa3c0c90a317b39eb3dcc016e063e4cbc180f3a8b7"),
    ("match", "201f7d4b4adba9a14d1298cdbea5d703b06469fece1586cb7fd08ed72dca7430"),
    ("match_arms", "d181b0c1c481f0c8a770298e6209cd59fd54cf4dea728be96bad2bd5fbabf136"),
    ("nested", "d171f55d8352e49c7b771e4445974195c5f10836032f5364cf4508a0d278ab18"),
    ("runtime_loop", "284c2c4b601eeda56b68c78b940a206c157775197f33ca0874a1335ff238f46a"),
    ("scoping", "b43862cb6761c5bd33fc49d18ab06b431fe81ec04b67e8e3a68755c9a041a3cc"),
    ("unroll", "1a171f6630684161a36c04eea0b757dafee144c87330a1cf8738b30a4c9ee74a"),
    ("wots_walk", "e9e0ea74ffe31cefd23bd793e5f9f348ba531437503b7bbb5c2abe7c6fd026d5"),
];

fn digest(p: &Program) -> String {
    primitives::hash::hash(format!("{:?}", p.prog()).as_bytes())
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
