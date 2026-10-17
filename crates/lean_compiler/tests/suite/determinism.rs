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
    ("conditionals", "d7dc47593428f340f489e6281a2e7666800972f3300e7c66de629f3530e9ade0"),
    ("const_params", "8294b14e0ab6b7145b6c101ea79051fa80751f7dfa37973779607ffe4f68945b"),
    ("fibonacci", "d6182b921e19261adab5cd05720a58036c213700ab39546bde2d3e6d5d79c9d7"),
    ("hash_heap_chain", "162d8a7947caf7390f00f438eb8574d2c3f816d7c7d9d2502f4753e3f7cac421"),
    ("hash_slices", "1334356ec60100198baaf77b6936e50ced71e7e00ffcf16b10b8b7feddf5eedc"),
    ("heapbuf_dyn", "a6b2cd9cfebe83df9917901e5f500d3b0b63420ff6b041aeb36aa66e5ba9155d"),
    ("hint", "81765bea72a973009328b1b2d786884bdf7134f5b874fb15686e1fda4db7ad9e"),
    ("identities", "09088942077198724ad0dc745209f71539fa55979edb5e8121df36c633ed9f49"),
    ("match", "7c41dc4ca756a9762ecd2429c39f5dfafc4a4671b39f4bbc8f937fc42b72dadc"),
    ("match_arms", "dc7dc9fbaf04adea9a6e3687ab30cb757ef310bb3f3918cff5041228dfcf5bd4"),
    ("nested", "89555686cbba0061566c59f2dd20232d508c31862a33be0145bb1237d151fdb2"),
    ("runtime_loop", "31efdcc9336de0fc0e310b937563f9f7c38bde2e8ba143ec33e2bf120047dca1"),
    ("scoping", "f616e5849c7e04b6f58a196ddfea3ae6588b2d62dfc765920ec1d69c644a7985"),
    ("unroll", "d2932fa6fb4ca9c1eb8c6ac390bd09726a4ecd8973bc67ba9750525a8c2a5c21"),
    ("wots_walk", "0c498cd45def2cbdb8e5b4512c6aa4e5faab3c6d9d18166ff3dc730171d173b4"),
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
