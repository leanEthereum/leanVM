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
    ("const_params", "2153e3cb0756ed73b920a022b137b413bf681566f5b590ea831a3900a1fee4c3"),
    ("fibonacci", "d6182b921e19261adab5cd05720a58036c213700ab39546bde2d3e6d5d79c9d7"),
    ("hash_heap_chain", "162d8a7947caf7390f00f438eb8574d2c3f816d7c7d9d2502f4753e3f7cac421"),
    ("hash_slices", "1334356ec60100198baaf77b6936e50ced71e7e00ffcf16b10b8b7feddf5eedc"),
    ("heapbuf_dyn", "a6b2cd9cfebe83df9917901e5f500d3b0b63420ff6b041aeb36aa66e5ba9155d"),
    ("hint", "81765bea72a973009328b1b2d786884bdf7134f5b874fb15686e1fda4db7ad9e"),
    ("identities", "09088942077198724ad0dc745209f71539fa55979edb5e8121df36c633ed9f49"),
    ("match", "efa7fd1c253487aec9b0aec64e1d8719313de828e646326ecd84704ee71f50a8"),
    ("match_arms", "bfd294e9894b00d081c7395f9ef84bdfef328872d6b58a1b55488b7226f8401f"),
    ("nested", "1e1f5136011030591d6198528d2a6343fefeb73e5fd76b62377c9c8d2aaa6a44"),
    ("runtime_loop", "31efdcc9336de0fc0e310b937563f9f7c38bde2e8ba143ec33e2bf120047dca1"),
    ("scoping", "f616e5849c7e04b6f58a196ddfea3ae6588b2d62dfc765920ec1d69c644a7985"),
    ("unroll", "d2932fa6fb4ca9c1eb8c6ac390bd09726a4ecd8973bc67ba9750525a8c2a5c21"),
    ("wots_walk", "e30cadf67a03589109eb0cc53fee8473dcd34e7acaf97335a2fddf54c7e8d095"),
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
