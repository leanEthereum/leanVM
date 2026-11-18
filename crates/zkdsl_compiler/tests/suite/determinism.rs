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
use isa::Program;
use zkdsl_compiler::parse;

/// `tests/programs/<name>.py` against the digest of the bytecode it compiles to.
/// The list is closed: a new program must be added here, so one cannot be added
/// without a digest.
#[rustfmt::skip]
const GOLDEN: &[(&str, &str)] = &[
    ("conditionals", "3e31186156a927f37ce2d3831a7202f6a495b1db7c6d73862bb42c1039b9e69b"),
    ("const_params", "af7e5058da27ffdb2ee2b1a2fe88b741ed2d7af6d1790c20535431f7d38ceddf"),
    ("fibonacci", "2520b89f2288778123643505116ae9796337188937451e163b075284c415c6b4"),
    ("hash_heap_chain", "d7b9191ce053eef377db872415344e047669d52c248ed604bc0a5d6ca9cc1d78"),
    ("hash_slices", "5efd4a0807024c68a8558cbd0278a02d486dd51f64b1b09c37de8765a905152f"),
    ("heapbuf_dyn", "6f5fe30124ff6a5f474acfa6c94396222a6be876badbb1c8cabaff42c9b2dc94"),
    ("hint", "a54823b7939367496709b7d4986df39d43f693b99aab770adb7f14547a568613"),
    ("identities", "8a2829a1ea6353ccb7c94b0b6976080746adc7bf6fa1ecaa405ca40f92d674c9"),
    ("match", "379fd144de8e5845bc9a2140f189c5ddc5ea2ad9d3c202719b90aa0f9300c4f6"),
    ("match_arms", "d234f70739700d5a10993103cda031ff5359678b6ebe674f13ad8a22052cb0e7"),
    ("nested", "ef94bc73d2daf795c06c04b5cf6f77c2a7c371bb55985c2295ce38a50b565a59"),
    ("runtime_loop", "8ae8e9f59fea6850e6f10524d89e4ad700e7166eefeb1c1c226f5edac5e5f548"),
    ("scoping", "f56d7c99054692dc83f7204a093de073399c67ac7a18287c263a5d18fcd13e42"),
    ("unroll", "850f510d19ad58f0d09f4c33ef2def371a1e84add73e91b50a39eeead0d1aaf5"),
    ("wots_walk", "8ed63a91cb6e4237da29b9e3e8a5a73222b757daff5ec06c40f6d0742280d1a0"),
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
