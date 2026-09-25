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
    ("conditionals", "3608b2008152e0dbedc03530f07208e74eacf7f41b147113ef924679157ba1cc"),
    ("const_params", "d85fc4de9189b052839f37c6aeba1caba2ef710ce3c7e4b8ea4d2306660cbc61"),
    ("fibonacci", "98bf9b4cc54bb6c59ed96c4d805e08d66d558fd991347e220893e74fbca7fe43"),
    ("hash_heap_chain", "119a2d00632f3da57fb6d40d42ec72688a2c97a46dcb9579a7a0c71b9c6b2263"),
    ("hash_slices", "796b147b16c140c8a37cb126c0a711d4d163536cced43f7ff606b148cd89150c"),
    ("heapbuf_dyn", "e02a00c58e1f701e262c4e3642aafbe369245430e2ee434c17c11881753723b2"),
    ("hint", "46034b6ab332bbf6bdb02f6342ef92fd5291391f972b0c3e2103865fe3b21a7e"),
    ("identities", "8629e2c42bdfa330632b8ca1e69acb70bd5147ba03a35e7d9509f92479e9b49c"),
    ("match", "1b77f181bf9ca3274908f796c8cf8609e1254c67087a83c6e3187d040c98a387"),
    ("match_arms", "67dce2773db5b68cd90f9bffc92220339e843e7720af636f65480fa48d06b1dc"),
    ("nested", "afd015a1114d271c3d32b4cf988e8ad3bc0112710e88cc571c5394ee44bb3633"),
    ("runtime_loop", "b3a7f974aaca4e634b43d2fd590cc2646a5564e95122908b5d65bede005b625b"),
    ("scoping", "29161f2fcfc8f81b599204bf4274ce554f6c6e586dba0388eb1cd4251d40790c"),
    ("unroll", "9ee2811ca1ef28ef9edef76ead9f178e0947b0c08e50bc4faff40ede4c245ad8"),
    ("wots_walk", "87b851fb57b504e8bf0aaa2a102c82d40fc9589a4392ab79cd13eb1f8cae9e75"),
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
