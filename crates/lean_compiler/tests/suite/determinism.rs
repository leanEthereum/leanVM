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
    ("conditionals", "5eff715feb68943cbce0050a6fe81c10017f41f2cf0503ecfbafc22dd62646d9"),
    ("const_params", "db981c9abe450a9f58c846e3ccdf1cb3a19176f59eff7aadcc593cae327ad637"),
    ("fibonacci", "dd55f106c94737bc0b05116246a5644c395536b3f9263c52a2158198fd620b64"),
    ("hash_heap_chain", "e8fdf0fc25c72817fd25377bc446576b6aed7a344353e6979d9578ad1df79895"),
    ("hash_slices", "7ee9bb65ed2b3d1c20c1e82f00bf26491632e2fe76f391f312ac70ded12b97ce"),
    ("heapbuf_dyn", "a0b2765fd1684f0eacaf2e37100f34e705b1bb77df70615ca34ee81f1923ed58"),
    ("hint", "d685590d9b64a46bb9d1dc074ec64aa479a432383b45ed90e0e70d7dad424ca8"),
    ("identities", "1885826cec7f92148d52e76b7dfeae8fbd743037eb01579a60e76b4ad59bfd68"),
    ("match", "40f098a1ce9d8686f339bb8138420efe36bd1ee5c17013368620f7508c246308"),
    ("match_arms", "4dad7a56ebd4ad1cabeba1d76c120cff534d13644446559de350d32f0ab59417"),
    ("nested", "68f62c2e13f209756236c72be8c4edd4e59f1662de11735bff51185ec38ad5b6"),
    ("runtime_loop", "e913b051b9ba4d623823adf94d2c60c74cc1d1add1025d4485515cf27b7242ec"),
    ("scoping", "9a9be3556e5899d326421b0cc2507c625974a180ee65c4054b938d4d78a19a74"),
    ("unroll", "0be3f7ffa860d53ba8e6874003c2ec349ffa112eb9ca064a11fa7968a7a3b6a6"),
    ("wots_walk", "36f5c06b84a83ca5fc3ea77f12bf0949000cba9c5b8898e4fee9d6fffaee8752"),
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
