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
    ("conditionals", "f40783e317d6aee67c45cdb8add3c21913279da0d2bbb84a2d7a477a3030c7bb"),
    ("const_params", "56755f65fd1b896aff8d05a0631ebc4848225acc8376ad5364626f5ded786209"),
    ("fibonacci", "6380549936cc2c2353e87d3b10c944ea1903e2d06e3e4d78e5ec759883bf7766"),
    ("hash_heap_chain", "5b16ae1c77d2e5162e23a62ba4ecf201b40fd076895a6c8676ffff67ef314c5b"),
    ("hash_slices", "a942f6f85d3a47c65ec39e7d7e3a8cac4b81c7f8fec9c4b00c95661493899265"),
    ("heapbuf_dyn", "f1de94049d8b2b0b00f653fa86c65aa68eeacf4ea3052199e93199c6e4407e5b"),
    ("hint", "9e9778d0cafb726bf0486ecc15f96090f3e84d501ef6e49e6d0b0eed2b147b1c"),
    ("identities", "83c3eac11423f4a2fbbabca0c714652287234334517de548dc451c77fd8d2825"),
    ("match", "d3b33d77b8c2a69b9964c2d45cb275cd9146d163319e3221ee776c5c5b0ecc34"),
    ("match_arms", "10e8a2ae79dce52a4c6374e5d37798729da3d1cd8bbc198ff76d1547f6d1490c"),
    ("nested", "254f7d333044e518628c74d50210622ca4d07be161ecc4ae20c09b3879033fde"),
    ("runtime_loop", "c70c80914e743fbb74dab865050a178d6aef11de9d10a64117e27428f2ea81d8"),
    ("scoping", "abee9e8a0ca5651d9ff51590fe70982f7ef224d0a7b11a43ba507869b49eeb75"),
    ("unroll", "0b5c8a729a210206e0aa1f633544443224ada07f2b6fd200396b90c4b439feb3"),
    ("wots_walk", "a63f74ef19d6c0c3f130230b8e1715bd279ff0fe5fb293efa179ed98bbf79e85"),
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
