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
    ("conditionals", "4555ec647e6a9d9329fa73d8c6378bb0c5da739768325edfeac3d1d0f1fa4b34"),
    ("const_params", "a30f3064a178ccaa9ce941e3fc12bf7536ba535087141caaf429d6e158d542c0"),
    ("fibonacci", "82f7ad2ccaf9bd8d4d721d182aa9c63ea656522c7d512cac0b28c2025c396281"),
    ("hash_heap_chain", "34975dffbf740d55f25ebe2bfcd23944d0e2188368d4555d40ce0e02a488be26"),
    ("hash_slices", "c5e0010f0a0f51ac61635911dcb4d0727d15f7b1af0de7080eab3ddb531a92e5"),
    ("heapbuf_dyn", "45673032a16ab7efe73b36884373a4cd458fd9206b1af3f26c57c15ab4436be3"),
    ("hint", "d653359b3a378686a4fdfd7a667d5e15e8d4cefac40a95d8095cd5d6b809cdce"),
    ("identities", "e0b1ec01996ec06a4de83c89da0796cab69149a1e542fc127098f5cdfcfa14e3"),
    ("inline", "e611b0269ad6b7fea2fe75f81f6f4c1ccfc4d48a0f129c5e6fd6672c7391fc43"),
    ("match", "dbb1aa76f8f33e545845208bd8ed8e7da768533255006df3972486ec5a6b1910"),
    ("match_arms", "0a8c12f423cc22507ef176c8e0884bac04013596678b3542a294ff86f1e495d5"),
    ("nested", "e1da90e778ca982dbda236c066f9459323c29c5a84cbd483c3280201a67e0413"),
    ("runtime_loop", "ecefaf9334816a7c4a5f913360aad9a67c393aa24a69e5a638a71ee2b14463fc"),
    ("scoping", "f563964e640c4258b0afa395b64ed86009bef4ea1a72b59acdbb7b9cef754938"),
    ("unroll", "1543d9628a3ecf27c16798b65c15d30894b4508232088ac4996786404080d523"),
    ("wots_walk", "b22db7b1907447f21f18144fa483bb0a9146a42e3eda258a48d5d9011b5ef117"),
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
