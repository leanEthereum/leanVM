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
    ("conditionals", "ed72764098b40502c4e6c6fe6798ef83218a979e68ca5a34db13a36561860f78"),
    ("const_params", "121c290d759b7f5911aad2d881387b31d2b7be5369478a5603aa121af14ee3a8"),
    ("fibonacci", "0f5a9468d0e92b724c5798ba65d00ea9b5f8099ac8a98c0eafbe0df74d06187a"),
    ("hash_heap_chain", "b8fbfaae945e16fb4eb673614240f85b7f4c401b773b360531f1c441a06db675"),
    ("hash_slices", "90e83d6e531bf730f6509b98cd4554cdc48b6553ad606fe35eca2b2b85b85130"),
    ("heapbuf_dyn", "9a2ae4898ed49d29df0f3d0a652247fc9976f192e768ba66d79d7d82fe45976a"),
    ("hint", "52da44acea39cc7db396b3280519fa172fdbe684fcb4779ce07254e3a9da7c33"),
    ("identities", "e0b1ec01996ec06a4de83c89da0796cab69149a1e542fc127098f5cdfcfa14e3"),
    ("inline", "7e333e8df8f1d11d7eb47d3574e49c1a40eb939061975ae52ec548255251e88c"),
    ("match", "f028efcf9532a46b6d8cde539d058a88bf522f2a5a8f70ef2611cbd8bc5263fc"),
    ("match_arms", "5beb2e73c258f442bbf010b555460474b72a885682d19e08fe6005126267f419"),
    ("nested", "a263e8066099e24ef21d45588579551eba0615e392dddfb0bdd94019ec9b6e84"),
    ("runtime_loop", "b36d44ff76fd7d1bb482378949d198b5706a79b57ccaf68896bce7e503ba1f63"),
    ("scoping", "7f170f9c6ec2893b693793a46aa424af61c087753a3468ef7377d4e28452dfd8"),
    ("unroll", "b6fd198ff4247a9a36d21149b14743ba08a757a1c0e6de49d6acb977aa0ab2f9"),
    ("wots_walk", "3a0f0552095d8874cfb8ffbbde41dc7fa80ef8986a59940ad6049f3a9e6d4d29"),
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
