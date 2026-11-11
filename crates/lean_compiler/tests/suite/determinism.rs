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
    ("conditionals", "4f88f144b73dfb5e6453c12fb3f1b20bbc99835d2b7e8b30c0b80a8c4d558c40"),
    ("const_params", "9e2168aed0eab72821f98f91e0406e226bf4d108acf15ee5c96868b93fd7e16e"),
    ("fibonacci", "184585c370a069f11d2e151a2ed31514f48a7b52afb1c49d2d4601aeca245a05"),
    ("hash_heap_chain", "f281889e8c3abdbacef18b6a5974345576874a12d90e46c8806b1803ea3b1556"),
    ("hash_slices", "9d4604cc5e6f978b3dc855143f3bedf4a3396e44c32c1df7dcfd543781fcd15f"),
    ("heapbuf_dyn", "95e1a69f54106145fc4f845e9076117ba3e891305dc30e20de6e2aa989ecb8e7"),
    ("hint", "4a4e977531e9603a9b2c5c4006c5f9289875caf9326d300e6cda53cf581764d9"),
    ("identities", "622b2661ca39c90b107b0364678a35daff1a2e52d149dd2d7c89160142397a92"),
    ("match", "9b83c42ba7b54d9ff0ed65a070f25ec36c969c3e1f4da050de2d8fa07cd9648e"),
    ("match_arms", "253d6694f92e36ec53923921bea01a2c10fdc04c640b042740c3ad55ef3f6b30"),
    ("nested", "fa19f657b534a8bdaf894854617f65d46f35cfd49f0d19e93d2dda7a1f2b1b01"),
    ("runtime_loop", "ccb3518649d47408ea3611cdee45751008dcad844e67a41bf2135d2c33741d19"),
    ("scoping", "15adff655932818f7ce52bd225e975fa9d38960a268aeda7af87e0272e75e1cf"),
    ("unroll", "33034051ad6dfb29235b60f32002ab48b6b93312c2964066c8d08130299c89be"),
    ("wots_walk", "c834495bca574608f0188354f1d0f25ac9c6e3a38af0581504e1b82045d64062"),
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
