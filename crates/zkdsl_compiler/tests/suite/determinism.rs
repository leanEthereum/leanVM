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
    ("conditionals", "d4f4126abc9ea51be42e477278b4ba53d17b161104cabff7deec50de43994292"),
    ("const_params", "c88e2d1d861fa655b13567944f2829890ae658c2bbc0cabef82eacd4014ecb0d"),
    ("fibonacci", "8a97e3a616df5671a158e8e87d90133c3815d52f31ff8073fa567b8836425691"),
    ("hash_heap_chain", "95b378f997c069969c03cdc0976578d55dd03e8794779db9ec6ecf04b282c37e"),
    ("hash_slices", "237e03d5e2a594fa019a49f704fa32fa5233afb1ac9ceeabd9df5de9e4616c11"),
    ("heapbuf_dyn", "8e84360adbc674b70c24786ff14f5639291aed55279e27a1fa7a32982baca423"),
    ("hint", "432788b9aca1b21d99e745770e5790d28ea3b35d6819db4f808fa149bdb61824"),
    ("identities", "6e03baffeb9abbcc827722fa3c0c90a317b39eb3dcc016e063e4cbc180f3a8b7"),
    ("inline", "3d4906a6e37672a9efe7f0ab3c8eee6033cfa867064b7aed444aceb53b7a5085"),
    ("match", "cea7b8ac3bc4118004c6f554ac82c84c1df05e851ced181969736998cfa4b2b0"),
    ("match_arms", "f2a91b915f7e6fafe11706a05eadf2ef8beb13be7ff394719a25461641e8c192"),
    ("nested", "c68d71ca2e3ba7404eab8f32e692b8125907699f6081060e4867f6dca897080b"),
    ("runtime_loop", "c08ab5953048e84eaaa7c19f8e4851c4f6ec710cd64d57e84831257ffec35aef"),
    ("scoping", "c401b4dac92f26296e315f08e1229eb18609cb81005d1da1859f3b65d80571a0"),
    ("unroll", "dcc038932d6f4bc49605e02d2369fb24ba1efefdc4d3333d7b1dbdd1eae693b0"),
    ("wots_walk", "1eea84f92a301ad6cd298b1c46ea88f2af4d5dfb7af0d589f56b07876b23c718"),
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
