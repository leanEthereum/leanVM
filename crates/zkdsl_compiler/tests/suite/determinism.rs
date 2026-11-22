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
    ("const_params", "9ed29b06cd46c24112514b7b5333d16aab7abb62e2f925f50c01a901b4a613a9"),
    ("fibonacci", "4e4706f35420171cac8a0465fc0d3f452355f9cc1535b86108ba1450fff53e71"),
    ("hash_heap_chain", "95b378f997c069969c03cdc0976578d55dd03e8794779db9ec6ecf04b282c37e"),
    ("hash_slices", "237e03d5e2a594fa019a49f704fa32fa5233afb1ac9ceeabd9df5de9e4616c11"),
    ("heapbuf_dyn", "8e84360adbc674b70c24786ff14f5639291aed55279e27a1fa7a32982baca423"),
    ("hint", "6b27c03837b8c85f6422ebc1632fafb9bae171499dc1e199ca3037f069f5af3e"),
    ("identities", "745e533161ccd8b952945b289ab47cb42416e61a2c4a3654a5c459516b3bc5cf"),
    ("inline", "79ff322bd9b4366b01e3e14432e5a2382106a405fdca39de1bd48447f7a979de"),
    ("match", "cea7b8ac3bc4118004c6f554ac82c84c1df05e851ced181969736998cfa4b2b0"),
    ("match_arms", "f2a91b915f7e6fafe11706a05eadf2ef8beb13be7ff394719a25461641e8c192"),
    ("nested", "f4ee869b2cc79d260ed70855c1bd6ea9f1de3c7a0d274c49f68134d3630a83d1"),
    ("runtime_loop", "3d57312d1a0876fb580d43265c9c4772c6765a2a85978ece19414de2112c028a"),
    ("scoping", "c95d9aa824829e56e4ce220293020f833799bc3111acadd61cda57b0e02bc1c2"),
    ("unroll", "fbac995ae8c8682fe1e07675d4972a33968d65d8f9b704c28e7e5469b0495c42"),
    ("wots_walk", "cfa8b3667e830aad380bcdf87c49928fb11ebb85a989552cbf9632a088ed5bdf"),
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
