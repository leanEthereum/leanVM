//! zkDSL sources as `.py` files (as in leanVM's `test_data`): the `snark_lib`
//! stub import makes them valid Python for editors/linters, and the compiler
//! skips it (single-file programs only: importing anything else is an error).
//!
//! The harness is generic: every `tests/programs/*.py` parses, and the program the
//! Lean back end compiled from it (`tests/compiled/<name>.txt`, written by
//! `lake exe guest-backend export programs`) is proven and verified. A program
//! declares the public input it expects with a top-of-file annotation of two
//! constant field elements,
//!
//! ```text
//! # public_input: GEN ** 89, 101229015297003380629709256178361811305
//! ```
//!
//! or omits it to run with the empty public input (two zeros).
//!
//! `formal/lean_vm/scripts/export-rust.sh` includes this file for [`public_input`] and [`witness`].

use std::fs;

use isa::Program;
use lean_vm_core::cpu::{from_scalar, prove, verify};
use primitives::field::F128;
use zkdsl::{parse, parse_const};

/// The `# public_input: <elt>, <elt>` annotation, if any.
pub(crate) fn public_input(src: &str) -> Option<[F128; 2]> {
    for line in src.lines() {
        if let Some(rest) = line.trim().strip_prefix("# public_input:") {
            let parts: Vec<&str> = rest.split(',').collect();
            assert_eq!(
                parts.len(),
                2,
                "`# public_input:` needs two field elements, got `{rest}`"
            );
            let elt = |s: &str| from_scalar(parse_const(s).unwrap_or_else(|e| panic!("bad public_input: {e}")));
            return Some([elt(parts[0]), elt(parts[1])]);
        }
    }
    None
}

/// Named prover streams, each a list of entries.
pub(crate) type Streams = Vec<(String, Vec<Vec<F128>>)>;

/// The `# witness <name>: <elt>, …` annotations: one line per *entry*
/// (repeated lines with the same name are the stream's successive entries,
/// popped by successive `hint_witness` calls).
pub(crate) fn witness(src: &str) -> Streams {
    let mut streams: Streams = Vec::new();
    for rest in src.lines().filter_map(|l| l.trim().strip_prefix("# witness ")) {
        let (name, vals) = rest.split_once(':').expect("`# witness` needs `name: values`");
        let entry = vals
            .split(',')
            .map(|s| from_scalar(parse_const(s).unwrap_or_else(|e| panic!("bad witness value: {e}"))))
            .collect();
        match streams.iter_mut().find(|(stream, _)| stream == name.trim()) {
            Some((_, entries)) => entries.push(entry),
            None => streams.push((name.trim().to_string(), vec![entry])),
        }
    }
    streams
}

/// The program `tests/programs/<name>.py` as the Lean back end compiled it, its witness streams and its public input.
pub(crate) fn lean_compiled(name: &str) -> (Program, Streams, [F128; 2]) {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests");
    let src = fs::read_to_string(format!("{dir}/programs/{name}.py")).unwrap_or_else(|e| panic!("{name}: read: {e}"));
    let text = fs::read_to_string(format!("{dir}/compiled/{name}.txt")).unwrap_or_else(|e| {
        panic!("{name}: no Lean-compiled program ({e}): run `lake exe guest-backend export programs`")
    });
    let program = Program::__from_text(&text).unwrap_or_else(|e| panic!("{name}: {e}"));
    (program, witness(&src), public_input(&src).unwrap_or([F128::ZERO; 2]))
}

/// Every program in `tests/programs/` parses, and proves and verifies as Lean compiled it.
#[test]
fn all_py_programs() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let mut paths: Vec<_> = fs::read_dir(dir)
        .expect("tests/programs")
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "py"))
        .collect();
    paths.sort();
    assert!(!paths.is_empty(), "no .py programs found");

    for path in paths {
        let name = path.file_stem().unwrap().to_string_lossy().into_owned();
        let src = fs::read_to_string(&path).unwrap_or_else(|e| panic!("{name}: read: {e}"));
        parse(&src).unwrap_or_else(|e| panic!("{name}: parse: {e}"));
        let (program, streams, want) = lean_compiled(&name);
        let (proof, _) = prove(&program, &streams, want, lean_vm_core::pcs::TEST_LOG_INV_RATE).unwrap();
        verify(&program, &want, &proof).unwrap_or_else(|e| panic!("{name}: verify: {e:?}"));
        println!("{name}: ok");
    }
}

/// Both import spellings are tolerated (and skipped).
#[test]
fn snark_lib_import_forms() {
    for import in ["import snark_lib", "from snark_lib import *"] {
        let src = format!("{import}\ndef main():\n    return\n");
        parse(&src).expect("snark_lib import is skipped");
    }
}

/// Importing anything else is a parse error: no multi-file programs (yet).
#[test]
fn other_imports_rejected() {
    for import in ["import math", "from utils import *"] {
        let src = format!("{import}\ndef main():\n    return\n");
        let err = parse(&src).expect_err("non-snark_lib import must be rejected");
        assert!(err.contains("file imports are not supported"), "{err}");
    }
}
