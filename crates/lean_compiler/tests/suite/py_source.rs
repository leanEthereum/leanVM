//! zkDSL sources as `.py` files (as in leanVM's `test_data`): the `snark_lib`
//! stub import makes them valid Python for editors/linters, and the compiler
//! skips it (single-file programs only: importing anything else is an error).
//!
//! The harness is generic: every `tests/programs/*.py` is parsed, compiled,
//! proven, and verified. A program declares the public input it expects with a
//! top-of-file annotation of two constant field elements,
//!
//! ```text
//! # public_input: GEN ** 89, 101229015297003380629709256178361811305
//! ```
//!
//! or omits it to run with the empty public input (two zeros).

use std::fs;

use lean_compiler::{compile, parse, parse_const};
use leanvm_core::cpu::{prove, verify};
use primitives::field::F128;

/// The `# public_input: <elt>, <elt>` annotation, or `[0, 0]` if absent.
fn public_input(src: &str) -> [F128; 2] {
    for line in src.lines() {
        if let Some(rest) = line.trim().strip_prefix("# public_input:") {
            let parts: Vec<&str> = rest.split(',').collect();
            assert_eq!(
                parts.len(),
                2,
                "`# public_input:` needs two field elements, got `{rest}`"
            );
            let elt = |s: &str| parse_const(s).unwrap_or_else(|e| panic!("bad public_input: {e}"));
            return [elt(parts[0]), elt(parts[1])];
        }
    }
    [F128::ZERO; 2]
}

/// The `# witness <name>: <elt>, …` annotations: one line per *entry*
/// (repeated lines with the same name are the stream's successive entries,
/// popped by successive `hint_witness` calls).
fn witness(src: &str) -> std::collections::HashMap<String, Vec<Vec<F128>>> {
    let mut streams: std::collections::HashMap<String, Vec<Vec<F128>>> = Default::default();
    for rest in src.lines().filter_map(|l| l.trim().strip_prefix("# witness ")) {
        let (name, vals) = rest.split_once(':').expect("`# witness` needs `name: values`");
        let entry = vals
            .split(',')
            .map(|s| parse_const(s).unwrap_or_else(|e| panic!("bad witness value: {e}")))
            .collect();
        streams.entry(name.trim().to_string()).or_default().push(entry);
    }
    streams
}

/// Every program in `tests/programs/`, end to end.
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
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        let src = fs::read_to_string(&path).unwrap_or_else(|e| panic!("{name}: read: {e}"));
        let want = public_input(&src);
        let ast = parse(&src).unwrap_or_else(|e| panic!("{name}: parse: {e}"));
        let mut program = compile(&ast);
        for (stream, entries) in witness(&src) {
            program.set_witness(stream, entries);
        }
        let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
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
