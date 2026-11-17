//! The test programs compiled twice: by this crate, and by the compiler's back end written in Lean
//! (`formal/lean_vm/LeanVM/Compiler`), whose output is checked in (`lean_backend/*.txt`, written from
//! `formal/lean_vm` by `lake exe guest-backend export programs ../../crates/zkdsl_compiler/tests/suite/lean_backend`).
//! The two are the same bytecode under the same hints and source lines, and what Lean compiled runs and proves on
//! this VM.

use std::fs;

use isa::Program;
use lean_vm_core::cpu::{execute, prove, verify};
use primitives::field::F128;
use zkdsl_compiler::parse;

use crate::common::compile;
use crate::py_source::{public_input, witness};

/// Each test program's name, source and Lean-compiled text.
fn programs() -> Vec<(String, String, String)> {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests");
    let mut names: Vec<String> = fs::read_dir(format!("{dir}/programs"))
        .expect("tests/programs")
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "py"))
        .map(|p| p.file_stem().unwrap().to_string_lossy().into_owned())
        .collect();
    names.sort();
    assert!(!names.is_empty(), "no .py programs found");
    names
        .into_iter()
        .map(|name| {
            let src = fs::read_to_string(format!("{dir}/programs/{name}.py")).unwrap();
            let lean = fs::read_to_string(format!("{dir}/suite/lean_backend/{name}.txt")).unwrap_or_else(|e| {
                panic!("{name}: no Lean-compiled program ({e}): export it as this file's header says")
            });
            (name, src, lean)
        })
        .collect()
}

#[test]
fn the_lean_back_end_compiles_the_test_programs_to_the_same_program() {
    for (name, src, lean) in programs() {
        let rust = compile(&parse(&src).unwrap_or_else(|e| panic!("{name}: parse: {e}")));
        let text = rust.__to_text();
        if let Some((line, (ours, theirs))) = text.lines().zip(lean.lines()).enumerate().find(|(_, (a, b))| a != b) {
            panic!(
                "{name}, line {}: this crate compiles `{ours}`, Lean `{theirs}`",
                line + 1
            );
        }
        assert_eq!(text.lines().count(), lean.lines().count(), "{name}");
        // What Lean compiled, loaded, is the same program and runs the same.
        let loaded = Program::__from_text(&lean).unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_eq!(loaded.__to_text(), text, "{name}");
        assert_eq!(
            loaded.bytecode().fiat_shamir_iv(),
            rust.bytecode().fiat_shamir_iv(),
            "{name}"
        );
        let pi = public_input(&src).unwrap_or([F128::ZERO; 2]);
        let streams = witness(&src);
        let rows = |program: &Program| {
            execute(program, &streams, pi)
                .unwrap_or_else(|e| panic!("{name}: {e:?}"))
                .rows()
        };
        assert_eq!(rows(&loaded), rows(&rust), "{name}");
    }
}

/// A program the Lean back end compiled proves, and its proof verifies against the program this crate compiles.
#[test]
fn a_lean_compiled_program_proves() {
    let (name, src, lean) = programs()
        .into_iter()
        .find(|(name, ..)| name == "hint")
        .expect("hint.py");
    let pi = public_input(&src).unwrap_or([F128::ZERO; 2]);
    let loaded = Program::__from_text(&lean).unwrap();
    let (proof, _) = prove(&loaded, &witness(&src), pi, lean_vm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    let rust = compile(&parse(&src).unwrap());
    verify(&rust, &pi, &proof).unwrap_or_else(|e| panic!("{name}: verify: {e:?}"));
}

/// A failed `assert` names the same function and source line in the program Lean compiled as in the one this crate
/// compiles: `hint.py`'s `assert sb[1] == 12`, on a witness whose entry holds 13.
#[test]
fn a_failed_assert_names_its_line() {
    let (_, src, lean) = programs()
        .into_iter()
        .find(|(name, ..)| name == "hint")
        .expect("hint.py");
    let line = src.lines().position(|l| l.contains("assert sb[1] == 12")).unwrap() + 1;
    let src = src.replace("# witness r: GEN ** 5, 12", "# witness r: GEN ** 5, 13");
    let (pi, streams) = (public_input(&src).unwrap_or([F128::ZERO; 2]), witness(&src));
    let site = |program: &Program| execute(program, &streams, pi).err().expect("the assert fails").site;
    let lean = site(&Program::__from_text(&lean).unwrap());
    assert_eq!(lean, format!("main (line {line})"));
    assert_eq!(site(&compile(&parse(&src).unwrap())), lean);
}
