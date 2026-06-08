use std::time::Instant;

use backend::{ArenaVec, BasedVectorSpace, PrimeCharacteristicRing, arena_vec};
use lean_compiler::*;
use lean_vm::*;
use rand::{RngExt, SeedableRng, rngs::StdRng};

#[test]
fn test_div_extension_field() {
    let program = r#"
DIM = 5

def main():
    nd = Array(2 * DIM)
    hint_witness("nd", nd)
    n = nd
    d = nd + DIM
    expected_q = Array(DIM)
    hint_witness("q", expected_q)
    computed_q_1 = div_ext_1(n, d)
    computed_q_2 = div_ext_2(n, d)
    assert_eq_ext(computed_q_2, expected_q)
    assert_eq_ext(computed_q_1, expected_q)
    return

def assert_eq_ext(x, y):
    for i in unroll(0, DIM):
        assert x[i] == y[i]
    return

def div_ext_1(n, d):
    quotient = Array(DIM)
    dot_product_ee(d, quotient, n)
    return quotient

def div_ext_2(n, d):
    quotient = Array(DIM)
    dot_product_ee(quotient, d, n)
    return quotient
    "#;

    let mut rng = StdRng::seed_from_u64(0);
    let n: EF = rng.random();
    let d: EF = rng.random();
    let q = n / d;
    let mut nd_buf: ArenaVec<F> = ArenaVec::new();
    nd_buf.extend_from_slice(n.as_basis_coefficients_slice());
    nd_buf.extend_from_slice(d.as_basis_coefficients_slice());
    let q_buf = ArenaVec::from_slice(q.as_basis_coefficients_slice());
    let bytecode = compile_program(&ProgramSource::Raw(program.to_string()));
    let mut hints = Hints::default();
    hints.insert(&bytecode, "nd", arena_vec![nd_buf]);
    hints.insert(&bytecode, "q", arena_vec![q_buf]);
    let witness = ExecutionWitness {
        hints,
        ..ExecutionWitness::default()
    };
    try_execute_bytecode(&bytecode, &Default::default(), &witness, false).unwrap();
}

fn test_data_dir() -> String {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    format!("{manifest_dir}/tests/test_data")
}

fn find_files(dir: &str, prefix: &str, suffix: &str) -> Vec<String> {
    let mut paths: Vec<String> = std::fs::read_dir(dir)
        .expect("Failed to read test data directory")
        .filter_map(|entry| entry.ok())
        .filter_map(|entry| {
            let path = entry.path();
            let filename = path.file_name()?.to_str()?;
            if filename.starts_with(prefix) && filename.ends_with(suffix) {
                Some(path.to_string_lossy().to_string())
            } else {
                None
            }
        })
        .collect();
    paths.sort();
    paths
}

#[test]
fn test_num_files() {
    let expected_num_files = 3; // program_2.py imports foo.py and bar.py
    let path = format!("{}/program_2.py", test_data_dir());
    let bytecode = compile_program(&ProgramSource::Filepath(path));
    assert_eq!(bytecode.filepaths.len(), expected_num_files);
    assert_eq!(bytecode.source_code.len(), expected_num_files);
}

#[test]
fn test_all_errors() {
    let test_dir = test_data_dir();
    let paths = find_files(&test_dir, "error_", ".py");

    assert!(!paths.is_empty(), "No error_*.py files found");
    println!("Found {} test error programs", paths.len());

    for path in paths {
        let result = try_compile_and_run(&ProgramSource::Filepath(path.clone()), &[F::ZERO; DIGEST_LEN], false);
        assert!(result.is_err(), "Expected error for {}, but it succeeded", path);
    }
}

#[test]
fn test_placeholder_replacement_respects_identifier_boundaries() {
    let program = r#"
def main():
    x1 = 5
    xPLACEHOLDER = 7
    assert x1 == 5
    assert xPLACEHOLDER == 7
    assert PLACEHOLDER == 1
    return
"#;
    let mut replacements = std::collections::BTreeMap::new();
    replacements.insert("PLACEHOLDER".to_string(), "1".to_string());
    let bytecode = try_compile_program_with_flags(
        &ProgramSource::Raw(program.to_string()),
        CompilationFlags { replacements },
    )
    .unwrap();
    try_execute_bytecode(&bytecode, &Default::default(), &ExecutionWitness::default(), false).unwrap();
}

#[test]
fn test_all_programs() {
    let test_dir = test_data_dir();
    let paths = find_files(&test_dir, "program_", ".py");

    assert!(!paths.is_empty(), "No program_*.py files found");
    println!("Found {} test programs", paths.len());

    // Reserve a 5-cell preamble for the programs that materialize a local
    // ONE_EF_PTR (program_15, program_179).
    let witness = ExecutionWitness {
        preamble_memory_len: 5,
        ..ExecutionWitness::default()
    };
    for path in paths {
        let bytecode = match try_compile_program(&ProgramSource::Filepath(path.clone())) {
            Ok(b) => b,
            Err(err) => panic!("Program {} failed to compile: {:?}", path, err),
        };
        if let Err(err) = try_execute_bytecode(&bytecode, &Default::default(), &witness, false) {
            panic!("Program {} failed with error: {:?}", path, err);
        }
    }
}

#[test]
fn test_reserved_function_names() {
    for name in RESERVED_FUNCTION_NAMES {
        let program = format!("def main():\n    return\ndef {name}():\n    return");
        assert!(
            try_compile_and_run(&ProgramSource::Raw(program), &[F::ZERO; DIGEST_LEN], false).is_err(),
            "Expected error when defining function with reserved name '{name}', but it succeeded"
        );
    }
}

#[test]
fn debug_file_program() {
    let index = 167;
    let path = format!("{}/program_{}.py", test_data_dir(), index);
    compile_and_run(&ProgramSource::Filepath(path), &[F::ZERO; DIGEST_LEN], false);
}

#[test]
fn test_fp_negative_offset() {
    let program = r#"
def main():
    a = Array(16)
    for i in unroll(0, 8):
        a[i] = i
    b = a - 1000
    for i in unroll(0, 1000):
        func(a, b + 1008)
    return

@inline
def func(a, b):
    poseidon16_compress_half(a, a, b)
    return
   "#;
    let bytecode = compile_program(&ProgramSource::Raw(program.to_string()));
    let n_cycles = execute_bytecode(&bytecode, &Default::default(), &ExecutionWitness::default(), false).n_cycles();
    assert!(n_cycles < 1100);
}

#[test]
fn test_parallel_loop() {
    let program = r#"
def main():
    n = 16
    res = Array(n)
    for i in loop(0, n):
        res[i] = factorial(10000)
    sum_buf = Array(n + 1)
    sum_buf[0] = 0
    for i in range(0, n):
        sum_buf[i + 1] = sum_buf[i] + res[i]
    print(sum_buf[n])
    return

def factorial(n):
    if n == 0:
        return 1
    else:
        return n * factorial(n - 1)
   "#;

    let compiled_sequencial = compile_program(&ProgramSource::Raw(program.replace("loop", "range")));
    let compiled_parallel = compile_program(&ProgramSource::Raw(program.replace("loop", "parallel_range")));

    let time_sequential = Instant::now();
    let exec_seq = execute_bytecode(
        &compiled_sequencial,
        &Default::default(),
        &ExecutionWitness::default(),
        false,
    );
    let duration_sequential = time_sequential.elapsed();
    let time_parallel = Instant::now();
    let exec_par = execute_bytecode(
        &compiled_parallel,
        &Default::default(),
        &ExecutionWitness::default(),
        false,
    );
    let duration_parallel = time_parallel.elapsed();

    assert_eq!(exec_seq.metadata.stdout, exec_par.metadata.stdout);
    assert_eq!(exec_seq.n_cycles(), exec_par.n_cycles());
    assert_eq!(exec_seq.runtime_memory_size, exec_par.runtime_memory_size);

    println!("Sequential duration: {:.4}s", duration_sequential.as_secs_f64());
    println!("Parallel duration: {:.4}s", duration_parallel.as_secs_f64());
    println!(
        "Speedup: {:.2}x",
        duration_sequential.as_secs_f64() / duration_parallel.as_secs_f64()
    );
}

#[test]
fn debug_str_program() {
    let program = r#"
def main():
    a = 2
    b = 3
    for i in unroll(0, a * b):
        print(i)
    return
   "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), &[F::ZERO; DIGEST_LEN], false);
}

#[test]
#[rustfmt::skip]
fn test_soundness_suite() {
    #[allow(clippy::type_complexity)]
    let cases: &[(&str, &[u32], &[(usize, u32)])] = &[
        ("soundness_0", &[3, 6, 7, 10, 9, 20, 26, 1], &[(0, 4), (1, 7), (2, 8), (3, 11), (4, 10), (5, 21), (6, 27), (7, 0), (7, 2)]),
        ("soundness_1", &[5, 10, 6, 7, 42, 9, 5, 4],  &[(0, 6), (1, 11), (2, 7), (3, 8), (4, 43), (5, 10), (6, 6), (7, 5)]),
        ("soundness_2", &[3, 4, 5, 29, 7, 1, 17, 46], &[(0, 2), (1, 5), (2, 6), (3, 30), (4, 8), (5, 0), (5, 2), (6, 18), (7, 47)]),
        ("soundness_3", &[4, 2, 14, 120, 5, 10, 50, 55], &[(0, 5), (1, 3), (2, 15), (3, 121), (4, 6), (5, 11), (6, 51), (7, 56)]),
        ("soundness_4", &[5, 10, 10, 3, 4, 19, 20, 1], &[(0, 6), (1, 11), (2, 11), (3, 4), (4, 5), (5, 20), (6, 50), (7, 0), (7, 2)]),
        ("soundness_5", &[3, 4, 7, 19, 49, 28, 1, 3],  &[(0, 4), (1, 5), (2, 8), (3, 20), (4, 50), (5, 29), (6, 0), (6, 2), (7, 4)]),
    ];

    let to_input = |v: &[u32]| -> [F; PUBLIC_INPUT_LEN] {
        let mut out = [F::ZERO; PUBLIC_INPUT_LEN];
        for (slot, &x) in out.iter_mut().zip(v) {
            *slot = F::new(x);
        }
        out
    };

    for &(name, valid, perturbations) in cases {
        let path = format!("{}/{}.py", test_data_dir(), name);
        let bytecode = compile_program(&ProgramSource::Filepath(path));

        try_execute_bytecode(&bytecode, &to_input(valid), &ExecutionWitness::default(), false)
            .unwrap_or_else(|err| panic!("{name}: valid input {valid:?} must succeed, got {err:?}"));

        for &(idx, bad_value) in perturbations {
            let mut input = valid.to_vec();
            input[idx] = bad_value;
            let res = try_execute_bytecode(&bytecode, &to_input(&input), &ExecutionWitness::default(), false);
            assert!(
                res.is_err(),
                "{name}: perturbation p[{idx}]={bad_value} (input {input:?}) unexpectedly succeeded",
            );
        }
    }
}
