use std::{collections::BTreeMap, io::Write};

use crate::{default_whir_config, prove_execution::prove_execution, verify_execution::verify_execution};
use backend::*;
use lean_compiler::*;
use lean_vm::*;
use rand::{RngExt, SeedableRng, rngs::StdRng};
use utils::{init_tracing, poseidon16_compress, poseidon16_permute};

const N: usize = 11;
const M: usize = 3;

const ALL_PRECOMPILES_PROGRAM: &str = r#"
DIM = 5
N = 11
M = 3
DIGEST_LEN = 8
HALF_DIGEST_LEN = 4
SCRATCH_SIZE = 8192
LOOP_ITERS = LOOP_ITERS_PLACEHOLDER

def main():
    scratch = Array(SCRATCH_SIZE)
    hint_witness("scratch", scratch)
    poseidon16_compress(scratch + 4 * DIGEST_LEN, scratch + 5 * DIGEST_LEN, scratch + 6 * DIGEST_LEN)

    # poseidon16_compress_half: only first 4 FE constrained
    full_out = scratch + 6 * DIGEST_LEN
    half_out = scratch + 80
    poseidon16_compress_half(scratch + 4 * DIGEST_LEN, scratch + 5 * DIGEST_LEN, half_out)
    for i in unroll(0, HALF_DIGEST_LEN):
        assert full_out[i] == half_out[i]

    # poseidon16_compress_hardcoded_left: the 4-element prefix lives at a compile-time
    # constant memory offset. Public input is the only region with such addresses, so we
    # place the prefix at public_input[0..4] (= memory address 0..4) and pass offset 0.
    hardcoded_left = scratch + 1496
    hardcoded_full_out = scratch + 1504
    poseidon16_compress_hardcoded_left(
        hardcoded_left,
        scratch + 5 * DIGEST_LEN,
        hardcoded_full_out,
        0
    )

    # Same, but only first 4 FE of the output are constrained.
    hardcoded_half_out = scratch + 1512
    poseidon16_compress_half_hardcoded_left(
        hardcoded_left,
        scratch + 5 * DIGEST_LEN,
        hardcoded_half_out,
        0
    )
    for i in unroll(0, HALF_DIGEST_LEN):
        assert hardcoded_full_out[i] == hardcoded_half_out[i]

    # poseidon16_permute: full 16-element permutation (no feed-forward), written in natural order:
    #   m[res .. res + 16] = poseidon(left || right)
    permute_out = scratch + 1600
    poseidon16_permute(scratch + 4 * DIGEST_LEN, scratch + 5 * DIGEST_LEN, permute_out)

    base_ptr = scratch + 88
    ext_a_ptr = scratch + 88 + N
    ext_b_ptr = scratch + 88 + N * (DIM + 1)

    # dot_product_be: sum_i base[i] * ext_a[i]
    dot_product_be(base_ptr, ext_a_ptr, scratch + 1000, N)

    # dot_product_ee: sum_i ext_a[i] * ext_b[i]
    dot_product_ee(ext_a_ptr, ext_b_ptr, scratch + 1000 + DIM, N)

    # add_be: sum_i (base[i] + ext_a[i])
    add_be(base_ptr, ext_a_ptr, scratch + 1200, N)

    # add_ee: sum_i (ext_a[i] + ext_b[i])
    add_ee(ext_a_ptr, ext_b_ptr, scratch + 1200 + DIM, N)

    # poly_eq_be: prod_i (a[i]*b[i] + (1-a[i])*(1-b[i])) with base a, ext b
    slice_a_ptr = scratch + 1100
    slice_b_ptr = scratch + 1100 + M
    poly_eq_be(slice_a_ptr, slice_b_ptr, scratch + 1100 + M + M * DIM, M)

    # poly_eq_ee: prod_i (a[i]*b[i] + (1-a[i])*(1-b[i])) with ext a, ext b
    poly_eq_ee(ext_a_ptr, ext_b_ptr, scratch + 1300, N)

    c: Mut = 0
    for i in range(0, LOOP_ITERS):
        c += 1
    assert c == LOOP_ITERS

    return
"#;

fn all_precompiles_flags(loop_iters: usize) -> CompilationFlags {
    CompilationFlags {
        replacements: BTreeMap::from([("LOOP_ITERS_PLACEHOLDER".to_string(), loop_iters.to_string())]),
    }
}

fn all_precompiles_witness() -> (Vec<F>, ExecutionWitness) {
    let mut rng = StdRng::seed_from_u64(0);
    let mut scratch = F::zero_vec(8192);

    // Poseidon test data
    let poseidon_16_compress_input: [F; 16] = rng.random();
    scratch[32..48].copy_from_slice(&poseidon_16_compress_input);
    let poseidon_output = poseidon16_compress(poseidon_16_compress_input);
    scratch[48..56].copy_from_slice(&poseidon_output[..8]);
    let poseidon_24_input: [F; 24] = rng.random();
    scratch[56..80].copy_from_slice(&poseidon_24_input);
    // poseidon16_compress_half output at offset 80: first 4 = hash, last 4 = arbitrary pre-existing data
    scratch[80..84].copy_from_slice(&poseidon_output[..4]);
    scratch[84..88].copy_from_slice(&[
        F::from_usize(111),
        F::from_usize(222),
        F::from_usize(333),
        F::from_usize(444),
    ]);

    // poseidon16_compress_hardcoded_left: prefix lives at public_input[0..4] (compile-time
    // constant offset 0), data at scratch[1496..1500], expected output at scratch[1504..1512].
    let hardcoded_prefix: [F; 4] = rng.random();
    let hardcoded_data: [F; 4] = rng.random();
    scratch[1496..1500].copy_from_slice(&hardcoded_data);
    let mut hardcoded_input = [F::ZERO; 16];
    hardcoded_input[..4].copy_from_slice(&hardcoded_prefix);
    hardcoded_input[4..8].copy_from_slice(&hardcoded_data);
    hardcoded_input[8..16].copy_from_slice(&poseidon_16_compress_input[8..16]);
    let hardcoded_output = poseidon16_compress(hardcoded_input);
    scratch[1504..1512].copy_from_slice(&hardcoded_output);
    // half output: first 4 = hash, last 4 = arbitrary pre-existing data
    scratch[1512..1516].copy_from_slice(&hardcoded_output[..4]);
    scratch[1516..1520].copy_from_slice(&[
        F::from_usize(555),
        F::from_usize(666),
        F::from_usize(777),
        F::from_usize(888),
    ]);

    // poseidon16_permute output at 1600..1616: raw permutation result.
    let permute_output = poseidon16_permute(poseidon_16_compress_input);
    scratch[1600..1616].copy_from_slice(&permute_output);

    // Extension op operands: base[N], ext_a[N], ext_b[N]
    let base_slice: [F; N] = rng.random();
    let ext_a_slice: [EF; N] = rng.random();
    let ext_b_slice: [EF; N] = rng.random();

    let ef_to_f = |slice: &[EF]| -> Vec<F> {
        slice
            .iter()
            .flat_map(|x| x.as_basis_coefficients_slice().to_vec())
            .collect()
    };

    scratch[88..][..N].copy_from_slice(&base_slice);
    scratch[88 + N..][..N * DIMENSION].copy_from_slice(&ef_to_f(&ext_a_slice));
    scratch[88 + N + N * DIMENSION..][..N * DIMENSION].copy_from_slice(&ef_to_f(&ext_b_slice));

    // dot_product_be result at 1000
    let dot_product_be_result: EF = dot_product(ext_a_slice.into_iter(), base_slice.into_iter());
    scratch[1000..][..DIMENSION].copy_from_slice(dot_product_be_result.as_basis_coefficients_slice());

    // dot_product_ee result at 1005
    let dot_product_ee_result: EF = dot_product(ext_a_slice.into_iter(), ext_b_slice.into_iter());
    scratch[1000 + DIMENSION..][..DIMENSION].copy_from_slice(dot_product_ee_result.as_basis_coefficients_slice());

    // add_be result at 1200: sum_i (EF::from(base[i]) + ext_a[i])
    let add_be_result: EF = (0..N)
        .map(|i| EF::from(base_slice[i]) + ext_a_slice[i])
        .fold(EF::ZERO, |a, b| a + b);
    scratch[1200..][..DIMENSION].copy_from_slice(add_be_result.as_basis_coefficients_slice());

    // add_ee result at 1205: sum_i (ext_a[i] + ext_b[i])
    let add_ee_result: EF = (0..N)
        .map(|i| ext_a_slice[i] + ext_b_slice[i])
        .fold(EF::ZERO, |a, b| a + b);
    scratch[1200 + DIMENSION..][..DIMENSION].copy_from_slice(add_ee_result.as_basis_coefficients_slice());

    // poly_eq_be operands: slice_a[M] (base), slice_b[M] (ext) at 1100
    let slice_a: [F; M] = rng.random();
    let slice_b: [EF; M] = rng.random();
    scratch[1100..][..M].copy_from_slice(&slice_a);
    scratch[1100 + M..][..M * DIMENSION].copy_from_slice(&ef_to_f(&slice_b));

    // poly_eq_be result at 1100 + M + M*DIM = 1118
    let poly_eq_be_result = MultilinearPoint(slice_b.to_vec())
        .eq_poly_outside(&MultilinearPoint(slice_a.iter().map(|&x| EF::from(x)).collect()));
    scratch[1100 + M + M * DIMENSION..][..DIMENSION].copy_from_slice(poly_eq_be_result.as_basis_coefficients_slice());

    // poly_eq_ee result at 1300: prod_i (ext_a[i]*ext_b[i] + (1-ext_a[i])*(1-ext_b[i]))
    let poly_eq_ee_result: EF = (0..N)
        .map(|i| ext_a_slice[i] * ext_b_slice[i] + (EF::ONE - ext_a_slice[i]) * (EF::ONE - ext_b_slice[i]))
        .fold(EF::ONE, |acc, x| acc * x);
    scratch[1300..][..DIMENSION].copy_from_slice(poly_eq_ee_result.as_basis_coefficients_slice());

    let mut public_input = vec![F::ZERO; PUBLIC_INPUT_LEN];
    public_input[..4].copy_from_slice(&hardcoded_prefix);

    let mut hints = std::collections::HashMap::new();
    hints.insert("scratch".to_string(), vec![scratch]);
    let witness = ExecutionWitness {
        hints,
        ..Default::default()
    };
    (public_input, witness)
}

#[test]
fn test_zk_vm_all_precompiles() {
    let (public_input, witness) = all_precompiles_witness();
    test_zk_vm_helper_with_witness(
        ALL_PRECOMPILES_PROGRAM,
        &public_input,
        witness,
        all_precompiles_flags(100),
    );
}

#[test]
#[ignore]
fn dump_test_vector_for_python_verifier() {
    const LOOP_ITERS: usize = 5000;

    let (public_input, witness) = all_precompiles_witness();
    let bytecode = compile_program_with_flags(
        &ProgramSource::Raw(ALL_PRECOMPILES_PROGRAM.to_string()),
        all_precompiles_flags(LOOP_ITERS),
    );
    let exec_proof = prove_execution(&bytecode, &public_input, &witness, &default_whir_config(1), false).unwrap();
    let (_details, raw_proof) = verify_execution(&bytecode, &public_input, exec_proof.proof).unwrap();

    let f_u32 = |x: F| x.as_canonical_u32();
    let out_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(std::env::var("CARGO_TARGET_DIR").unwrap_or_else(|_| "target".into()))
        .join("zkvm_test_vectors");
    std::fs::create_dir_all(&out_dir).unwrap();

    let bytecode_path = "proof.bytecode_mle.bin";
    let mut mle_file = std::fs::File::create(out_dir.join(bytecode_path)).unwrap();
    for v in &bytecode.instructions_multilinear {
        mle_file.write_all(&f_u32(*v).to_le_bytes()).unwrap();
    }

    let opening_json = |o: &MerkleOpening<F>| -> serde_json::Value {
        serde_json::json!({
            "leaf_data": o.leaf_data.iter().map(|&f| f_u32(f)).collect::<Vec<_>>(),
            "path": o.path.iter().map(|d| d.map(f_u32)).collect::<Vec<_>>(),
        })
    };
    let out = serde_json::json!({
        "bytecode_multilinear_path": bytecode_path,
        "public_input": public_input.iter().map(|&f| f_u32(f)).collect::<Vec<_>>(),
        "proof": {
            "transcript": raw_proof.transcript.iter().map(|&f| f_u32(f)).collect::<Vec<_>>(),
            "merkle_openings": raw_proof.merkle_openings.iter().map(opening_json).collect::<Vec<_>>(),
        },
    });
    let json_path = out_dir.join("proof.json");
    std::fs::write(&json_path, serde_json::to_string(&out).unwrap()).unwrap();

    println!(
        "wrote {} ({:.1} KiB), bytecode_log_size={}",
        json_path.display(),
        json_path.metadata().unwrap().len() as f64 / 1024.0,
        bytecode.log_size(),
    );
}

#[test]
fn test_small_memory() {
    let program_str = r#"
def main():
    a = Array(1)
    for i in unroll(0, 2**17):
        a[0] = 1 * 2
    return
"#;

    test_zk_vm_helper(program_str, &[F::ZERO; PUBLIC_INPUT_LEN]);
}

#[test]
fn test_prove_fibonacci() {
    if std::env::var("FIB_TRACING") == Ok("true".to_string()) {
        init_tracing();
    }
    let n = std::env::var("FIB_N")
        .unwrap_or("10000".to_string())
        .parse::<usize>()
        .unwrap();
    let program_str = r#"
N = FIB_N_PLACEHOLDER
STEPS = 10000  # N should be a multiple of STEPS
N_STEPS = N / STEPS

def main():
    x, y = fibonacci_step(0, 1, N_STEPS)
    print(x)
    return

def fibonacci_step(a, b, steps_remaining):
    if steps_remaining == 0:
        return a, b
    new_a, new_b = fibonacci_const(a, b, STEPS)
    res_a, res_b = fibonacci_step(new_a, new_b, steps_remaining - 1)
    return res_a, res_b

def fibonacci_const(a, b, n: Const):
    buff = Array(n + 2)
    buff[0] = a
    buff[1] = b
    for j in unroll(2, n + 2):
        buff[j] = buff[j - 1] + buff[j - 2]
    return buff[n], buff[n + 1]
"#;
    let flags = CompilationFlags {
        replacements: [("FIB_N_PLACEHOLDER".to_string(), n.to_string())].into_iter().collect(),
    };
    test_zk_vm_helper_with_witness(
        program_str,
        &[F::ZERO; PUBLIC_INPUT_LEN],
        ExecutionWitness::default(),
        flags,
    );
}

fn test_zk_vm_helper(program_str: &str, public_input: &[F]) {
    test_zk_vm_helper_with_witness(
        program_str,
        public_input,
        ExecutionWitness::default(),
        CompilationFlags::default(),
    )
}

fn test_zk_vm_helper_with_witness(
    program_str: &str,
    public_input: &[F],
    witness: ExecutionWitness,
    flags: CompilationFlags,
) {
    utils::init_tracing();
    let bytecode = compile_program_with_flags(&ProgramSource::Raw(program_str.to_string()), flags);
    let time = std::time::Instant::now();
    let starting_log_inv_rate = 1;
    let proof = prove_execution(
        &bytecode,
        public_input,
        &witness,
        &default_whir_config(starting_log_inv_rate),
        false,
    )
    .unwrap();
    let proof_time = time.elapsed();
    verify_execution(&bytecode, public_input, proof.proof).unwrap();
    println!("{}", proof.metadata.as_ref().unwrap().display());
    println!("Proof time: {:.3} s", proof_time.as_secs_f32());
}
