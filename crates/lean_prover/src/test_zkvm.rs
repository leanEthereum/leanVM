use std::collections::BTreeMap;

use crate::{default_whir_config, prove_execution::prove_execution, verify_execution::verify_execution};
use backend::*;
use lean_compiler::*;
use lean_vm::*;
use rand::{RngExt, SeedableRng, rngs::StdRng};

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
N_POSEIDON = N_POSEIDON_PLACEHOLDER
EXT_LEN = EXT_LEN_PLACEHOLDER
BYTECODE_PAD = BYTECODE_PAD_PLACEHOLDER

def main():
    scratch = Array(SCRATCH_SIZE)
    hint_witness("scratch", scratch)
    poseidon16_compress_half(scratch + 4 * DIGEST_LEN, scratch + 5 * DIGEST_LEN, scratch + 6 * DIGEST_LEN)

    # poseidon16_compress_quarter: only first 4 FE constrained
    full_out = scratch + 6 * DIGEST_LEN
    half_out = scratch + 80
    poseidon16_compress_quarter(scratch + 4 * DIGEST_LEN, scratch + 5 * DIGEST_LEN, half_out)
    for i in unroll(0, HALF_DIGEST_LEN):
        assert full_out[i] == half_out[i]

    # poseidon16_compress_half_hardcoded_left: the 4-element prefix lives at a compile-time
    # constant memory offset. Public input is the only region with such addresses, so we
    # place the prefix at public_input[0..4] (= memory address 0..4) and pass offset 0.
    hardcoded_left = scratch + 1496
    hardcoded_full_out = scratch + 1504
    poseidon16_compress_half_hardcoded_left(
        hardcoded_left,
        scratch + 5 * DIGEST_LEN,
        hardcoded_full_out,
        0
    )

    # Same, but only first 4 FE of the output are constrained.
    hardcoded_half_out = scratch + 1512
    poseidon16_compress_quarter_hardcoded_left(
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

    # poseidon16_permute_half: same permutation, but only the low 8 elements are written/constrained.
    permute_half_out = scratch + 1620
    poseidon16_permute_half(scratch + 4 * DIGEST_LEN, scratch + 5 * DIGEST_LEN, permute_half_out)
    for i in unroll(0, DIGEST_LEN):
        assert permute_half_out[i] == permute_out[i]

    # poseidon16_permute_half_hardcoded_left: permutation (low 8) with a hardcoded 4-element left prefix.
    # Uses the same input as the hardcoded compression above, so it equals the permutation of that input.
    permute_hardcoded_out = scratch + 1640
    poseidon16_permute_half_hardcoded_left(hardcoded_left, scratch + 5 * DIGEST_LEN, permute_hardcoded_out, 0)

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

    # execution table: a runtime loop (one code copy, LOOP_ITERS cycles).
    c_buf = Array(LOOP_ITERS + 1)
    c_buf[0] = 0
    for i in range(0, LOOP_ITERS):
        c_buf[i + 1] = c_buf[i] + 1
    assert c_buf[LOOP_ITERS] == LOOP_ITERS

    # bytecode size: a dead unrolled block (runtime_zero() is a real call, so the branch can't be folded).
    if runtime_zero() == 1:
        pad = Array(BYTECODE_PAD + 1)
        pad[0] = 1
        for j in unroll(0, BYTECODE_PAD):
            pad[j + 1] = pad[j] + 1

    # poseidon table: a runtime loop of N_POSEIDON poseidon calls (outputs left unread).
    pos_src = Array(16)
    hint_witness("pos_src", pos_src)
    pos_out = Array(N_POSEIDON * 8 + 16)
    for i in range(0, N_POSEIDON):
        poseidon16_permute_half(pos_src, pos_src + 8, pos_out + i * 8)

    # extension table: a single EXT_LEN-long dot product (output left unread too).
    big_a = Array(EXT_LEN * DIM)
    hint_witness("ext_a", big_a)
    big_b = Array(EXT_LEN * DIM)
    hint_witness("ext_b", big_b)
    big_res = Array(DIM)
    dot_product_ee(big_a, big_b, big_res, EXT_LEN)
    return

def runtime_zero():
    return 0
"#;

fn sweep_flags(loop_iters: usize, n_poseidon: usize, ext_len: usize, bytecode_pad: usize) -> CompilationFlags {
    let knobs = [
        ("LOOP_ITERS", loop_iters),
        ("N_POSEIDON", n_poseidon),
        ("EXT_LEN", ext_len),
        ("BYTECODE_PAD", bytecode_pad),
    ];
    CompilationFlags {
        replacements: BTreeMap::from(knobs.map(|(k, v)| (format!("{k}_PLACEHOLDER"), v.to_string()))),
    }
}

fn all_precompiles_witness(ext_len: usize) -> ([F; PUBLIC_INPUT_LEN], ExecutionWitness) {
    let mut rng = StdRng::seed_from_u64(0);
    let mut scratch = F::zero_vec(8192);

    // Poseidon test data
    let poseidon_16_compress_input: [F; 16] = rng.random();
    scratch[32..48].copy_from_slice(&poseidon_16_compress_input);
    let poseidon_output = poseidon16_compress(poseidon_16_compress_input);
    scratch[48..56].copy_from_slice(&poseidon_output[..8]);
    let poseidon_24_input: [F; 24] = rng.random();
    scratch[56..80].copy_from_slice(&poseidon_24_input);
    // poseidon16_compress_quarter output at offset 80: first 4 = hash, last 4 = arbitrary pre-existing data
    scratch[80..84].copy_from_slice(&poseidon_output[..4]);
    scratch[84..88].copy_from_slice(&[
        F::from_usize(111),
        F::from_usize(222),
        F::from_usize(333),
        F::from_usize(444),
    ]);

    // poseidon16_compress_half_hardcoded_left: prefix lives at public_input[0..4] (compile-time
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

    // poseidon16_permute_half output at 1620..1628: low 8 of the same permutation.
    scratch[1620..1628].copy_from_slice(&permute_output[..8]);

    // poseidon16_permute_half_hardcoded_left output at 1640..1648: low 8 of the permutation of the
    // hardcoded-left input (same input as the hardcoded compression above).
    let permute_hardcoded_output = poseidon16_permute(hardcoded_input);
    scratch[1640..1648].copy_from_slice(&permute_hardcoded_output[..8]);

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

    let mut public_input = [F::ZERO; PUBLIC_INPUT_LEN];
    public_input[..4].copy_from_slice(&hardcoded_prefix);

    let pos_src: [F; 16] = rng.random();
    let ext_vec = |rng: &mut StdRng| ef_to_f(&(0..ext_len).map(|_| rng.random()).collect::<Vec<EF>>());
    let hints = std::collections::HashMap::from([
        ("scratch".to_string(), vec![scratch]),
        ("pos_src".to_string(), vec![pos_src.to_vec()]),
        ("ext_a".to_string(), vec![ext_vec(&mut rng)]),
        ("ext_b".to_string(), vec![ext_vec(&mut rng)]),
    ]);
    let witness = ExecutionWitness {
        hints,
        ..Default::default()
    };
    (public_input, witness)
}

#[test]
fn test_zk_vm_all_precompiles() {
    // Exercises every precompile variant; the sweep knobs are kept small so it stays fast.
    let ext_len = 2;
    let (public_input, witness) = all_precompiles_witness(ext_len);
    test_zk_vm_helper_with_witness(
        ALL_PRECOMPILES_PROGRAM,
        &public_input,
        witness,
        sweep_flags(100, 2, ext_len, 4),
    );
}

// Python-verifier test vectors: compile ALL_PRECOMPILES_PROGRAM with different runtime flavours (table sizes, etc)

/// One flavour: (loop_iters, n_poseidon, ext_len, bytecode_pad, log_inv_rate).
type SweepConfig = (usize, usize, usize, usize, usize);

fn dump_vector(
    out_dir: &std::path::Path,
    index: usize,
    &(loop_iters, n_poseidon, ext_len, bytecode_pad, rate): &SweepConfig,
) -> serde_json::Value {
    let bytecode = compile_program_with_flags(
        &ProgramSource::Raw(ALL_PRECOMPILES_PROGRAM.to_string()),
        sweep_flags(loop_iters, n_poseidon, ext_len, bytecode_pad),
    );
    let (public_input, witness) = all_precompiles_witness(ext_len);
    let proof = prove_execution(&bytecode, &public_input, &witness, &default_whir_config(rate), false)
        .unwrap()
        .proof;
    let (_details, raw) = verify_execution(&bytecode, &public_input, proof).unwrap();

    let f = |x: F| x.as_canonical_u32();
    let fe = |xs: &[F]| xs.iter().map(|&x| f(x)).collect::<Vec<_>>();
    let dir = out_dir.join(index.to_string());
    std::fs::create_dir_all(&dir).unwrap();
    let mle: Vec<u8> = bytecode
        .instructions_multilinear
        .iter()
        .flat_map(|&v| f(v).to_le_bytes())
        .collect();
    std::fs::write(dir.join("proof.bytecode_mle.bin"), mle).unwrap();
    let opening = |o: &MerkleOpening<F>| serde_json::json!({ "leaf_data": fe(&o.leaf_data), "path": o.path.iter().map(|d| d.map(f)).collect::<Vec<_>>() });
    let proof_json = serde_json::json!({
        "bytecode_multilinear_path": "proof.bytecode_mle.bin",
        "public_input": fe(&public_input),
        "proof": { "transcript": fe(&raw.transcript), "merkle_openings": raw.merkle_openings.iter().map(opening).collect::<Vec<_>>() },
    });
    std::fs::write(dir.join("proof.json"), serde_json::to_string(&proof_json).unwrap()).unwrap();

    // The proof opens with [log_inv_rate, log_memory, <log-height per table, in ALL_TABLES order>].
    let dims: Vec<usize> = raw.transcript[..2 + N_TABLES]
        .iter()
        .map(|x| x.as_canonical_u32() as usize)
        .collect();
    let heights: serde_json::Map<_, _> = ALL_TABLES
        .iter()
        .enumerate()
        .map(|(i, t)| (t.name().to_string(), dims[2 + i].into()))
        .collect();
    serde_json::json!({
        "dir": index.to_string(), "log_inv_rate": dims[0], "log_memory": dims[1],
        "bytecode_log_size": bytecode.log_size(), "table_log_heights": heights,
    })
}

#[test]
#[ignore]
fn dump_test_vectors_for_python_verifier() {
    let out_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(std::env::var("CARGO_TARGET_DIR").unwrap_or_else(|_| "target".into()))
        .join("zkvm_test_vectors");
    let _ = std::fs::remove_dir_all(&out_dir);
    std::fs::create_dir_all(&out_dir).unwrap();

    #[rustfmt::skip]
    let configs: [SweepConfig; 5] = [
        (5000, 0,    2,     0,    1), // execution-table dominant
        (2,    0,    2,     4000, 2), // bytecode dominant
        (0,    6000, 2,     0,    3), // poseidon-table heavy
        (0,    0,    30000, 0,    1), // extension-table dominant
        (2000, 200,  100,   300,  4), // mixed
    ];
    let vectors: Vec<_> = configs
        .iter()
        .enumerate()
        .map(|(i, cfg)| dump_vector(&out_dir, i, cfg))
        .collect();
    let manifest = serde_json::json!({ "vectors": vectors });
    std::fs::write(
        out_dir.join("manifest.json"),
        serde_json::to_string_pretty(&manifest).unwrap(),
    )
    .unwrap();
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

    test_zk_vm_helper(program_str, &Default::default());
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
    test_zk_vm_helper_with_witness(program_str, &Default::default(), ExecutionWitness::default(), flags);
}

fn test_zk_vm_helper(program_str: &str, public_input: &[F; PUBLIC_INPUT_LEN]) {
    test_zk_vm_helper_with_witness(
        program_str,
        public_input,
        ExecutionWitness::default(),
        CompilationFlags::default(),
    )
}

fn test_zk_vm_helper_with_witness(
    program_str: &str,
    public_input: &[F; PUBLIC_INPUT_LEN],
    witness: ExecutionWitness,
    flags: CompilationFlags,
) {
    init_tracing();
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
