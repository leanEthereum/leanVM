//! The stable and the experimental prover give the same proof of the same statement, byte for byte: three leaves (leanXMSS
//! signatures and blobs, leanSPHINCS signatures, both schemes and blobs) and a recursion node over them, at the four
//! rates; and every compiler test program, or the same refusal. Both trees' thread pools run in this one process, each
//! idle while the other proves.

use aggregation::{OutputClaims, aggregate, signers_cache};
use experimental_leanvm_core::ExperimentalProver;
use isa::{CompiledProgram, Prover};
use stable_leanvm_core::StableProver;
use verifier::E;

/// The proofs `P` gives: the three leaves', then the node's.
fn proofs<P: Prover>() -> [Vec<u8>; 4] {
    P::init();
    let symbols: Vec<u128> = (0..2 * lean_da::BLOB_SYMBOLS as u128)
        .map(|i| i.wrapping_mul(0x9e37_79b9_7f4a_7c15))
        .collect();
    let blobs = lean_da::BlobMatrix::build(symbols.as_chunks().0).unwrap();
    let (xmss, sphincs) = (
        signers_cache::get_signers(5),
        signers_cache::get_lean_sphincs_signers(2),
    );
    let left = aggregate::<P>(&[], xmss[..3].to_vec(), vec![], Some(&blobs), OutputClaims::All, 1).unwrap();
    let right = aggregate::<P>(&[], vec![], sphincs[..1].to_vec(), None, OutputClaims::All, 2).unwrap();
    let mixed = aggregate::<P>(
        &[],
        xmss[3..].to_vec(),
        sphincs[1..].to_vec(),
        Some(&blobs),
        OutputClaims::All,
        3,
    )
    .unwrap();
    let children = [left.clone(), right.clone(), mixed.clone()];
    let node = aggregate::<P>(&children, vec![], vec![], None, OutputClaims::All, 4).unwrap();
    [left, right, mixed, node].map(|(_, proof)| proof.to_bytes())
}

#[test]
fn stable_and_experimental_proofs_are_identical() {
    let (experimental, stable) = (proofs::<ExperimentalProver>(), proofs::<StableProver>());
    for (name, (e, s)) in ["left leaf", "right leaf", "mixed leaf", "node"]
        .iter()
        .zip(experimental.iter().zip(&stable))
    {
        assert!(e == s, "the {name}'s proofs differ ({} and {} bytes)", e.len(), s.len());
    }
}

/// `program`'s proof at rate 1 on `public_input`, or why there is none.
fn prove<P: Prover>(
    program: &CompiledProgram,
    public_input: [E; 2],
    witness: &[(String, Vec<Vec<E>>)],
) -> Result<verifier::Proof, String> {
    P::init();
    let mut program = P::assemble(program.clone());
    for (name, entries) in witness {
        P::set_witness(&mut program, name, entries.clone());
    }
    P::prove(&program, public_input, 1).map(|(proof, _)| proof)
}

/// The compiler suite runs on stable alone; this runs its programs, with their annotated inputs (`# public_input:`,
/// `# witness name:`) and with a wrong public input, through experimental's interpreter and hints too.
#[test]
fn compiler_programs_prove_identically() {
    let dir = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../crates/zkdsl_compiler/tests/programs"
    );
    let mut paths: Vec<_> = std::fs::read_dir(dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect();
    paths.retain(|path| path.extension().is_some_and(|ext| ext == "py"));
    paths.sort();
    assert!(!paths.is_empty());
    let constants = |values: &str| -> Vec<E> {
        values
            .split(',')
            .map(|v| zkdsl_compiler::parse_const(v).unwrap())
            .collect()
    };
    for path in paths {
        let src = std::fs::read_to_string(&path).unwrap();
        let program = zkdsl_compiler::compile(&zkdsl_compiler::parse(&src).unwrap());
        let annotation = |tag: &'static str| src.lines().filter_map(move |line| line.trim().strip_prefix(tag));
        let public_input = annotation("# public_input:")
            .next()
            .map_or([E::new(0, 0); 2], |v| constants(v).try_into().unwrap());
        // Each line is the next entry of its stream.
        let mut witness: Vec<(String, Vec<Vec<E>>)> = Vec::new();
        for (name, values) in annotation("# witness ").map(|rest| rest.split_once(':').unwrap()) {
            match witness.iter_mut().find(|(stream, _)| stream == name.trim()) {
                Some((_, entries)) => entries.push(constants(values)),
                None => witness.push((name.trim().to_string(), vec![constants(values)])),
            }
        }
        let wrong = [public_input[0] + E::new(1, 0), public_input[1]];
        for (input, annotated) in [(public_input, true), (wrong, false)] {
            let (experimental, stable) = (
                prove::<ExperimentalProver>(&program, input, &witness),
                prove::<StableProver>(&program, input, &witness),
            );
            assert!(experimental == stable, "{}: the provers disagree", path.display());
            assert!(!annotated || stable.is_ok(), "{}: {:?}", path.display(), stable.err());
        }
    }
}
