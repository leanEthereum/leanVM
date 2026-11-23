//! The stable prover and the experimental one, in every CPU tier this machine runs, give the same proof of the same
//! statement, byte for byte: three leaves
//! (leanXMSS signatures and blobs, leanSPHINCS signatures, both schemes and blobs, with enough signatures of each that
//! experimental runs both signature loops as parallel segments), a recursion node over them, at the four rates, and a
//! second-level node over that node, a leaf and a raw signature; the same refusal of a forged signature the native
//! pre-check misses; and every compiler test program, or the same refusal. Both trees' thread pools live in this one
//! process, and libtest may run the two tests at once: both pools can then be busy together, and either can take
//! dispatches from both tests, which its dispatch lock serializes.

use aggregation::{AggregateClaims, AggregateError, AggregateProof, OutputClaims, signers_cache};
use experimental_dispatch::{__TierVisitor, __for_each_tier, Tier};
use isa::{Program, Prover};
use stable_lean_vm_core::StableProver;
use verifier::E;

/// The proofs `P` gives, the three leaves', the node's and the second-level node's, then why it refuses a
/// forged signature.
fn proofs<P: Prover>() -> ([Vec<u8>; 5], Option<AggregateError>) {
    P::init();
    let aggregate = |children: &[(AggregateClaims, AggregateProof)], xmss, sphincs, blobs, rate| {
        aggregation::aggregate::<P>(children, xmss, sphincs, blobs, OutputClaims::All, rate).map(|(c, p, _)| (c, p))
    };
    let symbols: Vec<u128> = (0..2 * lean_da::BLOB_SYMBOLS as u128)
        .map(|i| i.wrapping_mul(0x9e37_79b9_7f4a_7c15))
        .collect();
    let blobs = lean_da::BlobMatrix::build(symbols.as_chunks().0).unwrap();
    let (xmss, sphincs) = (
        signers_cache::get_signers::<P>(23),
        signers_cache::get_lean_sphincs_signers::<P>(20),
    );
    let left = aggregate(&[], xmss[..3].to_vec(), vec![], Some(&blobs), 1).unwrap();
    let right = aggregate(&[], vec![], sphincs[..1].to_vec(), None, 2).unwrap();
    let mixed = aggregate(&[], xmss[3..22].to_vec(), sphincs[1..].to_vec(), Some(&blobs), 3).unwrap();
    let children = [left.clone(), right.clone(), mixed.clone()];
    let node = aggregate(&children, vec![], vec![], None, 4).unwrap();
    // The node's carried deferred claim is at a non-zero point, unlike a leaf's.
    let children = [node.clone(), right.clone()];
    let top = aggregate(&children, xmss[22..].to_vec(), vec![], None, 1).unwrap();
    // A leanXMSS signature with its top layer's last path node changed: the native pre-check passes, the guest fails.
    let (pk, message, signature) = &xmss[0];
    let mut bytes = signature.to_bytes();
    bytes[lean_xmss::SIG_SIZE - 1] ^= 1;
    let forged = vec![(*pk, *message, lean_xmss::LeanXmssSignature::from_bytes(&bytes))];
    let refusal = aggregate(&[], forged, vec![], None, 1).err();
    (
        [left, right, mixed, node, top].map(|(_, proof)| proof.to_bytes()),
        refusal,
    )
}

#[test]
fn stable_and_experimental_proofs_are_identical() {
    struct Matches(([Vec<u8>; 5], Option<AggregateError>));
    impl __TierVisitor for Matches {
        fn visit<P: Prover>(&mut self, tier: Tier) {
            let ((experimental, experimental_refusal), (stable, stable_refusal)) = (proofs::<P>(), &self.0);
            for (name, (e, s)) in ["left leaf", "right leaf", "mixed leaf", "node", "second-level node"]
                .iter()
                .zip(experimental.iter().zip(stable))
            {
                assert!(
                    e == s,
                    "{tier:?}: the {name}'s proofs differ ({} and {} bytes)",
                    e.len(),
                    s.len()
                );
            }
            assert_eq!(&experimental_refusal, stable_refusal, "{tier:?}");
        }
    }
    let stable = proofs::<StableProver>();
    assert_eq!(stable.1, Some(AggregateError::ProvingFailed));
    __for_each_tier(&mut Matches(stable));
}

/// A compiler test program, its inputs and a rate.
struct Case {
    path: std::path::PathBuf,
    program: Program,
    public_input: [E; 2],
    witness: Vec<(String, Vec<Vec<E>>)>,
    log_inv_rate: usize,
    /// Whether `public_input` is the annotated one, so that a proof exists.
    annotated: bool,
}

/// Each case's proof by `P`, or why there is none.
fn case_proofs<P: Prover>(cases: &[Case]) -> Vec<Result<verifier::Proof, String>> {
    P::init();
    cases
        .iter()
        .map(|case| {
            P::prove(&case.program, &case.witness, case.public_input, case.log_inv_rate).map(|(proof, _)| proof)
        })
        .collect()
}

/// The compiler suite runs on stable alone; this runs its programs, with their annotated inputs (`# public_input:`,
/// `# witness name:`) and with a wrong public input, through experimental's interpreter and hints too, at every rate.
#[test]
fn compiler_programs_prove_identically() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../crates/zkdsl_compiler/tests/programs");
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
    let mut cases = Vec::new();
    for path in paths {
        let src = std::fs::read_to_string(&path).unwrap();
        let compiled = zkdsl_compiler::compile(&zkdsl_compiler::parse(&src).unwrap());
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
        for (input, log_inv_rate) in (1..=4).map(|rate| (public_input, rate)).chain([(wrong, 1)]) {
            cases.push(Case {
                path: path.clone(),
                program: Program::from(compiled.clone()),
                public_input: input,
                witness: witness.clone(),
                log_inv_rate,
                annotated: input == public_input,
            });
        }
    }
    let stable = case_proofs::<StableProver>(&cases);
    for (case, proof) in cases.iter().zip(&stable) {
        assert!(
            !case.annotated || proof.is_ok(),
            "{}: {:?}",
            case.path.display(),
            proof.as_ref().err()
        );
    }
    struct Matches<'a>(&'a [Case], Vec<Result<verifier::Proof, String>>);
    impl __TierVisitor for Matches<'_> {
        fn visit<P: Prover>(&mut self, tier: Tier) {
            for ((case, proof), stable) in self.0.iter().zip(case_proofs::<P>(self.0)).zip(&self.1) {
                let (path, rate) = (case.path.display(), case.log_inv_rate);
                assert!(
                    proof == *stable,
                    "{tier:?}: {path} at rate {rate}: the provers disagree"
                );
            }
        }
    }
    __for_each_tier(&mut Matches(&cases, stable));
}
