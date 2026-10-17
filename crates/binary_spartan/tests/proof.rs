//! End-to-end tests on random satisfied blocks: honest proofs verify in both modes, and a changed statement, a
//! mutated proof or an unsatisfied witness is rejected.

use binary_spartan::block::BlockR1cs;
use binary_spartan::format::{Constraint, FormatError, R1csFile, WitnessFile};
use binary_spartan::proof::{self, Mode, Proof, ProveError};
use binary_spartan::spark;
use primitives::test_rng::Rng;
use verifier::VerifierError;

/// A random circuit and a satisfying batch. Signals: the constant, `n_public` public inputs, `n_free` free private
/// signals, then one output per constraint. Constraint `r` reads random earlier signals on A and B, and its C side
/// is its own output plus random earlier signals, so evaluating the constraints in order satisfies them all.
struct Case {
    file: R1csFile,
    block: BlockR1cs,
    batch: WitnessFile,
}

fn subset(rng: &mut Rng, below: u32, max_len: u32) -> Vec<u32> {
    let len = rng.next_u32() % (max_len + 1);
    let mut s: Vec<u32> = (0..len).map(|_| rng.next_u32() % below).collect();
    s.sort_unstable();
    s.dedup();
    s
}

fn random_case(seed: u64, n_public: usize, n_free: usize, n_constraints: usize, n_instances: usize) -> Case {
    let mut rng = Rng::new(seed);
    let first_output = 1 + n_public + n_free;
    let n_signals = first_output + n_constraints;
    let constraints: Vec<Constraint> = (0..n_constraints)
        .map(|r| {
            let out = (first_output + r) as u32;
            let mut c = subset(&mut rng, out, 2);
            c.push(out);
            Constraint {
                a: subset(&mut rng, out, 3),
                b: subset(&mut rng, out, 3),
                c,
            }
        })
        .collect();
    let file = R1csFile {
        n_signals,
        n_public,
        constraints,
    };
    let width = n_signals.div_ceil(8);
    let mut data = vec![0u8; width * n_instances];
    for row in data.chunks_exact_mut(width) {
        let mut z = vec![false; n_signals];
        z[0] = true;
        for v in &mut z[1..first_output] {
            *v = rng.bit();
        }
        let parity = |z: &[bool], s: &[u32]| s.iter().fold(false, |acc, &j| acc ^ z[j as usize]);
        for (r, constraint) in file.constraints.iter().enumerate() {
            let out = first_output + r;
            let rest = &constraint.c[..constraint.c.len() - 1];
            z[out] = (parity(&z, &constraint.a) & parity(&z, &constraint.b)) ^ parity(&z, rest);
        }
        for (j, &v) in z.iter().enumerate() {
            row[j / 8] |= u8::from(v) << (j % 8);
        }
    }
    let batch = WitnessFile {
        n_signals,
        n_instances,
        data,
    };
    let block = BlockR1cs::new(&file).expect("valid block");
    Case { file, block, batch }
}

fn roundtrip(case: &Case) {
    let publics = proof::publics(&case.block, &case.batch);
    let p = proof::prove(&case.block, &case.batch, Mode::Direct).expect("satisfied");
    proof::verify(&case.block, &publics, &p, Mode::Direct).expect("direct proof verifies");

    let pk = spark::preprocess(&case.block.matrices, proof::LOG_INV_RATE);
    let p = proof::prove(&case.block, &case.batch, Mode::Spark(&pk)).expect("satisfied");
    proof::verify(&case.block, &publics, &p, Mode::Spark(&pk.verifier_key())).expect("SPARK proof verifies");
}

#[test]
fn honest_batches_verify_in_both_modes() {
    // One instance, a public region of two words, the smallest block.
    roundtrip(&random_case(1, 70, 10, 40, 1));
    // A batch that is not a power of two, so the padding instances repeat the last one.
    roundtrip(&random_case(2, 30, 40, 300, 5));
}

#[test]
fn honest_large_batch_verifies_in_both_modes() {
    // BLAKE2s-sized public region, k_log = 12, 2^6 instances.
    let case = random_case(3, 1024, 200, 2800, 64);
    assert_eq!(case.block.k_log(), 12);
    roundtrip(&case);
}

#[test]
fn rejects_changed_publics() {
    let case = random_case(4, 100, 30, 200, 6);
    let p = proof::prove(&case.block, &case.batch, Mode::Direct).expect("satisfied");
    let publics = proof::publics(&case.block, &case.batch);
    let pw = case.block.public_words();
    // A public bit of the first and of the last real instance, in both public words.
    for (instance, signal) in [(0, 1), (0, 70), (5, 3), (5, 100)] {
        let mut bad = publics.clone();
        bad[instance * pw + signal / 64] ^= 1 << (signal % 64);
        assert!(
            proof::verify(&case.block, &bad, &p, Mode::Direct).is_err(),
            "{instance}/{signal}"
        );
    }
    // The constant and the zero padding of the public region.
    for signal in [0, 101] {
        let mut bad = publics.clone();
        bad[signal / 64] ^= 1 << (signal % 64);
        assert_eq!(
            proof::verify(&case.block, &bad, &p, Mode::Direct),
            Err(VerifierError::PublicWords)
        );
    }
    // A different instance count.
    let mut fewer = publics.clone();
    fewer.truncate(publics.len() - pw);
    assert!(proof::verify(&case.block, &fewer, &p, Mode::Direct).is_err());
}

#[test]
fn rejects_mutated_proofs() {
    let case = random_case(5, 40, 20, 150, 3);
    let publics = proof::publics(&case.block, &case.batch);
    let pk = spark::preprocess(&case.block.matrices, proof::LOG_INV_RATE);
    let vk = pk.verifier_key();
    for spark_mode in [false, true] {
        let (prove_mode, verify_mode) = if spark_mode {
            (Mode::Spark(&pk), Mode::Spark(&vk))
        } else {
            (Mode::Direct, Mode::Direct)
        };
        let p = proof::prove(&case.block, &case.batch, prove_mode).expect("satisfied");
        let n = p.stream.len();
        for at in [0, 1, n / 4, n / 2, n - 1] {
            let mut bad = p.clone();
            bad.stream[at].c1 ^= 1;
            assert!(
                proof::verify(&case.block, &publics, &bad, verify_mode).is_err(),
                "scalar {at}"
            );
        }
        let bytes = bincode::serialize(&p).expect("serializes");
        for at in [bytes.len() / 3, 2 * bytes.len() / 3, bytes.len() - 1] {
            let mut bad = bytes.clone();
            bad[at] ^= 0x10;
            let rejected = bincode::deserialize::<Proof>(&bad)
                .map_or(true, |q| proof::verify(&case.block, &publics, &q, verify_mode).is_err());
            assert!(rejected, "byte {at}");
        }
        // A proof made in the other mode.
        let other = if spark_mode {
            proof::prove(&case.block, &case.batch, Mode::Direct)
        } else {
            proof::prove(&case.block, &case.batch, Mode::Spark(&pk))
        }
        .expect("satisfied");
        assert!(proof::verify(&case.block, &publics, &other, verify_mode).is_err());
    }
    // A SPARK key preprocessed for another block of the same shape.
    let other = random_case(8, 40, 20, 150, 3);
    let other_vk = spark::preprocess(&other.block.matrices, proof::LOG_INV_RATE).verifier_key();
    assert_eq!(other_vk.nnz_log, vk.nnz_log);
    let p = proof::prove(&case.block, &case.batch, Mode::Spark(&pk)).expect("satisfied");
    assert!(proof::verify(&case.block, &publics, &p, Mode::Spark(&other_vk)).is_err());
}

#[test]
fn prover_refuses_unsatisfied_witness() {
    let mut case = random_case(6, 20, 10, 100, 9);
    // Flip instance 7's output of constraint 30: constraint 30 breaks first.
    let signal = 1 + 20 + 10 + 30;
    let width = case.batch.bytes_per_instance();
    case.batch.data[7 * width + signal / 8] ^= 1 << (signal % 8);
    assert_eq!(
        proof::prove(&case.block, &case.batch, Mode::Direct),
        Err(ProveError::Unsatisfied { instance: 7, row: 30 })
    );
}

#[test]
fn parsers_reject_malformed_files() {
    let case = random_case(7, 10, 5, 20, 2);
    let r1cs = case.file.encode();
    assert_eq!(R1csFile::parse(&r1cs).as_ref(), Ok(&case.file));
    assert_eq!(R1csFile::parse(&r1cs[..r1cs.len() - 1]), Err(FormatError::Truncated));
    let mut long = r1cs.clone();
    long.push(0);
    assert_eq!(R1csFile::parse(&long), Err(FormatError::TrailingBytes));
    let mut swapped = case.file.clone();
    swapped.constraints[3].c = vec![9, 2];
    assert_eq!(
        R1csFile::parse(&swapped.encode()),
        Err(FormatError::NotIncreasing { constraint: 3 })
    );
    let mut repeated = case.file.clone();
    repeated.constraints[4].a = vec![2, 2];
    assert_eq!(
        R1csFile::parse(&repeated.encode()),
        Err(FormatError::NotIncreasing { constraint: 4 })
    );
    let mut out_of_range = case.file.clone();
    out_of_range.constraints[5].b = vec![case.file.n_signals as u32];
    assert!(matches!(
        R1csFile::parse(&out_of_range.encode()),
        Err(FormatError::SignalOutOfRange { constraint: 5, .. })
    ));

    let witness = case.batch.encode();
    assert_eq!(WitnessFile::parse(&witness).as_ref(), Ok(&case.batch));
    assert_eq!(
        WitnessFile::parse(&witness[..witness.len() - 1]),
        Err(FormatError::Truncated)
    );
    let width = case.batch.bytes_per_instance();
    // 36 signals: the last byte of each instance has four spare bits.
    assert_eq!(case.file.n_signals % 8, 4);
    let mut spare = case.batch.clone();
    spare.data[2 * width - 1] |= 0x80;
    assert_eq!(
        WitnessFile::parse(&spare.encode()),
        Err(FormatError::SpareBitsSet { instance: 1 })
    );
    let mut no_constant = case.batch.clone();
    no_constant.data[width] &= !1;
    assert_eq!(
        WitnessFile::parse(&no_constant.encode()),
        Err(FormatError::ConstantNotOne { instance: 1 })
    );
}
