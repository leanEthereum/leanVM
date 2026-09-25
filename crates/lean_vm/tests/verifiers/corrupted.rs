//! A corrupted proof is refused, and refused the way a verifier must refuse: with an
//! error, never with a panic and never with acceptance. Everything here is the
//! prover's to choose, so every path the verifier takes through it has to end in
//! [`CpuError`], not in an index out of bounds.

use lean_vm::cpu::{Proof, prove, verify};

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// One corruption of `proof`, chosen by `round`: a scalar's bit, a truncated stream,
/// a leaf word, a sibling digest, or a missing Merkle hint.
fn corrupt(proof: &Proof, round: usize, rng: &mut Rng) -> Proof {
    let mut forged = proof.clone();
    match round % 5 {
        0 => {
            let scalar = &mut forged.stream[rng.below(proof.stream.len())];
            let bit = 1u64 << (rng.next() % 64);
            match rng.next() % 3 {
                0 => scalar.c0 ^= bit,
                1 => scalar.c1 ^= bit,
                _ => scalar.c2 ^= bit,
            }
        }
        // At least one scalar short, so the stream really is cut.
        1 => forged.stream.truncate(rng.below(proof.stream.len())),
        2 => {
            let paths = &mut forged.merkle[rng.below(proof.merkle.len())];
            let row = rng.below(paths.leaf_data.len());
            let word = rng.below(paths.leaf_data[row].len());
            paths.leaf_data[row][word].0 ^= 1 << (rng.next() % 64);
        }
        3 => {
            let paths = &mut forged.merkle[rng.below(proof.merkle.len())];
            let hash = rng.below(paths.sibling_hashes.len());
            paths.sibling_hashes[hash][rng.below(32)] ^= 1;
        }
        _ => {
            forged.merkle.remove(rng.below(proof.merkle.len()));
        }
    }
    forged
}

#[test]
fn a_corrupted_proof_is_rejected_and_never_panics() {
    let (program, expected) = super::programs::fibonacci();
    let input = [0; 4];
    let (proof, output, _) = prove(&program, input, &[], 1).expect("the run halts");
    assert_eq!(output, expected);
    verify(&program, &input, &output, &proof).expect("the honest proof verifies");
    assert!(
        proof
            .merkle
            .iter()
            .all(|p| !p.leaf_data.is_empty() && !p.sibling_hashes.is_empty()),
        "the corruptions below index into every opening"
    );

    let mut rng = Rng(0x5eed_1234_5678_9abc);
    for round in 0..250 {
        let forged = corrupt(&proof, round, &mut rng);
        if forged == proof {
            continue; // the one no-op a random truncation can draw
        }
        let verified = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            verify(&program, &input, &output, &forged)
        }));
        match verified {
            Ok(Ok(())) => panic!("round {round}: a corrupted proof was accepted"),
            Ok(Err(_)) => {}
            Err(_) => panic!("round {round}: the verifier panicked instead of rejecting"),
        }
    }
}
