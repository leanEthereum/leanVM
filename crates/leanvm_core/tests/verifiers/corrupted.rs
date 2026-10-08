//! A corrupted proof is refused, and refused the way a verifier must refuse: with an
//! error, never with a panic and never with acceptance. Everything here is the
//! prover's to choose, so every path the verifier takes through it has to end in
//! [`CpuError`], not in an index out of bounds.

use leanvm_core::{Clock, CpuError, N_TABLES, Proof, ProvenRun, Prover, Rate};
use primitives::{F64, F192};
use std::panic::AssertUnwindSafe;

struct Rng(u64);

impl Rng {
    const fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    const fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// One corruption of `proof`, chosen by `round`: a scalar's bit, a truncated stream,
/// a leaf word, a sibling digest, or a missing Merkle hint.
fn corrupt(proof: &Proof, round: usize, rng: &mut Rng) -> Proof {
    let mut forged = proof.clone();
    match round % 5 {
        0 => {
            let scalar = &mut forged.0.stream[rng.below(proof.0.stream.len())];
            let bit = 1u64 << (rng.next() % 64);
            let mut coefficients = scalar.coefficients();
            coefficients[(rng.next() % 3) as usize] += F64::new(bit);
            *scalar = F192::new(coefficients);
        }
        // At least one scalar short, so the stream really is cut.
        1 => forged.0.stream.truncate(rng.below(proof.0.stream.len())),
        2 => {
            let paths = &mut forged.0.merkle[rng.below(proof.0.merkle.len())];
            let row = rng.below(paths.leaf_data.len());
            let word = rng.below(paths.leaf_data[row].len());
            paths.leaf_data[row][word] += F64::new(1 << (rng.next() % 64));
        }
        3 => {
            let paths = &mut forged.0.merkle[rng.below(proof.0.merkle.len())];
            let hash = rng.below(paths.sibling_hashes.len());
            paths.sibling_hashes[hash][rng.below(32)] ^= 1;
        }
        _ => {
            forged.0.merkle.remove(rng.below(proof.0.merkle.len()));
        }
    }
    forged
}

#[test]
fn a_corrupted_proof_is_rejected_and_never_panics() {
    let (program, expected) = super::programs::fibonacci();
    let ProvenRun { proof, output, .. } = Prover::new(Rate::MIN).prove(&program, &[]).expect("the run halts");
    assert_eq!(output, expected);
    program.verify(output, &proof).expect("the honest proof verifies");
    assert!(
        proof
            .0
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
        let verified = std::panic::catch_unwind(AssertUnwindSafe(|| program.verify(output, &forged)));
        match verified {
            Ok(Ok(())) => panic!("round {round}: a corrupted proof was accepted"),
            Ok(Err(_)) => {}
            Err(_) => panic!("round {round}: the verifier panicked instead of rejecting"),
        }
    }
}

#[test]
fn noncanonical_announcements_and_roots_are_refused() {
    let (program, _) = super::programs::fibonacci();
    let ProvenRun { proof, output, .. } = Prover::new(Rate::MIN).prove(&program, &[]).expect("the run halts");

    let mut forged = proof.clone();
    forged.0.stream[0].c1 = 1;
    assert_eq!(program.verify(output, &forged), Err(CpuError::NonCanonicalSize.into()));

    let mut forged = proof;
    forged.0.stream[N_TABLES + 2].c2 = 1;
    assert!(program.verify(output, &forged).is_err());
}

#[test]
fn a_final_clock_must_be_live_and_valid() {
    let (program, _) = super::programs::fibonacci();
    let ProvenRun { proof, output, .. } = Prover::new(Rate::MIN).prove(&program, &[]).expect("the run halts");
    let at = N_TABLES + 1;
    let honest = proof.0.stream[at].c0;
    for clock in [0, honest ^ Clock::SEED_CLOCK, honest | 1 << Clock::FAIL_BIT] {
        let mut forged = proof.clone();
        forged.0.stream[at] = F192::new(clock, 0, 0);
        assert_eq!(program.verify(output, &forged), Err(CpuError::FinalClock.into()));
    }
}
