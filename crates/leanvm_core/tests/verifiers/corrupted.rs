//! A corrupted proof is refused, and refused the way a verifier must refuse: with an
//! error, never with a panic and never with acceptance. Everything here is the
//! prover's to choose, so every path the verifier takes through it has to end in
//! an error, not in an index out of bounds.

use leanvm::{Clock, CpuError, N_TABLES, Proof, ProvenRun, Prover, Rate};
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

/// Where each hint's bytes start and end, past its 4-byte length.
fn hints(proof: &Proof) -> Vec<std::ops::Range<usize>> {
    let hints = &proof.0.hints;
    let mut ranges = Vec::new();
    let mut at = 0;
    while at < hints.len() {
        let len = u32::from_le_bytes(hints[at..at + 4].try_into().unwrap()) as usize;
        ranges.push(at + 4..at + 4 + len);
        at += 4 + len;
    }
    ranges
}

/// One corruption of `proof`, chosen by `round`: a message bit, a cut message string, a hint bit, cut hints, or a
/// missing hint.
fn corrupt(proof: &Proof, round: usize, rng: &mut Rng) -> Proof {
    let mut forged = proof.clone();
    let (narg, hints) = (&mut forged.0.narg, &mut forged.0.hints);
    match round % 5 {
        0 => narg[rng.below(proof.0.narg.len())] ^= 1 << (rng.next() % 8),
        // At least one byte short, so the messages really are cut.
        1 => narg.truncate(rng.below(proof.0.narg.len())),
        2 => hints[rng.below(proof.0.hints.len())] ^= 1 << (rng.next() % 8),
        3 => hints.truncate(rng.below(proof.0.hints.len())),
        _ => {
            let ranges = self::hints(proof);
            let range = &ranges[rng.below(ranges.len())];
            hints.drain(range.start - 4..range.end);
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
        hints(&proof).iter().all(|h| !h.is_empty()),
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
fn a_noncanonical_announcement_is_refused() {
    let (program, _) = super::programs::fibonacci();
    let ProvenRun { proof, output, .. } = Prover::new(Rate::MIN).prove(&program, &[]).expect("the run halts");

    // The first height, with its second limb set: bytes 8..16 of the first message.
    let mut forged = proof;
    forged.0.narg[8] = 1;
    assert_eq!(program.verify(output, &forged), Err(CpuError::NonCanonicalSize.into()));
}

#[test]
fn a_final_clock_must_be_live_and_valid() {
    let (program, _) = super::programs::fibonacci();
    let ProvenRun { proof, output, .. } = Prover::new(Rate::MIN).prove(&program, &[]).expect("the run halts");
    // The clock is message N_TABLES + 1, after the heights and the rate.
    let at = 24 * (N_TABLES + 1);
    let honest = u64::from_le_bytes(proof.0.narg[at..at + 8].try_into().unwrap());
    for clock in [0, honest ^ Clock::SEED_CLOCK, honest | 1 << Clock::FAIL_BIT] {
        let mut forged = proof.clone();
        forged.0.narg[at..at + 8].copy_from_slice(&clock.to_le_bytes());
        assert_eq!(program.verify(output, &forged), Err(CpuError::FinalClock.into()));
    }
}
