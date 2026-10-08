//! The BLAKE2s circuit driven through the whole reduction: zerocheck then lincheck, prover and verifier.
//!
//! The circuit's own tests show it is the right circuit.
//! These show its ten-round encoding is provable with the reduction as it stands, at `k_log = 14`.
//! Only the commitment's opening is left out: it is generic in the claims, and the benchmark covers it.

use fiat_shamir::transcript::{ProofTranscript, ProverState, VerifierState};
use primitives::field::F192;
use primitives::test_util::Rng;

use primitives::hash::PARAM_IV;

use crate::hash::{BLOCK, Blake2sCircuit, Compression, K_LOG};
use crate::reduction::{self, Instance, min_n_blocks_log};
use crate::zerocheck::K_SKIP;

const LABEL: &[u8] = b"flock-blake2s-reduction-test";

/// `n` compressions: a first block from the parameter IV, random chaining values after, mixed finalization flags.
fn blocks_for(n: usize, seed: u64) -> Vec<Compression> {
    let mut rng = Rng::new(seed);
    (0..n)
        .map(|i| {
            let h = if i == 0 {
                PARAM_IV
            } else {
                std::array::from_fn(|_| rng.next_u32())
            };
            let m = std::array::from_fn(|_| rng.next_u32());
            let f0 = if i % 3 == 0 { u32::MAX } else { 0 };
            Compression::new(h, m, 64 * (i as u64 + 1), f0, 0)
        })
        .collect()
}

/// Prove `n` compressions, flipping witness bit `tamper` first if given.
fn prove(n: usize, tamper: Option<usize>) -> (usize, ProofTranscript) {
    let n_log = min_n_blocks_log(n);
    let blocks = blocks_for(n, 0xB2_5E_ED ^ n as u64);
    let mut witness = Blake2sCircuit::witness(&blocks, n_log);
    if let Some(bit) = tamper {
        witness.z[bit / 64] ^= 1 << (bit % 64);
    }
    let mut ps = ProverState::from_label(LABEL);
    reduction::prove(&[Instance::of(BLOCK, n_log, &witness)], &mut ps);
    (n_log, ps.into_proof())
}

/// Whether the replay accepts, its matrix claim settled against the circuit.
fn verify(n_log: usize, transcript: &ProofTranscript) -> bool {
    let mut vs = VerifierState::from_label(LABEL, transcript);
    reduction::verify(&[(BLOCK.shape(), n_log)], &mut vs)
        .is_ok_and(|replays| replays[0].matrices.check(BLOCK.circuit).is_ok())
        && vs.finish().is_ok()
}

#[test]
fn an_honest_batch_verifies() {
    // Invariant: an honest witness proves, and the circuit's forward walk settles the prover's backward one.
    //
    // Fixture state: eight compressions, the floor, then sixteen.
    for n in [8, 16] {
        let (n_log, proof) = prove(n, None);
        assert!(verify(n_log, &proof), "n={n}");
    }
}

#[test]
fn a_flipped_witness_bit_is_refused() {
    // Invariant: no single committed bit can change without the reduction refusing.
    //
    // Mutation: an input bit, a message bit, the last G's product block, and the end of the useful bits.
    //
    //     15816 = 1280 + 184 * 79      the last G's first product
    for bit in [0, 700, 15_816, 15_900, 15_999] {
        let (n_log, proof) = prove(8, Some(bit));
        assert!(!verify(n_log, &proof), "bit {bit}");
    }
}

#[test]
fn a_moved_proof_word_is_refused() {
    // Invariant: every region of the stream is checked, by the zerocheck's terminal identity or by the lincheck.
    //
    // Fixture state: eight compressions, so a cube of 2^17 bits and 11 multilinear rounds.
    //
    //     [round 1: 64][2 per round][a, b, c][lincheck: 2 per round][64 slices][form value]
    let (n_log, proof) = prove(8, None);
    assert!(verify(n_log, &proof), "the honest proof verifies");
    let ell = 1 << K_SKIP;
    let n_mlv = K_LOG + n_log - K_SKIP;
    let zerocheck_len = ell + 2 * n_mlv + 3;
    let lincheck_rounds = K_LOG - K_SKIP;
    for (label, word) in [
        ("zerocheck round 1, first", 0),
        ("zerocheck round 1, last", ell - 1),
        ("zerocheck middle round, G(1)", ell + 2 * (n_mlv / 2)),
        ("zerocheck middle round, G(inf)", ell + 2 * (n_mlv / 2) + 1),
        ("zerocheck a", zerocheck_len - 3),
        ("lincheck first round", zerocheck_len),
        ("lincheck first slice", zerocheck_len + 2 * lincheck_rounds),
    ] {
        let mut bad = proof.clone();
        bad.stream[word] += F192::ONE;
        assert!(!verify(n_log, &bad), "{label}");
    }
}
