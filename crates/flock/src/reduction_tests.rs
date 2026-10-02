//! The BLAKE2s circuit driven through flock's actual reduction: zerocheck then
//! lincheck, prover and verifier, on the shared transcript.
//!
//! The unit tests in `flock::hash` establish that the circuit is the right
//! circuit (known-answer vectors, honest witness satisfies, walk agrees with
//! the matrices). This establishes that the ten-round encoding is *provable*
//! with the machinery as it stands: same zerocheck, same lincheck, same
//! `k_log = 14` and `k_skip = 6`. Only the PCS opening is left out, which is
//! generic in the claims and covered end to end by `blake2s_batch`.

use crate::hash::{
    Compression, K_LOG, K_SKIP, WalkLincheckCircuit, generate_witness_with_ab_packed_and_lincheck, min_n_blocks_log,
    param_iv,
};
use crate::reduction::{self, Block};
use fiat_shamir::transcript::{ProverState, VerifierState};
use primitives::test_rng::Rng;

const LABEL: &[u8] = b"flock-blake2s-reduction-test";

const BLOCK: Block<'static> = Block {
    k_log: K_LOG,
    useful_bits: crate::hash::USEFUL_BITS,
    circuit: &WalkLincheckCircuit,
};

fn blocks_for(n: usize, seed: u64) -> Vec<Compression> {
    let mut rng = Rng::new(seed);
    (0..n)
        .map(|i| {
            (
                if i == 0 {
                    param_iv()
                } else {
                    std::array::from_fn(|_| rng.next_u32())
                },
                std::array::from_fn(|_| rng.next_u32()),
                64 * (i as u64 + 1),
                if i % 3 == 0 { u32::MAX } else { 0 },
                0,
            )
        })
        .collect()
}

/// Prove. `tamper` may corrupt the packed witness first, in which case the
/// transcript this returns must not verify.
fn prove(n: usize, tamper: Option<usize>) -> (usize, fiat_shamir::transcript::Proof) {
    let n_log = min_n_blocks_log(n);
    let blocks = blocks_for(n, 0xB2_5E_ED ^ n as u64);

    let (mut z, a, b, mut z_lincheck) = generate_witness_with_ab_packed_and_lincheck(&blocks, n_log);
    if let Some(bit) = tamper {
        // Flip one committed witness bit, in both views the prover feeds in.
        z[bit / 64] ^= 1u64 << (bit % 64);
        let (inner, outer) = (bit % (1 << K_LOG), bit >> K_LOG);
        z_lincheck[(outer / 8) * (1 << K_LOG) + inner] ^= 1u8 << (outer % 8);
    }

    let mut ps = ProverState::from_label(LABEL);
    let instance = reduction::Instance {
        block: BLOCK,
        n_blocks_log: n_log,
        z: &z,
        a: &a,
        b: &b,
        pad: None,
        z_lincheck: &z_lincheck,
    };
    reduction::prove(&[instance], &mut ps);
    (n_log, ps.into_proof())
}

/// Replay a transcript through the reduction verifier.
fn verify(n_log: usize, transcript: &fiat_shamir::transcript::Proof) -> bool {
    let mut vs = VerifierState::from_label(LABEL, transcript);
    reduction::verify(&[(BLOCK, n_log)], &mut vs).is_ok() && vs.finish().is_ok()
}

/// Prove, then verify.
fn run(n: usize, tamper: Option<usize>) -> bool {
    let (n_log, transcript) = prove(n, tamper);
    verify(n_log, &transcript)
}

/// Ten rounds of BLAKE2s inside a 2^14 block, proved and verified through the
/// unmodified zerocheck and lincheck. The lincheck verifier here answers via
/// [`flock::hash::bilinear_walk`], so this also exercises the circuit walk
/// against the same transcript the walk-driven prover produced.
#[test]
fn blake2s_reduction_roundtrip() {
    for n in [8usize, 16] {
        assert!(run(n, None), "honest BLAKE2s reduction must verify at n = {n}");
    }
}

/// A single flipped witness bit must not survive. Picks bits inside the deep
/// end of the cascade (the last round's products) as well as an input bit.
#[test]
fn blake2s_reduction_rejects_tampering() {
    // GS_BASE + G_STRIDE * 79 = 15,816: the last G's product block.
    for bit in [0usize, 700, 15_816, 15_900, 15_999] {
        assert!(
            !run(8, Some(bit)),
            "flipping witness bit {bit} must make the reduction reject"
        );
    }
}

/// One flipped transcript word in any region must make the reduction reject:
/// the zerocheck's terminal identity, or lincheck, which pins â, b̂ and ĉ
/// against the same witness vector, catches it.
#[test]
fn blake2s_reduction_rejects_proof_mutations() {
    let n = 8;
    let (n_log, transcript) = prove(n, None);
    assert!(verify(n_log, &transcript), "honest transcript must verify");

    let ell = 1usize << K_SKIP;
    let n_mlv = K_LOG + n_log - K_SKIP;
    let zc_len = ell + 2 * n_mlv + 3;
    let lc_rounds = K_LOG - K_SKIP;
    let regions: [(&str, usize); 7] = [
        ("zerocheck round1[0]", 0),
        ("zerocheck round1[last]", ell - 1),
        ("zerocheck round[mid].msg_1", ell + 2 * (n_mlv / 2)),
        ("zerocheck round[mid].msg_inf", ell + 2 * (n_mlv / 2) + 1),
        ("zerocheck final_a", zc_len - 3),
        ("lincheck round[0]", zc_len),
        ("lincheck z_partial[0]", zc_len + 2 * lc_rounds),
    ];
    for (label, word) in regions {
        let mut bad = transcript.clone();
        bad.stream[word].c0 ^= 1;
        assert!(!verify(n_log, &bad), "flipping {label} must make the reduction reject");
    }
}
