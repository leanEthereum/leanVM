//! u64 circuits driven through the whole reduction: zerocheck then lincheck, prover and verifier.
//!
//! The circuits are built from the builder and the multiplier gadget, their witnesses by the generic walk.
//! Only the commitment's opening is left out: it is generic in the claims.

use fiat_shamir::transcript::{ProofTranscript, ProverState, VerifierState};
use primitives::field::F192;
use primitives::test_util::Rng;

use crate::Witness;
use crate::circuit::{Builder, Circuit, Wire};
use crate::gadgets::mul::Multiplier;
use crate::reduction::{self, Block, Instance};
use crate::zerocheck::K_SKIP;

/// The first slot of the result, after the two input words.
const OUT_BASE: usize = 128;

/// One u64 operation, as a whole circuit: inputs `a` and `b`, one result port.
#[derive(Clone, Copy, Debug)]
enum Op {
    /// `a + b mod 2^64`.
    WrappingAdd,

    /// `a b mod 2^64`.
    WrappingMul,

    /// `a b` as a u128.
    WideningMul,
}

impl Op {
    /// Every operation, smallest circuit first.
    const ALL: [Self; 3] = [Self::WrappingAdd, Self::WrappingMul, Self::WideningMul];

    /// The operation's gate list.
    fn circuit(self) -> Circuit {
        let n = match self {
            Self::WrappingAdd | Self::WrappingMul => 64,
            Self::WideningMul => 128,
        };
        let mut c = Builder::new(&[64, 64], &[n]);
        let (a, b) = (c.input(0), c.input(1));
        let out = match self {
            Self::WrappingAdd => ripple_carry(&mut c, &a, &b),
            Self::WrappingMul | Self::WideningMul => Multiplier::build(&mut c, &a, &b, n).0,
        };
        for (i, wire) in out.into_iter().enumerate() {
            c.output(0, i, wire);
        }
        c.finish()
    }
}

/// `a + b mod 2^64`: the carry into bit `i + 1` is `maj(a_i, b_i, c_i) = (a_i + c_i)(b_i + c_i) + c_i`.
fn ripple_carry(c: &mut Builder, a: &[Wire], b: &[Wire]) -> Vec<Wire> {
    let mut carry = None;
    let mut sum = Vec::with_capacity(64);
    for i in 0..64 {
        let ac = c.xor(a[i], carry);
        let bc = c.xor(b[i], carry);
        sum.push(c.xor(ac, b[i]));
        // The carry out of bit 63 falls off the modulus.
        if i < 63 {
            let maj = c.and(ac, bc);
            carry = c.xor(maj, carry);
        }
    }
    sum
}

/// Every pairing of the carry-heavy edge values, then random pairs.
fn pairs(n: usize, seed: u64) -> Vec<[u64; 2]> {
    const EDGES: [u64; 6] = [0, 1, 2, 1 << 63, u64::MAX - 1, u64::MAX];
    let mut rng = Rng::new(seed);
    (EDGES.iter().flat_map(|&x| EDGES.iter().map(move |&y| [x, y])))
        .chain(std::iter::repeat_with(|| [rng.next_u64(), rng.next_u64()]))
        .take(n)
        .collect()
}

/// The walk's witness of `pairs`, padded with `(0, 0)` to `2^n_log` instances.
fn witness(circuit: &Circuit, pairs: &[[u64; 2]], n_log: usize) -> Witness {
    circuit.witness_by_walk(pairs, &[0; 2], n_log, |row, words| words.copy_from_slice(row))
}

/// Prove one circuit's batch, then replay it: the verifier's claim, its matrices settled, the stream consumed.
fn accepts(block: Block<'_>, n_log: usize, witness: &Witness, tamper: impl FnOnce(&mut ProofTranscript)) -> bool {
    const LABEL: &[u8] = b"flock-u64-reduction-test";
    let mut ps = ProverState::from_label(LABEL);
    let claims = reduction::prove(&[Instance::of(block, n_log, witness)], &mut ps);
    let mut proof = ps.into_proof();
    tamper(&mut proof);
    let mut vs = VerifierState::from_label(LABEL, &proof);
    reduction::verify(&[(block.shape(), n_log)], &mut vs)
        .is_ok_and(|r| r[0].claim == claims[0] && r[0].matrices.check(block.circuit).is_ok())
        && vs.finish().is_ok()
}

#[test]
fn a_batch_verifies_and_a_flipped_bit_is_refused() {
    // Invariant: an honest batch verifies, tying the prover's backward walk to the verifier's forward one.
    //
    // Fixture state: 32 instances, the fewest whose cube reaches the zerocheck's 2^13 bits for every operation.
    //
    // Mutation: one bit of `a`, of the result, the constant, and the last product.
    let n_log = 5;
    for op in Op::ALL {
        let circuit = op.circuit();
        let pairs = pairs(1 << n_log, 0x3A12);
        assert!(
            accepts(circuit.block(), n_log, &witness(&circuit, &pairs, n_log), |_| {}),
            "{op:?}"
        );
        for bit in [3, OUT_BASE + 5, circuit.const_pos(), circuit.useful_bits() - 1] {
            let mut tampered = witness(&circuit, &pairs, n_log);
            tampered.z[bit / 64] ^= 1 << (bit % 64);
            assert!(!accepts(circuit.block(), n_log, &tampered, |_| {}), "{op:?}: bit {bit}");
        }
    }
}

#[test]
fn a_moved_proof_word_is_refused() {
    // Invariant: every region of the stream is checked, by the zerocheck's terminal identity or by the lincheck.
    //
    // Fixture state: eight widening products, so a cube of 2^16 bits and 10 multilinear rounds.
    //
    //     [round 1: 64][2 per round][a, b, c][lincheck: 2 per round][64 slices][form value]
    let n_log = 3;
    let circuit = Op::WideningMul.circuit();
    let witness = witness(&circuit, &pairs(1 << n_log, 0x3A14), n_log);
    let ell = 1 << K_SKIP;
    let n_mlv = circuit.k_log() + n_log - K_SKIP;
    let zerocheck_len = ell + 2 * n_mlv + 3;
    let lincheck_rounds = circuit.k_log() - K_SKIP;
    for (label, word) in [
        ("zerocheck round 1, first", 0),
        ("zerocheck round 1, last", ell - 1),
        ("zerocheck middle round, G(1)", ell + 2 * (n_mlv / 2)),
        ("zerocheck middle round, G(inf)", ell + 2 * (n_mlv / 2) + 1),
        ("zerocheck a", zerocheck_len - 3),
        ("lincheck first round", zerocheck_len),
        ("lincheck first slice", zerocheck_len + 2 * lincheck_rounds),
    ] {
        let moved = |proof: &mut ProofTranscript| proof.stream[word] += F192::ONE;
        assert!(!accepts(circuit.block(), n_log, &witness, moved), "{label}");
    }
}

#[test]
fn a_mixed_batch_proves_each_circuit() {
    // Invariant: a batch of circuits proves each of them.
    // The verifier recovers each claim, and each is its witness's truth.
    //
    // Fixture state, (operation, log instances, rows): three block sizes, from no rows to full batches.
    const LABEL: &[u8] = b"flock-u64-batch-test";
    let circuits = Op::ALL.map(Op::circuit);
    assert_eq!(circuits.each_ref().map(Circuit::k_log), [8, 12, 13]);
    let shapes = [(0, 9, 0), (1, 7, 40), (2, 3, 5), (0, 6, 64), (1, 8, 130)];
    let blocks: Vec<(Block<'_>, usize)> = shapes
        .iter()
        .map(|&(op, n_log, _)| (circuits[op].block(), n_log))
        .collect();
    let tables = |f: usize| -> Witness {
        let (op, n_log, rows) = shapes[f];
        witness(&circuits[op], &pairs(rows, 0x3A15 + f as u64), n_log)
    };
    let whole: Vec<Witness> = (0..shapes.len()).map(tables).collect();
    let prove = |tables: &[Witness]| {
        let instances: Vec<Instance<'_>> = (tables.iter().zip(&blocks))
            .map(|(witness, &(block, n_blocks_log))| Instance::of(block, n_blocks_log, witness))
            .collect();
        let mut ps = ProverState::from_label(LABEL);
        let claims = reduction::prove(&instances, &mut ps);
        (ps.into_proof(), claims)
    };
    let accepts = |proof: &ProofTranscript| {
        let mut vs = VerifierState::from_label(LABEL, proof);
        let shapes: Vec<_> = blocks.iter().map(|(block, n)| (block.shape(), *n)).collect();
        let replays = reduction::verify(&shapes, &mut vs).ok()?;
        let settled = (replays.iter().zip(&blocks)).all(|(r, (block, _))| r.matrices.check(block.circuit).is_ok());
        (settled && vs.finish().is_ok()).then_some(replays)
    };

    // Each claim is its witness's slices: word `w` is position `w` past the skip, bit `i` its slice `i`.
    let (proof, claims) = prove(&whole);
    let replays = accepts(&proof).expect("an honest batch verifies");
    for (f, ((replay, claim), Witness { z, .. })) in replays.iter().zip(&claims).zip(&whole).enumerate() {
        assert_eq!(&replay.claim, claim, "circuit {f}");
        let eq = primitives::multilinear::eq_table(&claim.suffix_point);
        let slices: Vec<F192> = (0..64)
            .map(|i| (z.iter().zip(&eq)).fold(F192::ZERO, |acc, (&w, &e)| if w >> i & 1 == 1 { acc + e } else { acc }))
            .collect();
        assert_eq!(claim.s_hat_v, slices, "circuit {f}");
    }

    // Mutation: an output bit of instance 1, in any one circuit.
    for f in 0..shapes.len() {
        let mut tampered: Vec<Witness> = (0..shapes.len()).map(tables).collect();
        let bit = (1 << blocks[f].0.k_log) + OUT_BASE + 5;
        tampered[f].z[bit / 64] ^= 1 << (bit % 64);
        assert!(accepts(&prove(&tampered).0).is_none(), "circuit {f}");
    }

    // Mutation: one circuit's zerocheck claim on `a`, or one of its slices.
    //
    //     [round 1: 64][2 per zerocheck round][3 claims per circuit][2 per lincheck round][65 words per circuit]
    let n_zerocheck = shapes
        .iter()
        .map(|&(op, n_log, _)| circuits[op].k_log() + n_log)
        .max()
        .unwrap()
        - K_SKIP;
    let n_lincheck = circuits.iter().map(Circuit::k_log).max().unwrap() - K_SKIP;
    let zerocheck_len = (1 << K_SKIP) + 2 * n_zerocheck + 3 * shapes.len();
    for f in 0..shapes.len() {
        for word in [
            (1 << K_SKIP) + 2 * n_zerocheck + 3 * f,
            zerocheck_len + 2 * n_lincheck + 65 * f + 3,
        ] {
            let mut bad = proof.clone();
            bad.stream[word] += F192::ONE;
            assert!(accepts(&bad).is_none(), "circuit {f}, word {word}");
        }
    }
}
