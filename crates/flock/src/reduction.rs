//! The circuit-agnostic half of flock: zerocheck then lincheck over batches of `2^k_log`-bit blocks.
//!
//! Every circuit of a batch shares every challenge.
//! Each circuit's R1CS validity reduces to one claim on its packed witness, ready for ring switching.
//! A circuit supplies only its block: its shape, and the walks behind its matrices.

use fiat_shamir::arith::Verifier;
use fiat_shamir::transcript::ProverState;
use pcs::ring_switch::SliceClaim;
use primitives::field::F192;

use crate::error::FlockError;
use crate::lincheck::{self, LincheckCircuit, LincheckInput, MatrixClaim, MatrixForm, QuirkyPoint};
use crate::witness::{Tables, Witness, packed_bytes};
use crate::zerocheck::multilinear::PackedWitness;
use crate::zerocheck::{self, K_SKIP, Padding, SkipDomain, ZerocheckInput};

// A claim's `2^K_SKIP` slices are a ring-switch claim on the packed witness only if they are one word's bits.
const _: () = assert!(
    K_SKIP == u64::BITS.ilog2() as usize,
    "the univariate skip must match the PCS packing width"
);

/// The fewest instances, as a base-two logarithm, that prove `n_blocks` of them.
///
/// The lincheck reads its witness in stripes of eight instances, so a batch holds at least eight.
///
/// # Panics
///
/// When `n_blocks` is zero.
pub const fn min_n_blocks_log(n_blocks: usize) -> usize {
    assert!(n_blocks >= 1, "a batch proves at least one instance");
    let n = if n_blocks > 8 { n_blocks } else { 8 };
    n.next_power_of_two().trailing_zeros() as usize
}

/// The instances before a packed witness's identical tail.
///
/// From the returned index on, every instance's `z` is the last one's, and so are its `A z` and `B z`.
///
/// # Panics
///
/// When an instance is not whole words.
pub fn live_instances(z: &[u64], k_log: usize) -> usize {
    assert!(k_log >= 6, "an instance is whole words");
    let words = 1usize << (k_log - 6);
    let Some(last) = z.rchunks_exact(words).next() else {
        return 0;
    };
    // Count the copies of the last instance just before it.
    let copies = z.rchunks_exact(words).skip(1).take_while(|w| *w == last).count();
    z.len() / words - 1 - copies
}

/// A circuit as the reduction sees it.
#[derive(Clone, Copy)]
pub struct Block<'a> {
    /// The base-two logarithm of the bits per instance.
    pub k_log: usize,

    /// The bits of an instance before its zero padding, which the prover skips.
    pub useful_bits: usize,

    /// The circuit's matrices, reached only by walking it.
    pub circuit: &'a dyn LincheckCircuit,
}

impl Block<'_> {
    /// What the verifier's replay reads of the circuit short of its matrices.
    pub fn shape(&self) -> Shape {
        Shape {
            k_log: self.k_log,
            const_pin_col: self.circuit.const_pin_col(),
        }
    }
}

/// What the verifier's replay reads of a circuit short of its matrices.
///
/// The matrices are left to the claim the replay returns, so the replay needs no built circuit.
/// Whoever settles that claim against the circuit holds the circuit to this shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Shape {
    /// The base-two logarithm of the bits per instance.
    pub k_log: usize,

    /// The column of the constant wire, which the lincheck pins to one.
    pub const_pin_col: usize,
}

impl Shape {
    /// Whether a matrix form has the lengths a replay of a circuit of this shape gives.
    pub const fn fits(&self, form: &MatrixForm) -> bool {
        let rest = self.k_log - K_SKIP;
        form.s_hat_v.len() == 1 << K_SKIP && form.x_inner_rest.len() == rest && form.r_inner_rest.len() == rest
    }
}

/// What the verifier's replay leaves of one circuit.
///
/// Its elements are values, or whatever a verifier holds them as.
#[derive(Clone, Debug)]
pub struct ReductionReplay<E = F192> {
    /// The claim on the circuit's packed witness, which the commitment's opening settles.
    pub claim: SliceClaim<E>,

    /// The claim on the circuit's matrices, which whoever holds the circuit settles.
    pub matrices: MatrixClaim<E>,
}

/// One circuit's batch as the prover holds it: `2^n_blocks_log` instances of its block, and their witness.
///
/// The bits are borrowed apart from the factor tables.
/// A committed batch's bits are its column of the commitment, which the generators write in place.
#[derive(Clone, Copy)]
pub struct Instance<'a> {
    /// The circuit.
    pub block: Block<'a>,

    /// The base-two logarithm of the instance count.
    pub n_blocks_log: usize,

    /// The instances before the identical tail.
    ///
    /// The zerocheck sums the tail once while it binds variables inside an instance.
    /// Nothing of the proof depends on it: claiming no tail changes no word.
    pub live: usize,

    /// The witness bits.
    pub z: &'a [u64],

    /// `A z`.
    pub az: &'a [u64],

    /// `B z`.
    pub bz: &'a [u64],
}

impl<'a> Instance<'a> {
    /// A batch whose bits the caller holds apart from its factor tables.
    ///
    /// Its identical tail is read off its bits.
    pub fn new(block: Block<'a>, n_blocks_log: usize, z: &'a [u64], tables: &'a Tables) -> Self {
        Self {
            block,
            n_blocks_log,
            live: live_instances(z, block.k_log),
            z,
            az: &tables.az,
            bz: &tables.bz,
        }
    }

    /// A batch whose whole witness is `witness`.
    ///
    /// Its identical tail is read off its bits.
    pub fn of(block: Block<'a>, n_blocks_log: usize, witness: &'a Witness) -> Self {
        Self {
            block,
            n_blocks_log,
            live: live_instances(&witness.z, block.k_log),
            z: &witness.z,
            az: &witness.az,
            bz: &witness.bz,
        }
    }

    /// The base-two logarithm of the batch's bits.
    const fn m(&self) -> usize {
        self.block.k_log + self.n_blocks_log
    }

    /// The batch as the zerocheck reads it: the factor tables' bits, and where their padding lies.
    fn zerocheck_input(&self) -> ZerocheckInput<'a> {
        // Each table packs the batch's `2^m` bits 64 a word.
        let words = 1usize << (self.m() - 6);
        assert_eq!(self.z.len(), words, "wrong packed witness length");
        assert_eq!(self.az.len(), words, "wrong packed A z length");
        assert_eq!(self.bz.len(), words, "wrong packed B z length");
        ZerocheckInput {
            bits: PackedWitness {
                a: packed_bytes(self.az),
                b: packed_bytes(self.bz),
            },
            m: self.m(),
            padding: Padding {
                k_log: self.block.k_log,
                useful_bits: self.block.useful_bits,
                live_blocks: self.live,
            },
        }
    }

    /// The batch as the lincheck reads it, at the point its zerocheck claims are at.
    fn lincheck_input<'p>(&self, point: &'p QuirkyPoint) -> LincheckInput<'p>
    where
        'a: 'p,
    {
        LincheckInput {
            z: self.z,
            m: self.m(),
            k_log: self.block.k_log,
            k_skip: K_SKIP,
            useful_bits: self.block.useful_bits,
            circuit: self.block.circuit,
            x_ab: point,
        }
    }
}

/// The batched zerocheck then lincheck, leaving one claim on each circuit's packed witness.
///
/// - The zerocheck reduces `a b + c = 0` over every circuit's cube to claims on its `(a, b, c)` at one point.
/// - The lincheck reduces those, against the circuit's matrices, to the bit slices of its `z` at one point.
///
/// Every circuit shares every challenge.
/// No statement is bound here: the embedding protocol binds the circuits, the instance counts and the commitment first.
pub fn prove(instances: &[Instance<'_>], ps: &mut ProverState) -> Vec<SliceClaim> {
    // Phase 1: the zerocheck, each circuit's claims at its share of one point.
    let points: Vec<QuirkyPoint> = {
        let _span = tracing::info_span!("Zerocheck").entered();
        let inputs: Vec<ZerocheckInput<'_>> = instances.iter().map(Instance::zerocheck_input).collect();
        let claims = zerocheck::prove(&inputs, ps);
        (instances.iter().zip(&claims))
            .map(|(i, claim)| claim.point(i.block.k_log - K_SKIP))
            .collect()
    };

    // Phase 2: the lincheck at those points, each circuit's claim moving onto its witness.
    let _span = tracing::info_span!("Lincheck").entered();
    let inputs: Vec<LincheckInput<'_>> = (instances.iter().zip(&points))
        .map(|(i, point)| i.lincheck_input(point))
        .collect();
    let claims = lincheck::prove(&inputs, ps);

    // The witness's point: the lincheck's inner coordinates, then the zerocheck's outer ones.
    (claims.into_iter().zip(&points))
        .map(|(claim, point)| claim.slice_claim(&point.x_outer))
        .collect()
}

/// Replay the batched zerocheck and lincheck over circuits of `2^n` instances each, straight off the transcript.
///
/// Each circuit is its shape and `n`, and leaves two claims:
///
/// - one on its packed witness, which the commitment's opening settles;
/// - one on its matrices, which the built circuit settles.
///
/// The verifier's arithmetic is the native one or the recursion machine's rows, which run the same steps.
///
/// # Errors
///
/// The first stage that refuses the proof.
pub fn verify<V: Verifier>(circuits: &[(Shape, usize)], v: &mut V) -> Result<Vec<ReductionReplay<V::E>>, FlockError> {
    // Phase 1: the zerocheck's point and evaluations.
    let log_ns: Vec<usize> = circuits.iter().map(|(shape, n)| shape.k_log + n).collect();
    let zc = v
        .scope("zerocheck", |v| zerocheck::verify(&log_ns, v))
        .map_err(FlockError::Zerocheck)?;

    // Phase 2: the lincheck, each circuit's matrices left as a claim.
    let shapes: Vec<Shape> = circuits.iter().map(|&(shape, _)| shape).collect();
    let matrices = v
        .scope("lincheck", |v| {
            lincheck::verify_deferred(SkipDomain::FLOCK, &zc, &shapes, v)
        })
        .map_err(FlockError::Lincheck)?;

    // Each witness claim: the lincheck's inner coordinates, then the zerocheck's outer ones.
    Ok((matrices.into_iter().zip(&log_ns))
        .map(|(matrices, &m)| {
            let rest = matrices.form.r_inner_rest.len();
            let mut suffix_point = matrices.form.r_inner_rest.clone();
            suffix_point.extend_from_slice(&zc.mlv_challenges[rest..m - K_SKIP]);
            let claim = SliceClaim {
                suffix_point,
                s_hat_v: matrices.form.s_hat_v.clone(),
            };
            ReductionReplay { claim, matrices }
        })
        .collect())
}

#[cfg(test)]
mod tests {
    //! u64 circuits driven through the whole reduction: zerocheck then lincheck, prover and verifier.
    //!
    //! The circuits are built from the builder and the multiplier gadget, their witnesses by the generic walk.
    //! Only the commitment's opening is left out: it is generic in the claims.

    use fiat_shamir::transcript::{ProofTranscript, ProverState, VerifierState};
    use primitives::field::F192;
    use primitives::test_util::Rng;

    use crate::Witness;
    use crate::circuit::{Builder, Circuit};
    use crate::gadgets::Multiplier;
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
                Self::WrappingAdd => crate::clean::wrapping_add64(&mut c, &a, &b).to_vec(),
                Self::WrappingMul => Multiplier::build::<64>(&mut c, &a, &b).0.to_vec(),
                Self::WideningMul => Multiplier::build::<128>(&mut c, &a, &b).0.to_vec(),
            };
            for (i, wire) in out.into_iter().enumerate() {
                c.output(0, i, wire);
            }
            c.finish()
        }
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
                .map(|i| {
                    (z.iter().zip(&eq)).fold(F192::ZERO, |acc, (&w, &e)| if w >> i & 1 == 1 { acc + e } else { acc })
                })
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
}
