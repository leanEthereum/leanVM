//! One u64 operation as a whole circuit, its witness by word arithmetic.
//!
//! ```text
//!     z[0 .. 64)       a
//!     z[64 .. 128)     b
//!     z[128 ..)        the result, 64 or 128 bits, then the constant, then the products
//! ```

use super::InstanceTables;
use super::add::Adder;
use super::mul::Multiplier;
use crate::circuit::{Builder, Circuit};
use crate::reduction::Block;
use crate::witness::Witness;

/// The first slot of `a`.
pub(crate) const A_BASE: usize = 0;

/// The first slot of `b`.
pub(crate) const B_BASE: usize = 64;

/// The first slot of the result.
pub(crate) const OUT_BASE: usize = 128;

/// The operations a whole circuit proves.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum U64Op {
    /// `a + b mod 2^64`.
    WrappingAdd,

    /// `a b mod 2^64`.
    WrappingMul,

    /// `a b` as a u128.
    WideningMul,
}

impl U64Op {
    /// Bits of the committed result.
    pub(crate) const fn out_bits(self) -> usize {
        match self {
            Self::WrappingAdd | Self::WrappingMul => 64,
            Self::WideningMul => 128,
        }
    }
}

/// What an operation's witness is computed from, besides its inputs.
enum Plan {
    Add(Adder),
    Mul(Multiplier),
}

/// One u64 operation as a whole circuit, with the plan its witness replays.
pub struct U64Circuit {
    op: U64Op,
    circuit: Circuit,
    plan: Plan,
}

impl U64Circuit {
    /// The circuit of `op`: two 64-bit inputs, one result.
    pub fn new(op: U64Op) -> Self {
        let n = op.out_bits();
        let mut c = Builder::new(&[64, 64], &[n]);
        let (a, b) = (c.input(0), c.input(1));
        let (out, plan) = match op {
            U64Op::WrappingAdd => {
                let (out, adder) = Adder::build(&mut c, &a, &b);
                (out, Plan::Add(adder))
            }
            U64Op::WrappingMul | U64Op::WideningMul => {
                let (out, multiplier) = Multiplier::build(&mut c, &a, &b, n);
                (out, Plan::Mul(multiplier))
            }
        };
        // The result leaves the circuit through its output port.
        for (i, wire) in out.into_iter().enumerate() {
            c.output(0, i, wire);
        }
        let circuit = c.finish();
        assert_eq!(circuit.const_pos(), OUT_BASE + n);
        Self { op, circuit, plan }
    }

    /// The gate list.
    pub const fn circuit(&self) -> &Circuit {
        &self.circuit
    }

    /// The base-two logarithm of the bits per instance.
    pub const fn k_log(&self) -> usize {
        self.circuit.k_log()
    }

    /// The bits of an instance before its zero padding.
    pub const fn useful_bits(&self) -> usize {
        self.circuit.useful_bits()
    }

    /// The circuit as the reduction sees it.
    pub fn block(&self) -> Block<'_> {
        self.circuit.block()
    }

    /// The witness of `pairs`, padded with `(0, 0)` to `2^n_blocks_log` instances.
    pub fn witness(&self, pairs: &[(u64, u64)], n_blocks_log: usize) -> Witness {
        let n = self.op.out_bits();
        self.circuit
            .witness_by_instance(pairs, &(0, 0), n_blocks_log, |&(a, b), z, az, bz| {
                let mut tables = InstanceTables { z, az, bz };
                // The operation's products, by word arithmetic.
                let out = match &self.plan {
                    Plan::Add(adder) => adder.witness(a, b, &mut tables),
                    Plan::Mul(multiplier) => multiplier.witness_into(a, b, &mut tables),
                };
                // The ports and the constant, each a row against the constant.
                tables.unit_rows(A_BASE, u128::from(a), 64);
                tables.unit_rows(B_BASE, u128::from(b), 64);
                tables.unit_rows(OUT_BASE, out, n);
                tables.unit_rows(self.circuit.const_pos(), 1, 1);
            })
    }
}

#[cfg(test)]
mod tests {
    use fiat_shamir::transcript::{ProofTranscript, ProverState, VerifierState};
    use primitives::field::F192;
    use primitives::test_util::Rng;

    use super::*;
    use crate::lincheck::LincheckCircuit;
    use crate::reduction::{self, Instance};

    const OPS: [U64Op; 3] = [U64Op::WrappingAdd, U64Op::WrappingMul, U64Op::WideningMul];

    /// The operation natively.
    fn native(op: U64Op, a: u64, b: u64) -> u128 {
        let (a, b) = (u128::from(a), u128::from(b));
        match op {
            U64Op::WrappingAdd => u128::from((a + b) as u64),
            U64Op::WrappingMul => u128::from((a * b) as u64),
            U64Op::WideningMul => a * b,
        }
    }

    /// Every pairing of the carry-heavy edge values, then random pairs.
    fn pairs(n: usize, seed: u64) -> Vec<(u64, u64)> {
        const EDGES: [u64; 6] = [0, 1, 2, 1 << 63, u64::MAX - 1, u64::MAX];
        let mut rng = Rng::new(seed);
        (EDGES.iter().flat_map(|&x| EDGES.iter().map(move |&y| (x, y))))
            .chain(std::iter::repeat_with(|| (rng.next_u64(), rng.next_u64())))
            .take(n)
            .collect()
    }

    #[test]
    fn the_witness_is_the_result_and_satisfies_every_row() {
        // Invariant: the word arithmetic commits the native result, and every row `a * b = z` holds.
        // That ties the word-level witness to the gate list the walks read.
        let n_log = 6;
        for op in OPS {
            let circuit = U64Circuit::new(op);
            let k = circuit.circuit.n_cols();
            let pairs = pairs(1 << n_log, 0x3A11);
            let z = circuit.witness(&pairs, n_log).z;
            for (t, &(x, y)) in pairs.iter().enumerate() {
                // Instance `t`'s ports: a, b, then the result over one or two words.
                let word = |w: usize| z[t * (k / 64) + w];
                let out = (u128::from(word(2)) | u128::from(word(3)) << 64) & (u128::MAX >> (128 - op.out_bits()));
                assert_eq!((word(0), word(1), out), (x, y, native(op, x, y)), "{op:?}");

                // Every row, through the forward walk's matrix-vector products at the instance's bits.
                let block: Vec<F192> = (0..k)
                    .map(|i| {
                        if z[(t * k + i) / 64] >> (i % 64) & 1 == 1 {
                            F192::ONE
                        } else {
                            F192::ZERO
                        }
                    })
                    .collect();
                let (ra, rb) = circuit.circuit.row_values(&block);
                assert!((0..k).all(|i| ra[i] * rb[i] == block[i]), "{op:?} ({x}, {y})");
            }
        }
    }

    #[test]
    fn the_word_arithmetic_is_the_gate_walk() {
        // Invariant: the generic walk of the gate list writes the very tables the word arithmetic does.
        let n_log = 4;
        for op in OPS {
            let circuit = U64Circuit::new(op);
            let pairs = pairs(1 << n_log, 0x3A13);
            let rows: Vec<[u64; 2]> = pairs.iter().map(|&(a, b)| [a, b]).collect();
            assert!(
                circuit.witness(&pairs, n_log) == circuit.circuit.witness(&rows, n_log),
                "{op:?}"
            );
        }
    }

    #[test]
    fn a_batch_verifies_and_a_flipped_bit_is_refused() {
        // Invariant: an honest batch verifies, tying the prover's backward walk to the verifier's forward one.
        //
        // Fixture state: 32 instances, the fewest whose cube reaches the zerocheck's 2^13 bits for every operation.
        //
        // Mutation: one bit of `a`, of the result, the constant, and the last product.
        const LABEL: &[u8] = b"flock-arith-reduction-test";
        let n_log = 5;
        for op in OPS {
            let circuit = U64Circuit::new(op);
            let block = circuit.block();
            let pairs = pairs(1 << n_log, 0x3A12);
            let accepts = |tamper: Option<usize>| {
                let mut witness = circuit.witness(&pairs, n_log);
                if let Some(bit) = tamper {
                    witness.z[bit / 64] ^= 1 << (bit % 64);
                }
                let mut ps = ProverState::from_label(LABEL);
                let claims = reduction::prove(&[Instance::of(block, n_log, &witness)], &mut ps);
                let proof = ps.into_proof();
                let mut vs = VerifierState::from_label(LABEL, &proof);
                reduction::verify(&[(block.shape(), n_log)], &mut vs)
                    .is_ok_and(|r| r[0].claim == claims[0] && r[0].matrices.check(block.circuit).is_ok())
                    && vs.finish().is_ok()
            };
            assert!(accepts(None), "{op:?}");
            for bit in [
                A_BASE + 3,
                OUT_BASE + 5,
                circuit.circuit.const_pos(),
                circuit.useful_bits() - 1,
            ] {
                assert!(!accepts(Some(bit)), "{op:?}: bit {bit}");
            }
        }
    }

    #[test]
    fn a_mixed_batch_proves_each_circuit() {
        // Invariant: a batch of circuits proves each of them.
        // The verifier recovers each claim, and each is its witness's truth.
        //
        // Fixture state, (operation, log instances, rows): three block sizes, from no rows to full batches.
        const LABEL: &[u8] = b"flock-arith-batch-test";
        let ops = OPS.map(U64Circuit::new);
        assert_eq!(ops.each_ref().map(U64Circuit::k_log), [8, 12, 13]);
        let shapes = [(0, 9, 0), (1, 7, 40), (2, 3, 5), (0, 6, 64), (1, 8, 130)];
        let blocks: Vec<(Block<'_>, usize)> = shapes.iter().map(|&(op, n_log, _)| (ops[op].block(), n_log)).collect();
        let tables = |f: usize| -> Witness {
            let (op, n_log, rows) = shapes[f];
            ops[op].witness(&pairs(rows, 0x3A15 + f as u64), n_log)
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
            .map(|&(op, n_log, _)| ops[op].k_log() + n_log)
            .max()
            .unwrap()
            - 6;
        let n_lincheck = shapes.iter().map(|&(op, ..)| ops[op].k_log()).max().unwrap() - 6;
        let zerocheck_len = 64 + 2 * n_zerocheck + 3 * shapes.len();
        for f in 0..shapes.len() {
            for word in [
                64 + 2 * n_zerocheck + 3 * f,
                zerocheck_len + 2 * n_lincheck + 65 * f + 3,
            ] {
                let mut bad = proof.clone();
                bad.stream[word] += F192::ONE;
                assert!(accepts(&bad).is_none(), "circuit {f}, word {word}");
            }
        }
    }
}
