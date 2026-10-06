//! One u64 operation as a whole circuit, its witness by word arithmetic.

use super::add::Adder;
use super::mul::Multiplier;
use super::{Instance, or_bits};
use crate::circuit::{Builder, Circuit};
use crate::reduction::Block;
use crate::witness::Witness;

pub(crate) const A_BASE: usize = 0;
pub(crate) const B_BASE: usize = 64;
pub(crate) const OUT_BASE: usize = 128;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum U64Op {
    /// `a + b mod 2^64`.
    WrappingAdd,
    /// `a·b mod 2^64`.
    WrappingMul,
    /// `a·b` as a u128.
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

impl Instance<'_> {
    /// `width` rows from `slot` whose B side is the constant, with `A·z = z = v`.
    fn unit_rows(&mut self, slot: usize, v: u128, width: usize) {
        or_bits(self.z, slot, v);
        or_bits(self.az, slot, v);
        or_bits(self.bz, slot, u128::MAX >> (128 - width));
    }
}

/// What an operation's witness is computed from, besides its inputs.
enum Plan {
    Add(Adder),
    Mul(Multiplier),
}

pub struct U64Circuit {
    op: U64Op,
    circuit: Circuit,
    plan: Plan,
}

impl U64Circuit {
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
        for (i, wire) in out.into_iter().enumerate() {
            c.output(0, i, wire);
        }
        let circuit = c.finish();
        assert_eq!(circuit.const_pos(), OUT_BASE + n);
        Self { op, circuit, plan }
    }

    pub const fn circuit(&self) -> &Circuit {
        &self.circuit
    }

    pub const fn k_log(&self) -> usize {
        self.circuit.k_log()
    }

    pub const fn useful_bits(&self) -> usize {
        self.circuit.useful_bits()
    }

    pub fn block(&self) -> Block<'_> {
        self.circuit.block()
    }

    /// The witness of `pairs`, padded with `(0, 0)` to `2^n_blocks_log` instances.
    pub fn generate_witness(&self, pairs: &[(u64, u64)], n_blocks_log: usize) -> Witness {
        let n = self.op.out_bits();
        self.circuit
            .generate_witness_with(pairs, &(0, 0), n_blocks_log, |&(a, b), z, az, bz| {
                let mut witness = Instance { z, az, bz };
                let out = match &self.plan {
                    Plan::Add(adder) => adder.witness(a, b, &mut witness),
                    Plan::Mul(multiplier) => multiplier.witness_into(a, b, &mut witness),
                };
                witness.unit_rows(A_BASE, a as u128, 64);
                witness.unit_rows(B_BASE, b as u128, 64);
                witness.unit_rows(OUT_BASE, out, n);
                witness.unit_rows(self.circuit.const_pos(), 1, 1);
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lincheck::LincheckCircuit;
    use crate::reduction::{self, Instance};
    use fiat_shamir::transcript::{ProofTranscript, ProverState, VerifierState};
    use primitives::field::F192;
    use primitives::test_util::Rng;

    const OPS: [U64Op; 3] = [U64Op::WrappingAdd, U64Op::WrappingMul, U64Op::WideningMul];

    fn native(op: U64Op, a: u64, b: u64) -> u128 {
        let (a, b) = (a as u128, b as u128);
        match op {
            U64Op::WrappingAdd => (a + b) as u64 as u128,
            U64Op::WrappingMul => (a * b) as u64 as u128,
            U64Op::WideningMul => a * b,
        }
    }

    /// Every pairing of the carry-heavy edge values, then random pairs.
    fn pairs(n: usize, seed: u64) -> Vec<(u64, u64)> {
        const EDGES: [u64; 6] = [0, 1, 2, 1 << 63, u64::MAX - 1, u64::MAX];
        let mut rng = Rng::new(seed);
        EDGES
            .iter()
            .flat_map(|&x| EDGES.iter().map(move |&y| (x, y)))
            .chain(std::iter::repeat_with(|| (rng.next_u64(), rng.next_u64())))
            .take(n)
            .collect()
    }

    /// The committed result is the native one and every row holds, which ties
    /// the word-level witness to the gate list the walks read.
    #[test]
    fn witness_is_the_result_and_satisfies_r1cs() {
        let n_log = 6;
        for op in OPS {
            let circuit = U64Circuit::new(op);
            let k = circuit.circuit.n_cols();
            let pairs = pairs(1 << n_log, 0x3A11);
            let z = circuit.generate_witness(&pairs, n_log).z;
            for (t, &(x, y)) in pairs.iter().enumerate() {
                let word = |w: usize| z[t * (k / 64) + w];
                let out = (word(2) as u128 | (word(3) as u128) << 64) & (u128::MAX >> (128 - op.out_bits()));
                assert_eq!((word(0), word(1), out), (x, y, native(op, x, y)), "{op:?}");
                let block: Vec<F192> = (0..k)
                    .map(|i| {
                        if (z[(t * k + i) / 64] >> (i % 64)) & 1 == 1 {
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

    /// The generic walk of the gate list writes the very tables the word arithmetic does.
    #[test]
    fn generic_witness_is_the_word_arithmetic() {
        let n_log = 4;
        for op in OPS {
            let circuit = U64Circuit::new(op);
            let pairs = pairs(1 << n_log, 0x3A13);
            let rows: Vec<[u64; 2]> = pairs.iter().map(|&(a, b)| [a, b]).collect();
            let fast = circuit.generate_witness(&pairs, n_log);
            let generic = circuit.circuit.generate_witness(&rows, n_log);
            assert!(fast == generic, "{op:?}");
        }
    }

    /// The reduction verifies an honest batch, which is also what ties the
    /// prover's backward walk and the `A·z`, `B·z` tables to the verifier's
    /// forward walk, and rejects one flipped witness bit.
    #[test]
    fn reduction_roundtrip_rejects_tampering() {
        const LABEL: &[u8] = b"flock-arith-reduction-test";
        // The zerocheck needs a cube of at least 2^13 bits.
        let n_log = 5;
        for op in OPS {
            let circuit = U64Circuit::new(op);
            let block = circuit.block();
            let pairs = pairs(1 << n_log, 0x3A12);
            let run = |tamper: Option<usize>| {
                let mut witness = circuit.generate_witness(&pairs, n_log);
                if let Some(bit) = tamper {
                    witness.z[bit / 64] ^= 1 << (bit % 64);
                    witness.stripes[bit] ^= 1;
                }
                let mut ps = ProverState::from_label(LABEL);
                let instance = Instance {
                    block,
                    n_blocks_log: n_log,
                    witness,
                };
                let claims = reduction::prove(&[instance], &mut ps);
                let proof = ps.into_proof();
                let mut vs = VerifierState::from_label(LABEL, &proof);
                reduction::verify(&[(block.shape(), n_log)], &mut vs)
                    .is_ok_and(|r| r[0].claim == claims[0] && r[0].matrices.check(block.circuit).is_ok())
                    && vs.finish().is_ok()
            };
            assert!(run(None), "{op:?}");
            for bit in [
                A_BASE + 3,
                OUT_BASE + 5,
                circuit.circuit.const_pos(),
                circuit.useful_bits() - 1,
            ] {
                assert!(!run(Some(bit)), "{op:?}: flipping bit {bit} must reject");
            }
        }
    }

    /// **A batch of circuits proves each of them.** Circuits of three block sizes
    /// (`k_log` 8, 12 and 13) and mixed instance counts and heights, from no rows at
    /// all to a batch of rows in full: the verifier recovers each circuit's claim,
    /// and each is its witness's true slices at its point. A flipped witness bit in
    /// any one circuit, or a wrong claim of any one circuit on the stream, is
    /// rejected.
    #[test]
    fn a_mixed_batch_proves_each_circuit() {
        const LABEL: &[u8] = b"flock-arith-batch-test";
        let ops = OPS.map(U64Circuit::new);
        assert_eq!(ops.each_ref().map(U64Circuit::k_log), [8, 12, 13]);
        // (operation, log instances, height)
        let shapes = [(0, 9, 0), (1, 7, 40), (2, 3, 5), (0, 6, 64), (1, 8, 130)];
        let blocks: Vec<(Block<'_>, usize)> = shapes.iter().map(|&(op, n_log, _)| (ops[op].block(), n_log)).collect();
        let tables = |f: usize| -> Witness {
            let (op, n_log, h) = shapes[f];
            ops[op].generate_witness(&pairs(h, 0x3A15 + f as u64), n_log)
        };
        let whole: Vec<Witness> = (0..shapes.len()).map(tables).collect();
        let prove = |tables: Vec<Witness>| {
            let instances: Vec<Instance<'_>> = (tables.into_iter().zip(&blocks))
                .map(|(witness, &(block, n_blocks_log))| Instance {
                    block,
                    n_blocks_log,
                    witness,
                })
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

        let (proof, claims) = prove(whole.clone());
        let replays = accepts(&proof).expect("an honest batch verifies");
        for (f, ((replay, claim), Witness { z, .. })) in replays.iter().zip(&claims).zip(&whole).enumerate() {
            assert_eq!(&replay.claim, claim, "circuit {f}'s claim");
            // Word `w` of the packed witness is position `w` past the skip, bit `i` its slice `i`.
            let eq = primitives::multilinear::eq_table(&claim.suffix_point);
            let slices: Vec<F192> = (0..64)
                .map(|i| {
                    (z.iter().zip(&eq)).fold(F192::ZERO, |acc, (&w, &e)| if w >> i & 1 == 1 { acc + e } else { acc })
                })
                .collect();
            assert_eq!(claim.s_hat_v, slices, "circuit {f}'s slices are its witness's");
        }

        // A flipped bit (an output bit of instance 1) in any one circuit.
        for f in 0..shapes.len() {
            let mut tampered: Vec<Witness> = (0..shapes.len()).map(tables).collect();
            let k = 1usize << blocks[f].0.k_log;
            let Witness { z, stripes, .. } = &mut tampered[f];
            let bit = k + OUT_BASE + 5;
            z[bit / 64] ^= 1 << (bit % 64);
            stripes[OUT_BASE + 5] ^= 1 << 1;
            let (bad, _) = prove(tampered);
            assert!(accepts(&bad).is_none(), "a flipped bit of circuit {f} must reject");
        }

        // A wrong claim of any one circuit: its zerocheck `â`, or one of its slices.
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
                zerocheck_len + 2 * n_lincheck + 64 * f + 3,
            ] {
                let mut bad = proof.clone();
                bad.stream[word].c0 ^= 1;
                assert!(
                    accepts(&bad).is_none(),
                    "a wrong claim of circuit {f} (word {word}) must reject"
                );
            }
        }
    }
}
