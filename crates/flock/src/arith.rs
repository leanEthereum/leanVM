//! u64 arithmetic as Flock R1CS circuits, one operation per block: wrapping
//! addition ([`add`]), and multiplication ([`mul`]) wrapping or widening.
//!
//! Each is a [`crate::circuit`] gate list over the ports `a`, `b` and the result, in
//! that order ([`A_BASE`], [`B_BASE`], [`OUT_BASE`]), built from [`add::Adder`] and
//! [`mul::Multiplier`], which take wires and return wires and so compose into
//! larger circuits. Here the witness is not the generic walk of the gate list but
//! word arithmetic on the structure the list is built from, one instance at a time.

pub mod add;
pub mod mul;

use crate::circuit::{Builder, Circuit};
use crate::reduction::Block;
use zk_alloc::ArenaVec;

pub const A_BASE: usize = 0;
pub const B_BASE: usize = 64;
pub const OUT_BASE: usize = 128;

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
    pub const fn out_bits(self) -> usize {
        match self {
            Self::WrappingAdd | Self::WrappingMul => 64,
            Self::WideningMul => 128,
        }
    }
}

/// One instance's words of `z`, `A·z` and `B·z`.
struct Instance<'a> {
    z: &'a mut [u64],
    az: &'a mut [u64],
    bz: &'a mut [u64],
}

impl Instance<'_> {
    /// `width` rows from `slot` whose B side is the constant, with `A·z = z = v`.
    fn unit_rows(&mut self, slot: usize, v: u128, width: usize) {
        or_bits(self.z, slot, v);
        or_bits(self.az, slot, v);
        or_bits(self.bz, slot, u128::MAX >> (128 - width));
    }

    /// Product rows from `slot`, one per position of `mask`, with `A·z = left`,
    /// `B·z = right` and `z = left·right`.
    fn products(&mut self, slot: usize, mask: u128, left: u128, right: u128) {
        if mask != 0 {
            let shift = mask.trailing_zeros();
            or_bits(self.z, slot, (left & right & mask) >> shift);
            or_bits(self.az, slot, (left & mask) >> shift);
            or_bits(self.bz, slot, (right & mask) >> shift);
        }
    }
}

/// OR `v` into `buf` from bit `at`.
#[inline(always)]
fn or_bits(buf: &mut [u64], at: usize, v: u128) {
    let s = at % 64;
    let words = [
        (v << s) as u64,
        ((v >> 1) >> (63 - s)) as u64,
        ((v >> 1) >> (127 - s)) as u64,
    ];
    for (w, x) in buf[at / 64..].iter_mut().zip(words) {
        *w |= x;
    }
}

/// What an operation's witness is computed from, besides its inputs.
enum Plan {
    Add(add::Adder),
    Mul(mul::Multiplier),
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
                let (out, adder) = add::Adder::build(&mut c, &a, &b);
                (out, Plan::Add(adder))
            }
            U64Op::WrappingMul | U64Op::WideningMul => {
                let (out, multiplier) = mul::Multiplier::build(&mut c, &a, &b, n);
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

    /// `(z, a, b, z_lincheck)` for `pairs` padded with `(0, 0)` to
    /// `2^n_blocks_log` instances: the bit-packed `z`, `A·z` and `B·z`
    /// (`2^k_log / 64` words per instance), and lincheck's byte stripes.
    pub fn generate_witness(
        &self,
        pairs: &[(u64, u64)],
        n_blocks_log: usize,
    ) -> (ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u8>) {
        self.witness_padded(pairs, &(0, 0), 1 << n_blocks_log)
    }

    /// [`Self::generate_witness`] over `n_instances`, `padding` past `pairs`.
    fn witness_padded(
        &self,
        pairs: &[(u64, u64)],
        padding: &(u64, u64),
        n_instances: usize,
    ) -> (ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u8>) {
        let n = self.op.out_bits();
        self.circuit
            .generate_witness_with(pairs, padding, n_instances, &mut [], |&(a, b), z, az, bz| {
                let mut witness = Instance { z, az, bz };
                let out = match &self.plan {
                    Plan::Add(adder) => adder.witness(a, b, &mut witness),
                    Plan::Mul(multiplier) => multiplier.witness(a, b, &mut witness),
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
    use fiat_shamir::transcript::{ProverState, VerifierState};
    use primitives::field::F192;
    use primitives::test_rng::Rng;

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
            let (z, _, _, _) = circuit.generate_witness(&pairs, n_log);
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
            assert!(fast.0[..] == generic.0[..], "{op:?}: z");
            assert!(fast.1[..] == generic.1[..], "{op:?}: A·z");
            assert!(fast.2[..] == generic.2[..], "{op:?}: B·z");
            assert!(fast.3[..] == generic.3[..], "{op:?}: stripes");
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
                let (mut z, a, b, mut z_lincheck) = circuit.generate_witness(&pairs, n_log);
                if let Some(bit) = tamper {
                    z[bit / 64] ^= 1 << (bit % 64);
                    z_lincheck[bit] ^= 1;
                }
                let mut ps = ProverState::from_label(LABEL);
                let instance = Instance {
                    block,
                    n_blocks_log: n_log,
                    z: &z,
                    a: &a,
                    b: &b,
                    pad: None,
                    z_lincheck: &z_lincheck,
                };
                let claims = reduction::prove(&[instance], &mut ps);
                let proof = ps.into_proof();
                let mut vs = VerifierState::from_label(LABEL, &proof);
                reduction::verify(&[(block, n_log)], &mut vs).is_ok_and(|r| r[0].claim == claims[0])
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

    /// A batch whose instances past its explicit ones repeat its last row proves exactly
    /// as the whole batch written out: the zerocheck and lincheck take the rest as copies
    /// of one 64-instance unit, for any number of whole units.
    #[test]
    fn a_batch_short_of_its_cube_proves_as_the_whole_cube() {
        type Tables = (ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u8>);
        const LABEL: &[u8] = b"flock-arith-tail-test";
        const UNIT: usize = 64;
        let circuit = U64Circuit::new(U64Op::WrappingAdd);
        let block = circuit.block();
        let prove = |n_log: usize, (z, a, b, z_lincheck): Tables, unit: Option<&Tables>| {
            let mut ps = ProverState::from_label(LABEL);
            let instance = Instance {
                block,
                n_blocks_log: n_log,
                z: &z,
                a: &a,
                b: &b,
                pad: unit.map(|(z, a, b, _)| [&z[..], &a[..], &b[..]]),
                z_lincheck: &z_lincheck,
            };
            let claims = reduction::prove(&[instance], &mut ps);
            (ps.into_proof(), claims)
        };
        // A cube whose tail is gone by the table rounds, and one with paired table
        // passes that grow the unit, more than once.
        for n_log in [7, 18] {
            let full = 1usize << n_log;
            let mut heights = vec![
                0,
                1,
                62,
                63,
                64,
                65,
                127,
                128,
                full / 2 - 1,
                full / 2,
                full / 2 + 1,
                full - 65,
                full - 64,
                full - 63,
                full - 2,
                full - 1,
            ];
            heights.retain(|&h| h < full);
            heights.sort_unstable();
            heights.dedup();
            for h in heights {
                // The rows to the height, the last one the row every later instance repeats.
                let rows = pairs(h + 1, 0x3A14 + h as u64);
                let padding = rows[h];
                let explicit = (h + 1).next_multiple_of(UNIT).min(full);
                let unit = (explicit < full).then(|| circuit.witness_padded(&[], &padding, UNIT));
                let short = prove(n_log, circuit.witness_padded(&rows, &padding, explicit), unit.as_ref());
                let whole = prove(n_log, circuit.witness_padded(&rows, &padding, full), None);
                assert!(short == whole, "2^{n_log} instances, height {h}");
            }
        }
    }

    /// **A batch of circuits proves each of them.** Circuits of three block sizes
    /// (`k_log` 8, 12 and 13) and mixed instance counts and heights, from the padding
    /// row alone (`h = 0`) to a batch written out in full, some with a padding tail of
    /// one or several units: the batch proves as the batches written out in full, the
    /// verifier recovers each circuit's claim, and each is its witness's true slices
    /// at its point. A flipped witness bit in any one circuit, or a wrong claim of any
    /// one circuit on the stream, is rejected.
    #[test]
    fn a_mixed_batch_proves_each_circuit() {
        type Tables = (ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u8>);
        const LABEL: &[u8] = b"flock-arith-batch-test";
        const UNIT: usize = 64;
        let ops = OPS.map(U64Circuit::new);
        // (operation, log instances, height)
        let shapes = [(0, 9, 0), (1, 7, 40), (2, 3, 5), (0, 6, 63), (1, 8, 130)];
        let blocks: Vec<(Block<'_>, usize)> = shapes.iter().map(|&(op, n_log, _)| (ops[op].block(), n_log)).collect();
        // Circuit `f`'s batch: its committed rows, then its padding unit when instances
        // are left to it, and the whole batch written out.
        let tables = |f: usize| -> ((Tables, Option<Tables>), Tables) {
            let (op, n_log, h) = shapes[f];
            let (circuit, full) = (&ops[op], 1usize << n_log);
            let rows = pairs(h + 1, 0x3A15 + f as u64);
            let padding = rows[h];
            let explicit = (h + 1).next_multiple_of(UNIT).min(full);
            let unit = (explicit < full).then(|| circuit.witness_padded(&[], &padding, UNIT));
            (
                (circuit.witness_padded(&rows, &padding, explicit), unit),
                circuit.witness_padded(&rows, &padding, full),
            )
        };
        let (short, whole): (Vec<_>, Vec<_>) = (0..shapes.len()).map(tables).unzip();
        assert!(short.iter().filter(|(_, unit)| unit.is_some()).count() >= 2);
        let prove = |tables: &[(&Tables, Option<&Tables>)]| {
            let instances: Vec<Instance<'_>> = (tables.iter().zip(&blocks))
                .map(|(((z, a, b, z_lincheck), unit), &(block, n_blocks_log))| Instance {
                    block,
                    n_blocks_log,
                    z,
                    a,
                    b,
                    pad: unit.map(|(z, a, b, _)| [&z[..], &a[..], &b[..]]),
                    z_lincheck,
                })
                .collect();
            let mut ps = ProverState::from_label(LABEL);
            let claims = reduction::prove(&instances, &mut ps);
            (ps.into_proof(), claims)
        };
        let accepts = |proof: &fiat_shamir::transcript::Proof| {
            let mut vs = VerifierState::from_label(LABEL, proof);
            reduction::verify(&blocks, &mut vs).ok().filter(|_| vs.finish().is_ok())
        };

        let (proof, claims) = prove(&short.iter().map(|(t, u)| (t, u.as_ref())).collect::<Vec<_>>());
        let dense: Vec<(&Tables, Option<&Tables>)> = whole.iter().map(|t| (t, None)).collect();
        assert!(
            prove(&dense) == (proof.clone(), claims.clone()),
            "the tails prove as the batches written out"
        );
        let replays = accepts(&proof).expect("an honest batch verifies");
        for (f, ((replay, claim), (z, ..))) in replays.iter().zip(&claims).zip(&whole).enumerate() {
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
            let mut tampered: Vec<Tables> = (0..shapes.len()).map(|f| tables(f).1).collect();
            let k = 1usize << blocks[f].0.k_log;
            let (z, _, _, z_lincheck) = &mut tampered[f];
            let bit = k + OUT_BASE + 5;
            z[bit / 64] ^= 1 << (bit % 64);
            z_lincheck[OUT_BASE + 5] ^= 1 << 1;
            let (bad, _) = prove(&tampered.iter().map(|t| (t, None)).collect::<Vec<_>>());
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
