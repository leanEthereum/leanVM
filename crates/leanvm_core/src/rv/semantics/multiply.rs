//! The multiplications: the low and the high word of a product.

use super::{InstructionClass, sext32};
use crate::rv::circuits::{ClassCircuit, WordGadgets};
use flock::circuit::{Builder, Circuit};
use flock::gadgets::Multiplier;
use std::sync::OnceLock;

/// One low multiplication instance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Mul {
    /// Whether to sign-extend a word product: one of the legal words.
    pub flags: u64,
    /// The first factor.
    pub v1: u64,
    /// The second factor.
    pub v2: u64,
}

impl Mul {
    /// Sign-extend the low 32 bits of the product.
    pub const WORD: u64 = 1 << 0;
}

impl InstructionClass for Mul {
    /// With or without the word form.
    const LEGAL: &'static [u64] = &[0, Self::WORD];

    /// The low word of the product.
    type Output = u64;

    fn eval(&self) -> u64 {
        let product = self.v1.wrapping_mul(self.v2);
        if self.flags & Self::WORD != 0 {
            sext32(product)
        } else {
            product
        }
    }
}

/// One high multiplication instance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Mulh {
    /// Which operands are signed: one of the legal words.
    pub flags: u64,
    /// The first factor.
    pub v1: u64,
    /// The second factor.
    pub v2: u64,
}

impl Mulh {
    /// The first operand is signed.
    pub const SIGNED_1: u64 = 1 << 0;
    /// The second operand is signed.
    pub const SIGNED_2: u64 = 1 << 1;
}

impl InstructionClass for Mulh {
    /// `mulh`, `mulhsu`, `mulhu`.
    const LEGAL: &'static [u64] = &[Self::SIGNED_1 | Self::SIGNED_2, Self::SIGNED_1, 0];

    /// The high word of the 128-bit product.
    type Output = u64;

    fn eval(&self) -> u64 {
        let widen = |v: u64, signed: bool| if signed { v as i64 as i128 } else { v as i128 };
        let (s1, s2) = (self.flags & Self::SIGNED_1 != 0, self.flags & Self::SIGNED_2 != 0);
        (widen(self.v1, s1).wrapping_mul(widen(self.v2, s2)) >> 64) as u64
    }
}

impl ClassCircuit for Mul {
    /// The low word of the product: `(v1, v2, flags) -> out`.
    ///
    /// A word multiplication sign-extends the low 32 bits.
    ///
    /// The gates are `clean::mul64`, checked in `LeanVMCircuits.Mul`: the multiplier, then the word selector.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 1], &[64]);
        let [v1, v2] = [0, 1].map(|port| c.input::<64>(port));
        let f = c.input::<1>(2);
        let multiplier = Multiplier::plan::<64>(c.next_slot());
        let out = flock::clean::mul64(&mut c, &v1, &v2, &f);
        c.output_word(0, &out);
        let mux_slot = multiplier.end_slot();
        let _ = MUL_PLAN.set(LowPlan { multiplier, mux_slot });
        c.finish()
    }
}

impl ClassCircuit for Mulh {
    /// The high word of the product: `(v1, v2, flags) -> out`.
    ///
    /// A negative operand reads as its unsigned value minus `2^64`.
    ///
    /// So the signed high word is the unsigned one, corrected:
    ///
    /// ```text
    ///     high(v1 * v2) = high_u(v1 * v2) - [v1 < 0] * v2 - [v2 < 0] * v1    (mod 2^64)
    /// ```
    ///
    /// The gates are `clean::mulh64`, checked in `LeanVMCircuits.Mulh`.
    /// Each correction is `negative`, the complement of the other operand gated by it, then `high` plus both.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 2], &[64]);
        let [v1, v2] = [0, 1].map(|port| c.input::<64>(port));
        let f = c.input::<2>(2);
        let multiplier = Multiplier::plan::<128>(c.next_slot());
        let high = flock::clean::mulh64(&mut c, &v1, &v2, &f);
        let corrections = [0, 1].map(|i| multiplier.end_slot() + i * CORRECTION_PRODUCTS);

        c.output_word(0, &high);
        let _ = MULH_PLAN.set(HighPlan {
            multiplier,
            corrections,
        });
        c.finish()
    }
}

/// The unsigned multiplier and the word-result selector's first product slot.
struct LowPlan {
    multiplier: Multiplier,
    mux_slot: usize,
}

/// A signed correction's products: `negative`, the 64 gated complement bits, then the 64 carries of the sum.
const CORRECTION_PRODUCTS: usize = 1 + 64 + 64;

/// The unsigned multiplier and each signed correction's first product slot.
struct HighPlan {
    multiplier: Multiplier,
    corrections: [usize; 2],
}

/// Building the low multiplication records its product runs once.
static MUL_PLAN: OnceLock<LowPlan> = OnceLock::new();

/// Building the high multiplication records its product runs once.
static MULH_PLAN: OnceLock<HighPlan> = OnceLock::new();

impl Mul {
    /// Fill eight low multiplication witnesses in two groups of four word lanes.
    pub(crate) fn witness_batch(inputs: &[&[u64]; 8], z: &mut [u64], az: &mut [u64], bz: &mut [u64]) {
        // A four-lane word-major table lets adjacent instances use vector operations.
        let plan = MUL_PLAN.get().unwrap_or_else(|| {
            Self::circuit();
            MUL_PLAN
                .get()
                .expect("circuit construction records multiplication products")
        });
        let words = z.len() / 8;
        assert_eq!(words, 64, "low multiplication has 4096 packed bits per instance");
        for group in 0..2 {
            let inputs: [&[u64]; 4] = std::array::from_fn(|l| inputs[4 * group + l]);
            let mut packed = [[[0u64; 4]; 64]; 3];
            let [z4, az4, bz4] = &mut packed;
            let a = std::array::from_fn(|l| inputs[l][0]);
            let b = std::array::from_fn(|l| inputs[l][1]);
            let product = plan.multiplier.witness_batch4(a, b, z4, az4, bz4);

            // The 32 high output bits select the sign extension for word multiplication.
            let flags: [u64; 4] = std::array::from_fn(|l| inputs[l][2] & 1);
            let difference: [u64; 4] =
                std::array::from_fn(|l| (product[l] >> 32) ^ ((product[l] >> 31 & 1).wrapping_neg() >> 32));
            let mask = flags.map(|v| v.wrapping_neg() & 0xffff_ffff);
            let selected: [u64; 4] = std::array::from_fn(|l| mask[l] & difference[l]);
            let out = std::array::from_fn(|l| product[l] ^ (selected[l] << 32));
            let (word, shift) = (plan.mux_slot / 64, plan.mux_slot % 64);
            for (buf, bits) in [(&mut *z4, selected), (&mut *az4, mask), (&mut *bz4, difference)] {
                buf[word] = std::array::from_fn(|l| buf[word][l] | (bits[l] << shift));
                buf[word + 1] = std::array::from_fn(|l| buf[word + 1][l] | ((bits[l] >> 1) >> (63 - shift)));
            }

            // Ports and the constant are ordinary linear rows in each independent lane.
            z4[0] = a;
            z4[1] = b;
            z4[2] = flags;
            z4[3] = out;
            az4[..4].copy_from_slice(&z4[..4]);
            bz4[..4].copy_from_slice(&[[u64::MAX; 4], [u64::MAX; 4], [1; 4], [u64::MAX; 4]]);
            for buf in [&mut *z4, &mut *az4, &mut *bz4] {
                buf[4] = buf[4].map(|v| v | 1);
            }

            // Convert once from adjacent vector lanes to the committed instance-major layout.
            for (src, dst) in packed.iter().zip([&mut *z, &mut *az, &mut *bz]) {
                for (word, lanes) in src.iter().enumerate() {
                    for (lane, &value) in lanes.iter().enumerate() {
                        dst[(4 * group + lane) * words + word] = value;
                    }
                }
            }
        }
    }
}

impl Mulh {
    /// Fill the high multiplication's packed witness using native word arithmetic.
    pub(crate) fn witness(inputs: &[u64], z: &mut [u64], az: &mut [u64], bz: &mut [u64]) {
        // Signed corrections are applied after the same unsigned 128-bit product.
        let plan = MULH_PLAN.get().unwrap_or_else(|| {
            Self::circuit();
            MULH_PLAN
                .get()
                .expect("circuit construction records multiplication products")
        });
        let mut high = (plan.multiplier.witness(inputs[0], inputs[1], z, az, bz) >> 64) as u64;
        for (i, &slot) in plan.corrections.iter().enumerate() {
            // A signed negative operand contributes minus the other operand to the high word.
            let signed = inputs[2] >> i & 1;
            let sign_bit = inputs[i] >> 63;
            let negative = signed & sign_bit;
            product_rows(z, az, bz, slot, signed, sign_bit);

            // Two's complement subtraction is the gated complement plus its low carry.
            let complemented = !inputs[1 - i];
            let subtrahend = negative.wrapping_neg() & complemented;
            product_rows(z, az, bz, slot + 1, negative.wrapping_neg(), complemented);
            let sum = high.wrapping_add(subtrahend).wrapping_add(negative);
            let carry = sum ^ high ^ subtrahend;
            product_rows(z, az, bz, slot + 65, high ^ carry, subtrahend ^ carry);
            high = sum;
        }
        ports(inputs, 2, high, z, az, bz);
    }
}

/// Fill three input ports, the result and the constant.
fn ports(inputs: &[u64], flag_bits: usize, out: u64, z: &mut [u64], az: &mut [u64], bz: &mut [u64]) {
    // Narrow flags leave their spare port bits at zero in all three tables.
    for (i, bits) in [64, 64, flag_bits].into_iter().enumerate() {
        let mask = u64::MAX >> (64 - bits);
        (z[i], az[i], bz[i]) = (inputs[i] & mask, inputs[i] & mask, mask);
    }
    (z[3], az[3], bz[3]) = (out, out, u64::MAX);

    // Bit 256 is the constant immediately after the four word ports.
    for buf in [z, az, bz] {
        buf[4] |= 1;
    }
}

/// Write a contiguous run of at most 64 product rows.
fn product_rows(z: &mut [u64], az: &mut [u64], bz: &mut [u64], slot: usize, left: u64, right: u64) {
    // A product row records both factors as well as their conjunction.
    for (buf, bits) in [(z, left & right), (az, left), (bz, right)] {
        let (word, shift) = (slot / 64, slot % 64);
        buf[word] |= bits << shift;
        buf[word + 1] |= (bits >> 1) >> (63 - shift);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::Class;
    use crate::rv::semantics::tests::{Ports, circuit_matches_reference, edge_word};
    use crate::tables::spec::InstanceWitness;
    use fiat_shamir::{ProverState, SessionId, VerifierState};
    use flock::BatchRows;
    use flock::reduction;
    use flock::test_util::Witness;
    use primitives::test_util::Rng;
    use proptest::prelude::*;
    use proptest::sample::select;
    use proptest::strategy::BoxedStrategy;

    /// Fill the low multiplication's packed witness using native word arithmetic.
    fn low_witness(inputs: &[u64], z: &mut [u64], az: &mut [u64], bz: &mut [u64]) {
        // Circuit construction fixes product positions before any instance is written.
        let plan = MUL_PLAN.get().unwrap_or_else(|| {
            Mul::circuit();
            MUL_PLAN
                .get()
                .expect("circuit construction records multiplication products")
        });
        let product = plan.multiplier.witness(inputs[0], inputs[1], z, az, bz) as u64;

        // The word selector commits only the differences in bits 32 through 63.
        let word = inputs[2] & 1;
        let high = product >> 32;
        let sign = (product >> 31 & 1).wrapping_neg() >> 32;
        let difference = high ^ sign;
        product_rows(z, az, bz, plan.mux_slot, word.wrapping_neg() & 0xffff_ffff, difference);
        let out = product ^ ((word.wrapping_neg() & difference) << 32);
        ports(inputs, 1, out, z, az, bz);
    }

    /// Any low multiplication instance.
    impl Arbitrary for Mul {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            (select(Self::LEGAL), edge_word(), edge_word())
                .prop_map(|(flags, v1, v2)| Self { flags, v1, v2 })
                .boxed()
        }
    }

    /// Any high multiplication instance.
    impl Arbitrary for Mulh {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            (select(Self::LEGAL), edge_word(), edge_word())
                .prop_map(|(flags, v1, v2)| Self { flags, v1, v2 })
                .boxed()
        }
    }

    proptest! {
        #[test]
        fn mulh_is_the_high_half_of_the_wide_product(v1 in edge_word(), v2 in edge_word()) {
            // The unsigned and signed high words, from 128-bit integers.
            prop_assert_eq!(Mulh { flags: 0, v1, v2 }.eval(), ((v1 as u128 * v2 as u128) >> 64) as u64);
            let signed = Mulh { flags: Mulh::SIGNED_1 | Mulh::SIGNED_2, v1, v2 }.eval();
            prop_assert_eq!(signed, ((v1 as i64 as i128 * v2 as i64 as i128) >> 64) as u64);
        }
    }

    /// A class's native witness of one instance.
    type NativeWitness = fn(&[u64], &mut [u64], &mut [u64], &mut [u64]);

    /// Prove `rows` with a native witness, a bit of `z` flipped if `tamper` says so, and check the proof.
    fn proves(circuit: &Circuit, rows: &[[u64; 3]], witness: NativeWitness, tamper: Option<usize>) -> bool {
        let block = circuit.block();
        let n_log = rows.len().trailing_zeros() as usize;
        let mut w = Witness::by_instance(circuit, BatchRows::new(rows, &rows[0], n_log), |row, z, az, bz| {
            witness(row, z, az, bz);
        });
        if let Some(bit) = tamper {
            w.z[bit / 64] ^= 1 << (bit % 64);
        }
        let label = b"clean-multiplication-native-witness";
        let mut ps = ProverState::new(&SessionId::new(label), &0u64);
        let claims = reduction::prove(&[w.instance(block, n_log)], &mut ps);
        let proof = ps.into_proof();
        let mut vs = VerifierState::new(&SessionId::new(label), &0u64, &proof);
        reduction::verify(&[(block.shape(), n_log)], &mut vs)
            .is_ok_and(|r| r[0].claim == claims[0] && r[0].matrices.check(block.circuit).is_ok())
            && vs.check_eof().is_ok()
    }

    #[test]
    fn clean_multiplications_prove_native_witnesses_and_reject_flipped_bits() {
        // Invariant: the generated gates prove the native witnesses of both classes, and any flipped bit is refused.
        //
        // Mutation: a result bit, the multiplier's first and last products, and each class's last product.
        let edges = [
            0,
            1,
            2,
            (1 << 63) - 1,
            1 << 63,
            u64::MAX - 1,
            u64::MAX,
            0x0123_4567_89ab_cdef,
        ];
        let rows = |legal: &[u64]| -> Vec<[u64; 3]> {
            (0..64usize)
                .map(|i| [edges[i % 8], edges[i / 8], legal[i % legal.len()]])
                .collect()
        };
        let low = Mul::circuit();
        let high = Mulh::circuit();
        let cases: [(&Circuit, Vec<[u64; 3]>, NativeWitness); 2] = [
            (&low, rows(Mul::LEGAL), low_witness),
            (&high, rows(Mulh::LEGAL), Mulh::witness),
        ];
        for (circuit, rows, witness) in cases {
            assert!(proves(circuit, &rows, witness, None));
            let output = 64 * circuit.n_input_words();
            let first = circuit.const_pos() + 1;
            for bit in [output + 7, output + 63, first, first + 2000, circuit.useful_bits() - 1] {
                assert!(
                    !proves(circuit, &rows, witness, Some(bit)),
                    "flipping witness bit {bit} must reject"
                );
            }
        }
    }

    #[test]
    fn word_witnesses_match_the_gate_walk() {
        // Every pair covers zero, the sign boundary and the largest unsigned values.
        let edges = [0, 1, 2, (1 << 63) - 1, 1 << 63, u64::MAX - 1, u64::MAX];
        let mut rng = Rng::new(0x4D554C);
        for (circuit, flags, witness) in [
            (Mul::circuit(), Mul::LEGAL, low_witness as InstanceWitness),
            (Mulh::circuit(), Mulh::LEGAL, Mulh::witness as InstanceWitness),
        ] {
            for &flag in flags {
                // A short batch also checks that a nonzero row supplies the padding witness.
                let mut rows: Vec<[u64; 3]> = edges
                    .iter()
                    .flat_map(|&a| edges.iter().map(move |&b| [a, b, flag]))
                    .collect();
                rows.extend((0..151).map(|_| [rng.next_u64(), rng.next_u64(), flag]));
                let padding = [u64::MAX, 1 << 63, flag];

                // Exact equality checks the committed bits and both factors.
                let rows = BatchRows::new(&rows, &padding, 8);
                let walk = Witness::by_walk(&circuit, rows, |row, words| words.copy_from_slice(row));
                let native = Witness::by_instance(&circuit, rows, |row, z, az, bz| witness(row, z, az, bz));
                assert_eq!(native.z, walk.z, "committed bits, flags {flag}");
                assert_eq!(native.az, walk.az, "left factors, flags {flag}");
                assert_eq!(native.bz, walk.bz, "right factors, flags {flag}");
            }
        }
    }

    #[test]
    fn batched_low_witness_matches_the_gate_walk() {
        // Boundary operands exercise every carry pattern and both word selectors.
        let mut rng = Rng::new(0x53494D44);
        let edges = [0, 1, 2, (1 << 63) - 1, 1 << 63, u64::MAX - 1, u64::MAX];
        let mut rows: Vec<[u64; 3]> = edges
            .iter()
            .flat_map(|&a| edges.iter().enumerate().map(move |(i, &b)| [a, b, (i & 1) as u64]))
            .collect();
        rows.extend((0..151).map(|i| [rng.next_u64(), rng.next_u64(), i & 1]));
        let padding = [u64::MAX, 1 << 63, 1];
        let circuit = Mul::circuit();
        let rows = BatchRows::new(&rows, &padding, 8);
        let generic = Witness::by_walk(&circuit, rows, |row, words| words.copy_from_slice(row));
        let batched = Witness::by_batch8(&circuit, rows, |rows, z, az, bz| {
            // Padding occupies incomplete groups as well as complete trailing groups.
            let inputs = rows.map(|row| row.as_slice());
            Mul::witness_batch(&inputs, z, az, bz);
        });
        assert_eq!(batched.z, generic.z, "committed bits");
        assert_eq!(batched.az, generic.az, "left factors");
        assert_eq!(batched.bz, generic.bz, "right factors");
    }

    #[test]
    fn mul_circuit_matches_the_reference() {
        // Legal flags and edge-biased operands pin the gate list to the reference function.
        circuit_matches_reference::<Mul>(512);
    }

    #[test]
    fn mulh_circuit_matches_the_reference() {
        // Legal flags and edge-biased operands pin the gate list to the reference function.
        circuit_matches_reference::<Mulh>(512);
    }

    impl Ports for Mul {
        const CLASS: Class = Class::Mul;

        fn input_words(&self) -> Vec<u64> {
            vec![self.v1, self.v2, self.flags]
        }

        fn output_words(&self, &out: &u64) -> Vec<u64> {
            vec![out]
        }
    }

    impl Ports for Mulh {
        const CLASS: Class = Class::Mulh;

        fn input_words(&self) -> Vec<u64> {
            vec![self.v1, self.v2, self.flags]
        }

        fn output_words(&self, &out: &u64) -> Vec<u64> {
            vec![out]
        }
    }
}
