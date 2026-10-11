//! The ALU: sums, differences, comparisons, bitwise logic, branches and jumps.

use super::{InstructionClass, sext32};
use crate::rv::circuits::{ClassCircuit, Products, WordGadgets};
use flock::circuit::{Builder, Circuit};

/// One ALU instance: add, subtract, compare, bitwise logic, branches and jumps.
///
/// The second operand `b` is `v2 ^ imm`.
///
/// One of the two is always zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Alu {
    /// What the ALU computes: one of its legal words.
    pub flags: u64,
    /// The first register's value.
    pub v1: u64,
    /// The second register's value.
    pub v2: u64,
    /// The immediate.
    pub imm: u64,
    /// The jump's offset: the fixed target XOR `pc + 4`, zero for an entry with none.
    ///
    /// The decision does not read it; the circuit gates it by the decision.
    pub dt: u64,
    /// The fall-through address `pc + 4`: what an indirect jump links, and what its target is taken against.
    pub pc4: u64,
}

impl Alu {
    /// Compute `v1 - b` instead of `v1 + b`.
    ///
    /// The comparisons and the branches need the difference.
    pub const SUB: u64 = 1 << 0;
    /// Sign-extend the low 32 bits of the sum.
    pub const WORD: u64 = 1 << 1;
    /// Output `v1 < b`, signed.
    pub const SEL_LT: u64 = 1 << 2;
    /// Output `v1 < b`, unsigned.
    pub const SEL_LTU: u64 = 1 << 3;
    /// Output `v1 & b`.
    pub const SEL_AND: u64 = 1 << 4;
    /// Output `v1 | b`.
    pub const SEL_OR: u64 = 1 << 5;
    /// Output `v1 ^ b`.
    pub const SEL_XOR: u64 = 1 << 6;
    /// Jump to the sum with bit 0 cleared and output `pc + 4`, as `JALR` does; set with `ALWAYS`.
    pub const INDIRECT: u64 = 1 << 7;
    /// Branch when `v1 == b`.
    pub const BR_EQ: u64 = 1 << 8;
    /// Branch when `v1 != b`.
    pub const BR_NE: u64 = 1 << 9;
    /// Branch when `v1 < b`, signed.
    pub const BR_LT: u64 = 1 << 10;
    /// Branch when `v1 >= b`, signed.
    pub const BR_GE: u64 = 1 << 11;
    /// Branch when `v1 < b`, unsigned.
    pub const BR_LTU: u64 = 1 << 12;
    /// Branch when `v1 >= b`, unsigned.
    pub const BR_GEU: u64 = 1 << 13;
    /// Always take the jump.
    pub const ALWAYS: u64 = 1 << 14;

    /// Every branch condition.
    pub const BRANCHES: u64 = Self::BR_EQ | Self::BR_NE | Self::BR_LT | Self::BR_GE | Self::BR_LTU | Self::BR_GEU;

    const fn has_flag(&self, flag: u64) -> bool {
        self.flags & flag != 0
    }

    /// What the successor adds to `pc + 4`, given the decision: zero when the jump is not taken.
    ///
    /// - A fixed jump adds its offset, the target XOR `pc + 4`.
    /// - An indirect jump has offset zero and adds the sum XOR `pc + 4`, bit 0 left out.
    /// - Its successor is then the sum with bit 0 cleared, since `pc + 4` is even.
    pub const fn jump(&self, taken: bool) -> u64 {
        let indirect = if self.has_flag(Self::INDIRECT) {
            (self.v1.wrapping_add(self.v2 ^ self.imm) ^ self.pc4) & !1
        } else {
            0
        };
        if taken { self.dt ^ indirect } else { 0 }
    }
}

impl InstructionClass for Alu {
    /// At most one output selector and at most one branch condition is set.
    const LEGAL: &'static [u64] = &[
        0,
        Self::SUB,
        Self::WORD,
        Self::SUB | Self::WORD,
        Self::SUB | Self::SEL_LT,
        Self::SUB | Self::SEL_LTU,
        Self::SEL_AND,
        Self::SEL_OR,
        Self::SEL_XOR,
        Self::INDIRECT | Self::ALWAYS,
        Self::SUB | Self::BR_EQ,
        Self::SUB | Self::BR_NE,
        Self::SUB | Self::BR_LT,
        Self::SUB | Self::BR_GE,
        Self::SUB | Self::BR_LTU,
        Self::SUB | Self::BR_GEU,
        Self::ALWAYS,
    ];

    /// The output, and whether the jump is taken.
    ///
    /// The output of an indirect jump is its link, `pc + 4`.
    type Output = (u64, bool);

    fn eval(&self) -> (u64, bool) {
        let (v1, b) = (self.v1, self.v2 ^ self.imm);

        // One adder serves the sum and the difference.
        let sum = if self.has_flag(Self::SUB) {
            v1.wrapping_sub(b)
        } else {
            v1.wrapping_add(b)
        };

        // The comparisons every selector and branch picks from.
        let (lt, ltu, eq) = ((v1 as i64) < (b as i64), v1 < b, v1 == b);

        // The output: one selector, or the sum when none is set.
        let out = if self.has_flag(Self::SEL_LT) {
            lt as u64
        } else if self.has_flag(Self::SEL_LTU) {
            ltu as u64
        } else if self.has_flag(Self::SEL_AND) {
            v1 & b
        } else if self.has_flag(Self::SEL_OR) {
            v1 | b
        } else if self.has_flag(Self::SEL_XOR) {
            v1 ^ b
        } else if self.has_flag(Self::INDIRECT) {
            self.pc4
        } else if self.has_flag(Self::WORD) {
            sext32(sum)
        } else {
            sum
        };

        // The jump: unconditional, or the one branch condition set.
        let taken = self.has_flag(Self::ALWAYS)
            || (self.has_flag(Self::BR_EQ) && eq)
            || (self.has_flag(Self::BR_NE) && !eq)
            || (self.has_flag(Self::BR_LT) && lt)
            || (self.has_flag(Self::BR_GE) && !lt)
            || (self.has_flag(Self::BR_LTU) && ltu)
            || (self.has_flag(Self::BR_GEU) && !ltu);
        (out, taken)
    }
}

impl ClassCircuit for Alu {
    /// The ALU: `(v1, v2, imm, flags, dt, pc4) -> (out, jump)`.
    ///
    /// It mirrors the reference function on every legal flag word.
    ///
    /// - The second operand is `b = v2 ^ imm`.
    /// - One adder gives `v1 + b`, or `v1 - b` for the comparisons.
    /// - The output is that sum, unless a selector picks a comparison or a bitwise operation.
    /// - An indirect jump outputs `pc + 4` instead, and adds to `dt` the sum XOR `pc + 4` but for bit 0.
    /// - The jump is taken always, or when the one branch condition set holds.
    /// - `jump` is that offset gated by the decision, so the successor `pc + 4 + jump` is linear in the row's columns.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 64, 15, 64, 64], &[64, 64]);
        let [v1, v2, imm] = [0, 1, 2].map(|port| c.input::<64>(port));
        let f = c.input::<15>(3);
        let [dt, pc4] = [4, 5].map(|port| c.input::<64>(port));
        let out = flock::clean::alu64(&mut c, &v1, &v2, &imm, &f, &dt, &pc4);
        c.output_word(0, &out);
        c.finish()
    }
}

impl Alu {
    /// One instance of the circuit's witness by word arithmetic: what the walk of [`Alu::circuit`] writes, into zeroed buffers.
    ///
    /// Inputs `v1`, `v2`, `imm`, the flags' 15 bits, `dt` and `pc4`, the outputs `out` and `jump` (each bit of `jump` the product `taken * offset`), the constant at bit 512, then the products:
    ///
    /// ```text
    ///     adder        64   A·z = v1 ^ c,   B·z = (b ^ sub) ^ c,  c the carries of v1 + (b ^ sub) + sub
    ///     any          63   A·z = the OR of diff's bits below,  B·z = diff's bit
    ///     sext32       32   A·z = word,  B·z = sum_31 ^ sum_i
    ///     none         64   A·z = none,  B·z = the sign-extended sum
    ///     logic       192   per bit: v1 * b, and_or * that, or_xor * diff
    ///     comparisons   2   SEL_LT * lt, SEL_LTU * ltu
    ///     indirect     64   INDIRECT * (out ^ pc4)
    ///     branches      6   each condition's flag * whether it holds
    /// ```
    pub(crate) fn witness(inputs: &[u64], z: &mut [u64], az: &mut [u64], bz: &mut [u64]) {
        const FLAG_BITS: u64 = (1 << 15) - 1;
        let (v1, v2, imm, flags) = (inputs[0], inputs[1], inputs[2], inputs[3] & FLAG_BITS);
        let (dt, pc4) = (inputs[4], inputs[5]);
        let flag = |bit: u64| u64::from(flags & bit != 0);
        let all = |bit: u64| u64::from(bit != 0).wrapping_neg();
        let b = v2 ^ imm;
        let sub = flag(Self::SUB);

        // The adder: the carry into each bit, and out of the top.
        let y = b ^ all(sub);
        let (partial, o1) = v1.overflowing_add(y);
        let (sum, o2) = partial.overflowing_add(sub);
        let carries = sum ^ v1 ^ y;
        let ltu = u64::from(!(o1 | o2));
        let lt = ltu ^ (v1 ^ b) >> 63;
        let diff = v1 ^ b;
        let ne = u64::from(diff != 0);

        let word = all(flag(Self::WORD));
        let sext_diff = ((sum >> 31 & 1).wrapping_neg() ^ sum) >> 32;
        let extended = sum ^ (word & sext_diff) << 32;
        let none = 1
            ^ flag(Self::SEL_LT)
            ^ flag(Self::SEL_LTU)
            ^ flag(Self::SEL_AND)
            ^ flag(Self::SEL_OR)
            ^ flag(Self::SEL_XOR);
        let and_or = all(flag(Self::SEL_AND) ^ flag(Self::SEL_OR));
        let or_xor = all(flag(Self::SEL_OR) ^ flag(Self::SEL_XOR));
        let both = v1 & b;
        let (lt_term, ltu_term) = (flag(Self::SEL_LT) & lt, flag(Self::SEL_LTU) & ltu);
        let selected = all(none) & extended ^ and_or & both ^ or_xor & diff ^ lt_term ^ ltu_term;

        // An indirect jump moves the output to `pc4` and the offset by the same difference but for bit 0.
        let indirect = all(flag(Self::INDIRECT));
        let link = selected ^ pc4;
        let moved = indirect & link;
        let out = selected ^ moved;
        let offset = dt ^ moved & !1;

        let conditions = [
            (Self::BR_EQ, ne ^ 1),
            (Self::BR_NE, ne),
            (Self::BR_LT, lt),
            (Self::BR_GE, lt ^ 1),
            (Self::BR_LTU, ltu),
            (Self::BR_GEU, ltu ^ 1),
        ];
        let taken = all(conditions
            .iter()
            .fold(flag(Self::ALWAYS), |acc, &(when, holds)| acc ^ flag(when) & holds));

        // The ports.
        let bits = [u64::MAX, u64::MAX, u64::MAX, FLAG_BITS, u64::MAX, u64::MAX];
        for (i, bits) in bits.into_iter().enumerate() {
            (z[i], az[i], bz[i]) = (inputs[i] & bits, inputs[i] & bits, bits);
        }
        (z[6], az[6], bz[6]) = (out, out, u64::MAX);
        (z[7], az[7], bz[7]) = (taken & offset, taken, offset);

        // The constant, then the products in the order the circuit makes them.
        let mut rows = Products::new([z, az, bz], 8);
        rows.push(1, 1, 1);
        rows.push(v1 ^ carries, y ^ carries, 64);
        let below = diff.isolate_lowest_one().wrapping_neg();
        rows.push(below & (u64::MAX >> 1), diff >> 1, 63);
        rows.push(word >> 32, sext_diff, 32);
        rows.push(all(none), extended, 64);
        rows.push_interleaved3([v1, and_or, or_xor], [b, both, diff]);
        rows.push(flag(Self::SEL_LT), lt, 1);
        rows.push(flag(Self::SEL_LTU), ltu, 1);
        rows.push(indirect, link, 64);
        for (when, holds) in conditions {
            rows.push(flag(when), holds, 1);
        }
        rows.finish();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::Class;
    use crate::rv::semantics::tests::{
        EDGES, Ports, circuit_matches_reference, edge_word, grid, word_witness_is_the_walk,
    };
    use fiat_shamir::transcript::{ProverState, VerifierState};
    use flock::reduction::{self, Instance};
    use proptest::prelude::*;
    use proptest::sample::select;
    use proptest::strategy::BoxedStrategy;
    use std::sync::LazyLock;

    /// Any ALU instance, as the decoder makes them: one of `v2` and `imm` is zero.
    impl Arbitrary for Alu {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            // Equal operands now and then, which random words never are.
            (
                select(Self::LEGAL),
                edge_word(),
                edge_word(),
                any::<bool>(),
                any::<bool>(),
                any::<u64>(),
                any::<u64>(),
            )
                .prop_map(|(flags, v1, v2, equal, immediate, dt, pc4)| {
                    let v2 = if equal { v1 } else { v2 };
                    let (v2, imm) = if immediate { (0, v2) } else { (v2, 0) };
                    Self {
                        flags,
                        v1,
                        v2,
                        imm,
                        dt,
                        pc4,
                    }
                })
                .boxed()
        }
    }

    static ALU: LazyLock<Circuit> = LazyLock::new(Alu::circuit);

    #[test]
    fn alu_circuit_matches_the_reference() {
        // Legal flags and edge-biased operands pin the gate list to the reference function.
        circuit_matches_reference::<Alu>(4096);
    }

    #[test]
    fn the_word_witness_is_the_gate_walk() {
        // Every legal flag word on edge operands: `b` an edge word or its complement, equal to `v1` on the diagonal, `dt` and `pc4` each none or all of their bits.
        let edges = grid(&[
            &EDGES,
            &EDGES,
            &[0, u64::MAX],
            Alu::LEGAL,
            &[0, u64::MAX],
            &[0, u64::MAX],
        ]);
        word_witness_is_the_walk::<Alu>(Alu::witness, edges);
    }

    #[test]
    fn flock_proves_honest_alu_instances_and_refuses_a_flipped_bit() {
        // Native packed witnesses cover every legal operation, including unconditional and indirect jumps.
        const LABEL: &[u8] = b"rv-alu-reduction-test";
        let block = ALU.block();
        let n_log = 5;
        let rows: Vec<[u64; 6]> = (0..1u64 << n_log)
            .map(|i| {
                [
                    i.wrapping_mul(0x9e37_79b9_7f4a_7c15),
                    !i,
                    0,
                    Alu::LEGAL[i as usize % Alu::LEGAL.len()],
                    i << 2,
                    i << 3,
                ]
            })
            .collect();

        // Prove the batch, optionally flipping one witness bit first, and verify.
        let accepts = |tamper: Option<usize>| {
            let mut witness = ALU.witness_by_instance(&rows, &rows[0], n_log, |row, z, az, bz| {
                Alu::witness(row, z, az, bz);
            });
            if let Some(bit) = tamper {
                witness.z[bit / 64] ^= 1 << (bit % 64);
            }
            let mut ps = ProverState::from_label(LABEL);
            let instance = Instance::of(block, n_log, &witness);
            let claims = reduction::prove(&[instance], &mut ps);
            let proof = ps.into_proof();
            let mut vs = VerifierState::from_label(LABEL, &proof);
            reduction::verify(&[(block.shape(), n_log)], &mut vs)
                .is_ok_and(|r| r[0].claim == claims[0] && r[0].matrices.check(block.circuit).is_ok())
                && vs.finish().is_ok()
        };
        assert!(accepts(None));

        // False values, committed jump products, private products, unused flags and padding must reject.
        for bit in [
            64 * ALU.n_input_words() + 5,
            64 * (ALU.n_input_words() + 1) + 3,
            ALU.useful_bits() - 1,
            3 * 64 + 15,
            (1 << ALU.k_log()) - 1,
        ] {
            assert!(!accepts(Some(bit)), "flipping bit {bit} must reject");
        }
    }

    impl Ports for Alu {
        const CLASS: Class = Class::Alu;

        fn input_words(&self) -> Vec<u64> {
            vec![self.v1, self.v2, self.imm, self.flags, self.dt, self.pc4]
        }

        // The output, and the offset the successor adds to `pc + 4`.
        fn output_words(&self, &(out, taken): &(u64, bool)) -> Vec<u64> {
            vec![out, self.jump(taken)]
        }
    }
}
