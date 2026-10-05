//! The ALU: sums, differences, comparisons, bitwise logic, branches and jumps.

use super::{InstructionClass, sext32};
use crate::rv::circuits::{ClassCircuit, Word, WordGadgets};
use crate::rv::entry::Class;
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
    const CLASS: Class = Class::Alu;

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

    fn input_words(&self) -> Vec<u64> {
        vec![self.v1, self.v2, self.imm, self.flags, self.dt, self.pc4]
    }

    /// The output, and the offset the successor adds to `pc + 4`.
    fn output_words(&self, &(out, taken): &(u64, bool)) -> Vec<u64> {
        vec![out, self.jump(taken)]
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
        let (v1, v2, imm, f, dt, pc4) = (c.input(0), c.input(1), c.input(2), c.input(3), c.input(4), c.input(5));
        let flag = |bit: u64| f[bit.trailing_zeros() as usize];
        let b = c.xor_word(&v2, &imm);

        // The difference is v1 + !b + 1.
        //
        // It borrows exactly when that sum does not carry out.
        let sub = flag(Self::SUB);
        let b_or_not: Word = b.iter().map(|&bit| c.xor(bit, sub)).collect();
        let (sum, carry_out) = c.add_with_carry(&v1, &b_or_not, sub);

        // The comparisons, from the borrow and the signs.
        //
        //     ltu = borrow
        //     lt  = borrow ^ sign(v1) ^ sign(b)
        //     eq  = no bit of v1 ^ b set
        let ltu = c.not(carry_out);
        let signs = c.xor(v1[63], b[63]);
        let lt = c.xor(ltu, signs);
        let diff = c.xor_word(&v1, &b);
        let ne = c.any(&diff);
        let eq = c.not(ne);

        // The output: the sum unless a selector is set.
        //
        //     and = v1 * b
        //     or  = v1 * b ^ (v1 ^ b)
        //     xor = v1 ^ b
        let sum = c.sext32_if(flag(Self::WORD), &sum);
        let selectors = [Self::SEL_LT, Self::SEL_LTU, Self::SEL_AND, Self::SEL_OR, Self::SEL_XOR];
        let none = selectors.iter().fold(c.one(), |acc, &s| c.xor(acc, flag(s)));
        let and_or = c.xor(flag(Self::SEL_AND), flag(Self::SEL_OR));
        let or_xor = c.xor(flag(Self::SEL_OR), flag(Self::SEL_XOR));
        let mut out = c.and_word(none, &sum);
        for i in 0..64 {
            let both = c.and(v1[i], b[i]);
            let and_term = c.and(and_or, both);
            let xor_term = c.and(or_xor, diff[i]);
            let logic = c.xor(and_term, xor_term);
            out[i] = c.xor(out[i], logic);
        }

        // A comparison is a single bit, the output's bit 0.
        let lt_term = c.and(flag(Self::SEL_LT), lt);
        let ltu_term = c.and(flag(Self::SEL_LTU), ltu);
        let compared = c.xor(lt_term, ltu_term);
        out[0] = c.xor(out[0], compared);

        // An indirect jump outputs its link, and offsets the successor by the sum's difference from it.
        //
        //     out  = out ^ indirect * (out ^ pc4)            = pc4 when indirect
        //     jump = dt  ^ indirect * (out ^ pc4), bit 0 kept = the sum with bit 0 cleared, XOR pc4
        let indirect = flag(Self::INDIRECT);
        let mut offset = dt;
        for i in 0..64 {
            let d = c.xor(out[i], pc4[i]);
            let moved = c.and(indirect, d);
            out[i] = c.xor(out[i], moved);
            if i > 0 {
                offset[i] = c.xor(offset[i], moved);
            }
        }

        // The jump: unconditional, or the one branch condition set.
        let (ge, geu) = (c.not(lt), c.not(ltu));
        let taken = [
            (Self::BR_EQ, eq),
            (Self::BR_NE, ne),
            (Self::BR_LT, lt),
            (Self::BR_GE, ge),
            (Self::BR_LTU, ltu),
            (Self::BR_GEU, geu),
        ]
        .into_iter()
        .fold(flag(Self::ALWAYS), |acc, (when, holds)| {
            let term = c.and(flag(when), holds);
            c.xor(acc, term)
        });

        // Each bit of the jump is a product written at its output position, so it costs no copy.
        c.output_word(0, &out);
        for (i, &bit) in offset.iter().enumerate() {
            c.and_output(1, i, taken, bit);
        }
        c.finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::semantics::tests::{circuit_matches_reference, edge_word};
    use fiat_shamir::transcript::{ProverState, VerifierState};
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
    fn flock_proves_honest_alu_instances_and_refuses_a_flipped_bit() {
        // Fixture: 16 instances cycling through the legal words.
        const LABEL: &[u8] = b"rv-alu-reduction-test";
        let block = ALU.block();
        let n_log = 4;
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
            let (mut z, a, b, mut z_lincheck) = ALU.generate_witness(&rows, n_log);
            if let Some(bit) = tamper {
                z[bit / 64] ^= 1 << (bit % 64);
                z_lincheck[bit] ^= 1;
            }
            let mut ps = ProverState::from_label(LABEL);
            let instance = flock::reduction::Instance {
                block,
                n_blocks_log: n_log,
                z: &z,
                a: &a,
                b: &b,
                z_lincheck: &z_lincheck,
            };
            let claims = flock::reduction::prove(&[instance], &mut ps);
            let proof = ps.into_proof();
            let mut vs = VerifierState::from_label(LABEL, &proof);
            flock::reduction::verify(&[(block, n_log)], &mut vs).is_ok_and(|r| r[0].claim == claims[0])
                && vs.finish().is_ok()
        };
        assert!(accepts(None));

        // Mutation: an output bit, a bit of the jump, the last product.
        for bit in [
            64 * ALU.n_input_words() + 5,
            64 * (ALU.n_input_words() + 1) + 3,
            ALU.useful_bits() - 1,
        ] {
            assert!(!accepts(Some(bit)), "flipping bit {bit} must reject");
        }
    }
}
