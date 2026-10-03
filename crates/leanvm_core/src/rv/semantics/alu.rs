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
    /// Clear bit 0 of the output, as `JALR` does to its target.
    pub const CLEAR_BIT0: u64 = 1 << 7;
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

    /// The flag word of a branch with function `funct3`.
    ///
    /// Returns `None` for functions 2 and 3, which are reserved.
    pub const fn branch_flags(funct3: u32) -> Option<u64> {
        let condition = match funct3 {
            0 => Self::BR_EQ,
            1 => Self::BR_NE,
            4 => Self::BR_LT,
            5 => Self::BR_GE,
            6 => Self::BR_LTU,
            7 => Self::BR_GEU,
            _ => return None,
        };
        Some(Self::SUB | condition)
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
        Self::CLEAR_BIT0,
        Self::SUB | Self::BR_EQ,
        Self::SUB | Self::BR_NE,
        Self::SUB | Self::BR_LT,
        Self::SUB | Self::BR_GE,
        Self::SUB | Self::BR_LTU,
        Self::SUB | Self::BR_GEU,
        Self::ALWAYS,
    ];

    /// The output, and whether the jump is taken.
    type Output = (u64, bool);

    fn eval(&self) -> (u64, bool) {
        let on = |flag: u64| self.flags & flag != 0;
        let (v1, b) = (self.v1, self.v2 ^ self.imm);

        // One adder serves the sum and the difference.
        let sum = if on(Self::SUB) {
            v1.wrapping_sub(b)
        } else {
            v1.wrapping_add(b)
        };

        // The comparisons every selector and branch picks from.
        let (lt, ltu, eq) = ((v1 as i64) < (b as i64), v1 < b, v1 == b);

        // The output: one selector, or the sum when none is set.
        let mut out = if on(Self::SEL_LT) {
            lt as u64
        } else if on(Self::SEL_LTU) {
            ltu as u64
        } else if on(Self::SEL_AND) {
            v1 & b
        } else if on(Self::SEL_OR) {
            v1 | b
        } else if on(Self::SEL_XOR) {
            v1 ^ b
        } else if on(Self::WORD) {
            sext32(sum)
        } else {
            sum
        };

        // A JALR target drops its low bit.
        if on(Self::CLEAR_BIT0) {
            out &= !1;
        }

        // The jump: unconditional, or the one branch condition set.
        let taken = on(Self::ALWAYS)
            || (on(Self::BR_EQ) && eq)
            || (on(Self::BR_NE) && !eq)
            || (on(Self::BR_LT) && lt)
            || (on(Self::BR_GE) && !lt)
            || (on(Self::BR_LTU) && ltu)
            || (on(Self::BR_GEU) && !ltu);
        (out, taken)
    }

    fn input_words(&self) -> Vec<u64> {
        vec![self.v1, self.v2, self.imm, self.flags]
    }

    fn output_words(&(out, taken): &(u64, bool)) -> Vec<u64> {
        vec![out, taken as u64]
    }
}

impl ClassCircuit for Alu {
    /// The ALU: `(v1, v2, imm, flags) -> (out, taken)`.
    ///
    /// It mirrors the reference function on every legal flag word.
    ///
    /// - The second operand is `b = v2 ^ imm`.
    /// - One adder gives `v1 + b`, or `v1 - b` for the comparisons.
    /// - The output is that sum, unless a selector picks a comparison or a bitwise operation.
    /// - The jump is taken always, or when the one branch condition set holds.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 64, 15], &[64, 1]);
        let (v1, v2, imm, f) = (c.input(0), c.input(1), c.input(2), c.input(3));
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

        // A JALR target drops its low bit.
        let keep_bit0 = c.not(flag(Self::CLEAR_BIT0));
        out[0] = c.and(keep_bit0, out[0]);

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

        c.output_word(0, &out);
        c.output(1, 0, taken);
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
            )
                .prop_map(|(flags, v1, v2, equal, immediate)| {
                    let v2 = if equal { v1 } else { v2 };
                    let (v2, imm) = if immediate { (0, v2) } else { (v2, 0) };
                    Self { flags, v1, v2, imm }
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
        let rows: Vec<[u64; 4]> = (0..1u64 << n_log)
            .map(|i| {
                [
                    i.wrapping_mul(0x9e37_79b9_7f4a_7c15),
                    !i,
                    0,
                    Alu::LEGAL[i as usize % Alu::LEGAL.len()],
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

        // Mutation: an output bit, a spare bit of taken's word, the last product.
        for bit in [
            64 * ALU.n_input_words() + 5,
            64 * (ALU.n_input_words() + 1) + 1,
            ALU.useful_bits() - 1,
        ] {
            assert!(!accepts(Some(bit)), "flipping bit {bit} must reject");
        }
    }
}
