//! The ALU's four classes: sums and comparisons, bitwise logic, branches, and jumps.
//!
//! Each is a table of its own, so that a row pays only for the circuit its instruction needs.

use super::{InstructionClass, sext32};
use crate::rv::circuits::{ClassCircuit, Word, WordGadgets};
use crate::rv::entry::Class;
use flock::circuit::{Builder, Circuit};

/// One adder instance: add, subtract, and the two comparisons.
///
/// The second operand `b` is `v2 ^ imm`.
///
/// One of the two is always zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Add {
    /// What the adder computes: one of its legal words.
    pub flags: u64,
    /// The first register's value.
    pub v1: u64,
    /// The second register's value.
    pub v2: u64,
    /// The immediate.
    pub imm: u64,
}

impl Add {
    /// Compute `v1 - b` instead of `v1 + b`.
    ///
    /// The comparisons need the difference.
    pub const SUB: u64 = 1 << 0;
    /// Sign-extend the low 32 bits of the sum.
    pub const WORD: u64 = 1 << 1;
    /// Output `v1 < b`, signed.
    pub const SEL_LT: u64 = 1 << 2;
    /// Output `v1 < b`, unsigned.
    pub const SEL_LTU: u64 = 1 << 3;
}

impl InstructionClass for Add {
    const CLASS: Class = Class::Add;

    /// A comparison subtracts, and has no word form.
    const LEGAL: &'static [u64] = &[
        0,
        Self::SUB,
        Self::WORD,
        Self::SUB | Self::WORD,
        Self::SUB | Self::SEL_LT,
        Self::SUB | Self::SEL_LTU,
    ];

    /// The sum, or the comparison's bit.
    type Output = u64;

    fn eval(&self) -> u64 {
        let on = |flag: u64| self.flags & flag != 0;
        let (v1, b) = (self.v1, self.v2 ^ self.imm);
        if on(Self::SEL_LT) {
            ((v1 as i64) < (b as i64)) as u64
        } else if on(Self::SEL_LTU) {
            (v1 < b) as u64
        } else {
            let sum = if on(Self::SUB) {
                v1.wrapping_sub(b)
            } else {
                v1.wrapping_add(b)
            };
            if on(Self::WORD) { sext32(sum) } else { sum }
        }
    }

    fn input_words(&self) -> Vec<u64> {
        vec![self.v1, self.v2, self.imm, self.flags]
    }

    fn output_words(&out: &u64) -> Vec<u64> {
        vec![out]
    }
}

/// One instance of the bitwise logic: AND, OR or XOR of `v1` and `b = v2 ^ imm`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Logic {
    /// The operation: one of its legal words.
    pub flags: u64,
    /// The first register's value.
    pub v1: u64,
    /// The second register's value.
    pub v2: u64,
    /// The immediate.
    pub imm: u64,
}

impl Logic {
    /// Output `v1 & b`.
    pub const AND: u64 = 1 << 0;
    /// Output `v1 | b`.
    pub const OR: u64 = 1 << 1;
    /// Output `v1 ^ b`.
    pub const XOR: u64 = 1 << 2;
}

impl InstructionClass for Logic {
    const CLASS: Class = Class::Logic;

    /// Exactly one operation.
    const LEGAL: &'static [u64] = &[Self::AND, Self::OR, Self::XOR];

    /// The result.
    type Output = u64;

    fn eval(&self) -> u64 {
        let (v1, b) = (self.v1, self.v2 ^ self.imm);
        match self.flags {
            Self::AND => v1 & b,
            Self::OR => v1 | b,
            _ => v1 ^ b,
        }
    }

    fn input_words(&self) -> Vec<u64> {
        vec![self.v1, self.v2, self.imm, self.flags]
    }

    fn output_words(&out: &u64) -> Vec<u64> {
        vec![out]
    }
}

/// One conditional branch: whether `v1` and `v2` meet its condition.
///
/// A branch writes no register and has no immediate: its target is the entry's.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Branch {
    /// The condition: one of its legal words.
    pub flags: u64,
    /// The first register's value.
    pub v1: u64,
    /// The second register's value.
    pub v2: u64,
}

impl Branch {
    /// Branch when `v1 == v2`.
    pub const EQ: u64 = 1 << 0;
    /// Branch when `v1 != v2`.
    pub const NE: u64 = 1 << 1;
    /// Branch when `v1 < v2`, signed.
    pub const LT: u64 = 1 << 2;
    /// Branch when `v1 >= v2`, signed.
    pub const GE: u64 = 1 << 3;
    /// Branch when `v1 < v2`, unsigned.
    pub const LTU: u64 = 1 << 4;
    /// Branch when `v1 >= v2`, unsigned.
    pub const GEU: u64 = 1 << 5;

    /// The flag word of a branch with function `funct3`.
    ///
    /// Returns `None` for functions 2 and 3, which are reserved.
    pub const fn flags_of(funct3: u32) -> Option<u64> {
        match funct3 {
            0 => Some(Self::EQ),
            1 => Some(Self::NE),
            4 => Some(Self::LT),
            5 => Some(Self::GE),
            6 => Some(Self::LTU),
            7 => Some(Self::GEU),
            _ => None,
        }
    }
}

impl InstructionClass for Branch {
    const CLASS: Class = Class::Branch;

    /// Exactly one condition.
    const LEGAL: &'static [u64] = &[Self::EQ, Self::NE, Self::LT, Self::GE, Self::LTU, Self::GEU];

    /// Whether the branch is taken.
    type Output = bool;

    fn eval(&self) -> bool {
        let (v1, v2) = (self.v1, self.v2);
        let (lt, ltu) = ((v1 as i64) < (v2 as i64), v1 < v2);
        match self.flags {
            Self::EQ => v1 == v2,
            Self::NE => v1 != v2,
            Self::LT => lt,
            Self::GE => !lt,
            Self::LTU => ltu,
            _ => !ltu,
        }
    }

    fn input_words(&self) -> Vec<u64> {
        vec![self.v1, self.v2, self.flags]
    }

    fn output_words(&taken: &bool) -> Vec<u64> {
        vec![taken as u64]
    }
}

/// One jump: `JAL` and the exit to a fixed target, `JALR` to `v1 + imm` with bit 0 cleared.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Jump {
    /// Direct or not: one of its legal words.
    pub flags: u64,
    /// The first register's value.
    pub v1: u64,
    /// The immediate.
    pub imm: u64,
}

impl Jump {
    /// Jump to the entry's fixed target, not to the computed one.
    pub const DIRECT: u64 = 1 << 0;
}

impl InstructionClass for Jump {
    const CLASS: Class = Class::Jump;

    /// `JALR`, then `JAL` and the exit.
    const LEGAL: &'static [u64] = &[0, Self::DIRECT];

    /// The computed target, and whether the fixed one is taken.
    type Output = (u64, bool);

    fn eval(&self) -> (u64, bool) {
        (self.v1.wrapping_add(self.imm) & !1, self.flags & Self::DIRECT != 0)
    }

    fn input_words(&self) -> Vec<u64> {
        vec![self.v1, self.imm, self.flags]
    }

    fn output_words(&(out, taken): &(u64, bool)) -> Vec<u64> {
        vec![out, taken as u64]
    }
}

impl ClassCircuit for Add {
    /// The adder: `(v1, v2, imm, flags) -> out`.
    ///
    /// - The second operand is `b = v2 ^ imm`.
    /// - One adder gives `v1 + b`, or `v1 - b` for the comparisons.
    /// - The output is that sum, unless a comparison replaces it by its bit.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 64, 4], &[64]);
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
        let ltu = c.not(carry_out);
        let signs = c.xor(v1[63], b[63]);
        let lt = c.xor(ltu, signs);

        // The sum unless a comparison is selected, whose single bit is the output's bit 0.
        let sum = c.sext32_if(flag(Self::WORD), &sum);
        let compares = c.xor(flag(Self::SEL_LT), flag(Self::SEL_LTU));
        let keeps = c.not(compares);
        let mut out = c.and_word(keeps, &sum);
        let lt_term = c.and(flag(Self::SEL_LT), lt);
        let ltu_term = c.and(flag(Self::SEL_LTU), ltu);
        let compared = c.xor(lt_term, ltu_term);
        out[0] = c.xor(out[0], compared);

        c.output_word(0, &out);
        c.finish()
    }
}

impl ClassCircuit for Logic {
    /// The bitwise logic: `(v1, v2, imm, flags) -> out`, two products per bit.
    ///
    /// With `b = v2 ^ imm` and the selectors `or` and `xor`, bit by bit:
    ///
    /// ```text
    ///     p   = (v1 ^ or) * (b ^ or)          v1 & b, or !(v1 | b) when or
    ///     out = p ^ or ^ xor * (p ^ v1 ^ b)
    /// ```
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 64, 3], &[64]);
        let (v1, v2, imm, f) = (c.input(0), c.input(1), c.input(2), c.input(3));
        let flag = |bit: u64| f[bit.trailing_zeros() as usize];
        let (or, xor) = (flag(Self::OR), flag(Self::XOR));
        let b = c.xor_word(&v2, &imm);
        for i in 0..64 {
            let (x, y) = (c.xor(v1[i], or), c.xor(b[i], or));
            let p = c.and(x, y);
            let diff = c.xor(v1[i], b[i]);
            let flip = c.xor(p, diff);
            let xor_term = c.and(xor, flip);
            let kept = c.xor(p, or);
            let bit = c.xor(kept, xor_term);
            c.output(0, i, bit);
        }
        c.finish()
    }
}

impl ClassCircuit for Branch {
    /// The branch: `(v1, v2, flags) -> taken`.
    ///
    /// - The difference `v1 + !v2 + 1` borrows exactly when it does not carry out, and only its carries are made.
    /// - The jump is taken when the one condition set holds.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 6], &[1]);
        let (v1, v2, f) = (c.input(0), c.input(1), c.input(2));
        let flag = |bit: u64| f[bit.trailing_zeros() as usize];
        let one = c.one();

        // The comparisons, from the borrow and the signs.
        //
        //     ltu = borrow
        //     lt  = borrow ^ sign(v1) ^ sign(v2)
        //     eq  = no bit of v1 ^ v2 set
        let not_v2: Word = v2.iter().map(|&bit| c.not(bit)).collect();
        let (_, carry_out) = c.add_with_carry(&v1, &not_v2, one);
        let ltu = c.not(carry_out);
        let signs = c.xor(v1[63], v2[63]);
        let lt = c.xor(ltu, signs);
        let diff = c.xor_word(&v1, &v2);
        let ne = c.any(&diff);
        let eq = c.not(ne);

        let (ge, geu) = (c.not(lt), c.not(ltu));
        let taken = [
            (Self::EQ, eq),
            (Self::NE, ne),
            (Self::LT, lt),
            (Self::GE, ge),
            (Self::LTU, ltu),
            (Self::GEU, geu),
        ]
        .into_iter()
        .fold(None, |acc, (when, holds)| {
            let term = c.and(flag(when), holds);
            c.xor(acc, term)
        });

        c.output(0, 0, taken);
        c.finish()
    }
}

impl ClassCircuit for Jump {
    /// The jump: `(v1, imm, flags) -> (out, taken)`.
    ///
    /// - The computed target is `v1 + imm`, bit 0 cleared: that bit has no gate, so it is zero.
    /// - The fixed target is taken when the jump is direct.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 1], &[64, 1]);
        let (v1, imm, f) = (c.input(0), c.input(1), c.input(2));
        let target = c.add_wrapping(&v1, &imm);
        for (i, &bit) in target.iter().enumerate().skip(1) {
            c.output(0, i, bit);
        }
        c.output(1, 0, f[Self::DIRECT.trailing_zeros() as usize]);
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

    /// An operand pair as the decoder makes them: one of `v2` and `imm` is zero, and now and
    /// then the second operand equals `v1`, which random words never do.
    fn operands() -> impl Strategy<Value = (u64, u64, u64)> {
        (edge_word(), edge_word(), any::<bool>(), any::<bool>()).prop_map(|(v1, v2, equal, immediate)| {
            let v2 = if equal { v1 } else { v2 };
            let (v2, imm) = if immediate { (0, v2) } else { (v2, 0) };
            (v1, v2, imm)
        })
    }

    impl Arbitrary for Add {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            (select(Self::LEGAL), operands())
                .prop_map(|(flags, (v1, v2, imm))| Self { flags, v1, v2, imm })
                .boxed()
        }
    }

    impl Arbitrary for Logic {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            (select(Self::LEGAL), operands())
                .prop_map(|(flags, (v1, v2, imm))| Self { flags, v1, v2, imm })
                .boxed()
        }
    }

    impl Arbitrary for Branch {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            (select(Self::LEGAL), operands())
                .prop_map(|(flags, (v1, v2, imm))| Self {
                    flags,
                    v1,
                    v2: v2 ^ imm,
                })
                .boxed()
        }
    }

    impl Arbitrary for Jump {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            (select(Self::LEGAL), edge_word(), edge_word())
                .prop_map(|(flags, v1, imm)| Self { flags, v1, imm })
                .boxed()
        }
    }

    static BRANCH: LazyLock<Circuit> = LazyLock::new(Branch::circuit);

    #[test]
    fn the_alu_classes_circuits_match_their_references() {
        // Legal flags and edge-biased operands pin each gate list to its reference function.
        circuit_matches_reference::<Add>(4096);
        circuit_matches_reference::<Logic>(4096);
        circuit_matches_reference::<Branch>(4096);
        circuit_matches_reference::<Jump>(4096);
    }

    #[test]
    fn flock_proves_honest_branch_instances_and_refuses_a_flipped_bit() {
        // Fixture: 16 instances cycling through the legal words.
        const LABEL: &[u8] = b"rv-branch-reduction-test";
        let block = BRANCH.block();
        let n_log = 4;
        let rows: Vec<[u64; 3]> = (0..1u64 << n_log)
            .map(|i| {
                [
                    i.wrapping_mul(0x9e37_79b9_7f4a_7c15),
                    !i,
                    Branch::LEGAL[i as usize % Branch::LEGAL.len()],
                ]
            })
            .collect();

        // Prove the batch, optionally flipping one witness bit first, and verify.
        let accepts = |tamper: Option<usize>| {
            let (mut z, a, b, mut z_lincheck) = BRANCH.generate_witness(&rows, n_log);
            if let Some(bit) = tamper {
                z[bit / 64] ^= 1 << (bit % 64);
                z_lincheck[bit] ^= 1;
            }
            let mut ps = ProverState::from_label(LABEL);
            let stage = block.prove_zerocheck(n_log, &z, &a, &b, None, &mut ps);
            let claim = block.prove_lincheck(n_log, stage, &z_lincheck, None, &mut ps);
            let proof = ps.into_proof();
            let mut vs = VerifierState::from_label(LABEL, &proof);
            block.verify(n_log, &mut vs).is_ok_and(|r| r.claim == claim) && vs.finish().is_ok()
        };
        assert!(accepts(None));

        // Mutation: taken, a spare bit of taken's word, the last product.
        for bit in [
            64 * BRANCH.n_input_words(),
            64 * BRANCH.n_input_words() + 1,
            BRANCH.useful_bits() - 1,
        ] {
            assert!(!accepts(Some(bit)), "flipping bit {bit} must reject");
        }
    }
}
