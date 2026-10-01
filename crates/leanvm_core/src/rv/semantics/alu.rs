//! The ALU: sums, differences, comparisons, bitwise logic, branches and jumps.

use super::{InstructionClass, sext32};
use crate::rv::entry::Class;

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
    pub fn branch_flags(funct3: u32) -> Option<u64> {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::semantics::tests::edge_word;
    use proptest::prelude::*;
    use proptest::sample::select;
    use proptest::strategy::BoxedStrategy;

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
}
