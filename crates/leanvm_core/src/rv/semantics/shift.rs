//! The shifter: logical and arithmetic shifts, on 64 or 32 bits.

use super::{InstructionClass, sext32};
use crate::rv::entry::Class;

/// One shifter instance.
///
/// The amount is the low 6 bits of `v2 ^ imm`, or 5 bits for a word shift.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Shift {
    /// What the shifter computes: one of its legal words.
    pub flags: u64,
    /// The value to shift.
    pub v1: u64,
    /// The second register's value.
    pub v2: u64,
    /// The immediate.
    pub imm: u64,
}

impl Shift {
    /// Shift right instead of left.
    pub const RIGHT: u64 = 1 << 0;
    /// Fill a right shift with the sign bit.
    pub const ARITH: u64 = 1 << 1;
    /// Shift the low 32 bits, then sign-extend the low 32 bits of the result.
    pub const WORD: u64 = 1 << 2;
}

impl InstructionClass for Shift {
    const CLASS: Class = Class::Shift;

    /// An arithmetic shift is always a right shift.
    const LEGAL: &'static [u64] = &[
        0,
        Self::RIGHT,
        Self::RIGHT | Self::ARITH,
        Self::WORD,
        Self::WORD | Self::RIGHT,
        Self::WORD | Self::RIGHT | Self::ARITH,
    ];

    /// The shifted value.
    type Output = u64;

    fn eval(&self) -> u64 {
        let on = |flag: u64| self.flags & flag != 0;
        let (right, arith, word) = (on(Self::RIGHT), on(Self::ARITH), on(Self::WORD));
        let amount = (self.v2 ^ self.imm) & if word { 31 } else { 63 };

        // A word shift starts from the low 32 bits, extended as the shift fills.
        let x = match (word, arith) {
            (false, _) => self.v1,
            (true, true) => sext32(self.v1),
            (true, false) => self.v1 as u32 as u64,
        };

        // Shift, then sign-extend a word result.
        let out = match (right, arith) {
            (false, _) => x << amount,
            (true, false) => x >> amount,
            (true, true) => ((x as i64) >> amount) as u64,
        };
        if word { sext32(out) } else { out }
    }

    fn input_words(&self) -> Vec<u64> {
        vec![self.v1, self.v2, self.imm, self.flags]
    }

    fn output_words(&out: &u64) -> Vec<u64> {
        vec![out]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::semantics::tests::edge_word;
    use proptest::prelude::*;
    use proptest::sample::select;
    use proptest::strategy::BoxedStrategy;

    /// Any shifter instance, as the decoder makes them: a register amount or a six-bit immediate.
    impl Arbitrary for Shift {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            // Every amount now and then, which a random word's low bits reach slowly.
            (
                select(Self::LEGAL),
                edge_word(),
                edge_word(),
                0u64..64,
                any::<bool>(),
                any::<bool>(),
            )
                .prop_map(|(flags, v1, v2, amount, small, immediate)| {
                    let v2 = if small { amount } else { v2 };
                    let (v2, imm) = if immediate { (0, v2 & 63) } else { (v2, 0) };
                    Self { flags, v1, v2, imm }
                })
                .boxed()
        }
    }
}
