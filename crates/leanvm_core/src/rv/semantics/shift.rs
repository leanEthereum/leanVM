//! The shifter: logical and arithmetic shifts, on 64 or 32 bits.

use super::{InstructionClass, sext32};
use crate::rv::circuits::{ClassCircuit, Word, WordGadgets};
use flock::circuit::{Builder, Circuit};

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
}

impl ClassCircuit for Shift {
    /// The shifter: `(v1, v2, imm, flags) -> out`.
    ///
    /// One right shifter serves both directions.
    ///
    /// A left shift is a right shift of the bit-reversed word, reversed back.
    ///
    /// The right shift is six barrel stages, by 1, 2, 4, 8, 16 and 32 bits.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 64, 3], &[64]);
        let (v1, v2, imm, f) = (c.input(0), c.input(1), c.input(2), c.input(3));
        let flag = |bit: u64| f[bit.trailing_zeros() as usize];
        let (right, arith, word) = (flag(Self::RIGHT), flag(Self::ARITH), flag(Self::WORD));

        // The amount: six bits, or five for a word shift.
        let mut amount: Word = (0..6).map(|i| c.xor(v2[i], imm[i])).collect();
        let not_word = c.not(word);
        amount[5] = c.and(not_word, amount[5]);

        // A word shift takes the low 32 bits, extended by the sign if arithmetic, by zero if not.
        let low_sign = c.and(arith, v1[31]);
        let x: Word = (0..64)
            .map(|i| if i < 32 { v1[i] } else { c.mux(word, low_sign, v1[i]) })
            .collect();

        // What a right shift brings in from the top; arithmetic implies right.
        let fill = c.and(arith, x[63]);

        // Reverse, shift right stage by stage, reverse back.
        let mut y = c.reverse_unless(right, &x);
        for (stage, &bit) in amount.iter().enumerate() {
            let by = 1 << stage;
            y = (0..64)
                .map(|i| c.mux(bit, if i + by < 64 { y[i + by] } else { fill }, y[i]))
                .collect();
        }
        let y = c.reverse_unless(right, &y);

        let out = c.sext32_if(word, &y);
        c.output_word(0, &out);
        c.finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::Class;
    use crate::rv::semantics::tests::{Ports, circuit_matches_reference, edge_word};
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

    #[test]
    fn shift_circuit_matches_the_reference() {
        // Legal flags and edge-biased operands pin the gate list to the reference function.
        circuit_matches_reference::<Shift>(4096);
    }

    impl Ports for Shift {
        const CLASS: Class = Class::Shift;

        fn input_words(&self) -> Vec<u64> {
            vec![self.v1, self.v2, self.imm, self.flags]
        }

        fn output_words(&self, &out: &u64) -> Vec<u64> {
            vec![out]
        }
    }
}
