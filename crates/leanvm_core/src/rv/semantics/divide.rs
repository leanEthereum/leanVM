//! The division: quotients and remainders, and the hints its circuit checks.

use super::{InstructionClass, sext32};
use crate::rv::entry::Class;

/// One division instance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Div {
    /// Signed or not, quotient or remainder, word or not: one of the legal words.
    pub flags: u64,
    /// The dividend.
    pub v1: u64,
    /// The divisor.
    pub v2: u64,
}

impl Div {
    /// Divide signed operands.
    pub const SIGNED: u64 = 1 << 0;
    /// Output the remainder instead of the quotient.
    pub const REM: u64 = 1 << 1;
    /// Divide the low 32 bits, then sign-extend the low 32 bits of the result.
    pub const WORD: u64 = 1 << 2;

    /// The magnitudes of the quotient and the remainder.
    ///
    /// The prover supplies them to the division circuit, which checks them rather than computes them.
    ///
    /// Both are zero for a zero divisor, which the circuit ignores.
    pub fn hints(&self) -> (u64, u64) {
        let (signed, word) = (self.flags & Self::SIGNED != 0, self.flags & Self::WORD != 0);

        // The operands' magnitudes, on 32 bits for a word division.
        let magnitude = |v: u64| match (word, signed) {
            (false, false) => v,
            (false, true) => (v as i64).unsigned_abs(),
            (true, false) => v as u32 as u64,
            (true, true) => (v as i32 as i64).unsigned_abs(),
        };
        let (n, d) = (magnitude(self.v1), magnitude(self.v2));
        n.checked_div(d).map_or((0, 0), |q| (q, n % d))
    }
}

impl InstructionClass for Div {
    const CLASS: Class = Class::Div;

    /// Every combination.
    const LEGAL: &'static [u64] = &[0, 1, 2, 3, 4, 5, 6, 7];

    /// The quotient or the remainder.
    type Output = u64;

    /// The quotient or the remainder, as RISC-V defines them.
    ///
    /// - Dividing by zero gives all ones, and its remainder is the dividend.
    /// - The one signed overflow, `-2^63 / -1`, wraps to `-2^63` with remainder zero.
    /// - A word division extends the low 32 bits of both operands, divides, and sign-extends the result.
    fn eval(&self) -> u64 {
        let on = |flag: u64| self.flags & flag != 0;
        let (signed, rem, word) = (on(Self::SIGNED), on(Self::REM), on(Self::WORD));

        // A word division's operands, extended to 64 bits.
        let extend = |v: u64| match (word, signed) {
            (false, _) => v,
            (true, true) => sext32(v),
            (true, false) => v as u32 as u64,
        };
        let (n, d) = (extend(self.v1), extend(self.v2));

        // The quotient and the remainder, the zero divisor and the overflow included.
        let (q, r) = if d == 0 {
            (u64::MAX, n)
        } else if signed {
            let (n, d) = (n as i64, d as i64);
            (n.wrapping_div(d) as u64, n.wrapping_rem(d) as u64)
        } else {
            (n / d, n % d)
        };
        let out = if rem { r } else { q };
        if word { sext32(out) } else { out }
    }

    /// The operands, the flags, then the honest hints.
    fn input_words(&self) -> Vec<u64> {
        let (q, r) = self.hints();
        vec![self.v1, self.v2, self.flags, q, r]
    }

    /// The result, then the circuit's verdict on the hints, which honest hints keep at zero.
    fn output_words(&out: &u64) -> Vec<u64> {
        vec![out, 0]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::semantics::tests::edge_word;
    use proptest::prelude::*;
    use proptest::sample::select;
    use proptest::strategy::BoxedStrategy;

    /// Any division instance, its divisor biased toward zero and toward small values.
    impl Arbitrary for Div {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            let divisor = prop_oneof![1 => Just(0), 4 => (edge_word(), 0u32..64).prop_map(|(w, s)| w >> s)];
            (select(Self::LEGAL), edge_word(), divisor)
                .prop_map(|(flags, v1, v2)| Self { flags, v1, v2 })
                .boxed()
        }
    }

    proptest! {
        #[test]
        fn div_hints_satisfy_the_division_identity(div in any::<Div>()) {
            // Invariant: |n| = q * |d| + r with r < |d|, over the integers.
            let (q, r) = div.hints();
            let word = div.flags & Div::WORD != 0;
            let signed = div.flags & Div::SIGNED != 0;
            let magnitude = |v: u64| match (word, signed) {
                (false, false) => v as u128,
                (false, true) => (v as i64).unsigned_abs() as u128,
                (true, false) => v as u32 as u128,
                (true, true) => (v as i32 as i64).unsigned_abs() as u128,
            };
            let (n, d) = (magnitude(div.v1), magnitude(div.v2));
            if d == 0 {
                prop_assert_eq!((q, r), (0, 0));
            } else {
                prop_assert_eq!(q as u128 * d + r as u128, n);
                prop_assert!((r as u128) < d);
            }
        }
    }

    #[test]
    fn division_edge_cases_follow_the_specification() {
        let (min, min32) = (i64::MIN as u64, i32::MIN as i64 as u64);
        let div = |flags, v1, v2| Div { flags, v1, v2 }.eval();

        // A zero divisor: all ones, and the remainder is the dividend.
        assert_eq!(div(0, 7, 0), u64::MAX);
        assert_eq!(div(Div::REM, 7, 0), 7);

        // The signed overflow: -2^63 / -1 wraps, remainder zero.
        assert_eq!(div(Div::SIGNED, min, u64::MAX), min);
        assert_eq!(div(Div::SIGNED | Div::REM, min, u64::MAX), 0);

        // The same on 32 bits: -2^31 / -1 wraps to -2^31, sign-extended.
        assert_eq!(div(Div::SIGNED | Div::WORD, min32, u64::MAX), min32);
    }
}
