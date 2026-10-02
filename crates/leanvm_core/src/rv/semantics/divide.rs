//! The division: quotients and remainders, and the hints its circuit checks.

use super::{InstructionClass, sext32};
use crate::rv::circuits::{ClassCircuit, Word, WordGadgets};
use crate::rv::entry::Class;
use flock::arith::mul::Multiplier;
use flock::circuit::{Builder, Circuit, Wire};

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

impl ClassCircuit for Div {
    /// The division: `(v1, v2, flags, q, r) -> (out, bad)`.
    ///
    /// The prover supplies `q` and `r`, the magnitudes of the quotient and the remainder.
    ///
    /// The circuit sets `bad` unless they are the right ones:
    ///
    /// ```text
    ///     |n| = q * |d| + r
    ///     r   < |d|
    /// ```
    ///
    /// The identity holds over the integers: the product has no high word, and the sum no carry.
    ///
    /// A row puts `bad` where its bytecode entry holds zero, so the proof forces it to zero.
    ///
    /// A zero divisor checks nothing, and gives what RISC-V says: all ones, or the dividend.
    ///
    /// The one overflow, `-2^63 / -1`, needs no special case on magnitudes.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 3, 64, 64], &[64, 1]);
        let (v1, v2, f, q, r) = (c.input(0), c.input(1), c.input(2), c.input(3), c.input(4));
        let (signed, rem, word) = (f[0], f[1], f[2]);

        // A word division divides the low 32 bits, extended as the division is signed or not.
        let mut extend = |x: &[Wire]| -> Word {
            let sign = c.and(signed, x[31]);
            (0..64)
                .map(|i| if i < 32 { x[i] } else { c.mux(word, sign, x[i]) })
                .collect()
        };
        let (n, d) = (extend(&v1), extend(&v2));

        // The operands' magnitudes.
        let (n_negative, d_negative) = (c.and(signed, n[63]), c.and(signed, d[63]));
        let (n_abs, d_abs) = (c.negate_if(n_negative, &n), c.negate_if(d_negative, &d));

        // Check |n| = q * |d| + r: the product fits 64 bits, the sum does not carry, and it equals |n|.
        let (product, _) = Multiplier::build(&mut c, &q, &d_abs, 128);
        let overflows = c.any(&product[64..]);
        let (sum, carries) = c.add_with_carry(&product[..64], &r, None);
        let difference = c.xor_word(&sum, &n_abs);
        let differs = c.any(&difference);

        // Check r < |d|: r - |d| = r + !|d| + 1 carries out exactly when r >= |d|.
        let d_inverted: Word = d_abs.iter().map(|&bit| c.not(bit)).collect();
        let one = c.one();
        let (_, too_large) = c.add_with_carry(&r, &d_inverted, one);

        // Any failed check is bad, unless the divisor is zero.
        let d_nonzero = c.any(&d);
        let wrong = [carries, differs, too_large]
            .into_iter()
            .fold(overflows, |acc, w| c.or(acc, w));
        let bad = c.and(d_nonzero, wrong);

        // The quotient is negative when the operands' signs differ.
        // The remainder is negative when the dividend is.
        let q_negative = c.xor(n_negative, d_negative);
        let (q_signed, r_signed) = (c.negate_if(q_negative, &q), c.negate_if(n_negative, &r));

        // The output: the quotient or the remainder, or the zero divisor's result.
        let out: Word = (0..64)
            .map(|i| {
                let result = c.mux(rem, r_signed[i], q_signed[i]);
                let by_zero = c.mux(rem, n[i], one);
                c.mux(d_nonzero, result, by_zero)
            })
            .collect();
        let out = c.sext32_if(word, &out);

        c.output_word(0, &out);
        c.output(1, 0, bad);
        c.finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::semantics::tests::{circuit_matches_reference, edge_word, run};
    use proptest::prelude::*;
    use proptest::sample::select;
    use proptest::strategy::BoxedStrategy;
    use std::sync::LazyLock;

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

    static DIV: LazyLock<Circuit> = LazyLock::new(Div::circuit);

    #[test]
    fn div_circuit_matches_the_reference() {
        // Legal flags and edge-biased operands pin the gate list to the reference function.
        circuit_matches_reference::<Div>(512);
    }

    #[test]
    fn division_edge_cases_match_the_reference() {
        // The signed overflow -2^63 / -1, and a zero divisor for the quotient and the remainder.
        let min = i64::MIN as u64;
        for div in [
            Div {
                flags: Div::SIGNED,
                v1: min,
                v2: u64::MAX,
            },
            Div { flags: 0, v1: 7, v2: 0 },
            Div {
                flags: Div::REM,
                v1: 7,
                v2: 0,
            },
        ] {
            assert_eq!(
                run(&DIV, &div.input_words(), 2),
                Div::output_words(&div.eval()),
                "{div:?}"
            );
        }
    }

    #[test]
    fn a_hint_correct_modulo_2_64_is_refused() {
        // 1 / 3 with q = (2^64 + 1) / 3: q * 3 = 2^64 + 1, which is 1 modulo 2^64.
        assert_eq!(run(&DIV, &[1, 3, 0, 0x5555_5555_5555_5555, 2], 2)[1], 1);
    }

    proptest! {
        #[test]
        fn div_refuses_any_other_hint(div in any::<Div>(), dq in any::<u64>(), dr in any::<u64>()) {
            // Mutation: shift the honest hints by a nonzero amount.
            prop_assume!((dq, dr) != (0, 0));
            let mut inputs = div.input_words();
            inputs[3] = inputs[3].wrapping_add(dq);
            inputs[4] = inputs[4].wrapping_add(dr);
            let got = run(&DIV, &inputs, 2);

            // A nonzero divisor refuses them; a zero divisor ignores them.
            let by_zero = if div.flags & Div::WORD != 0 { div.v2 as u32 == 0 } else { div.v2 == 0 };
            if by_zero {
                prop_assert_eq!(got, Div::output_words(&div.eval()));
            } else {
                prop_assert_eq!(got[1], 1);
            }
        }
    }
}
