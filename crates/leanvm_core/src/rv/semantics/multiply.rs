//! The multiplications: the low and the high word of a product.

use super::{InstructionClass, sext32};
use crate::rv::circuits::{ClassCircuit, Word, WordGadgets};
use crate::rv::entry::Class;
use flock::arith::mul::Multiplier;
use flock::circuit::{Builder, Circuit};

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
    const CLASS: Class = Class::Mul;

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

    fn input_words(&self) -> Vec<u64> {
        vec![self.v1, self.v2, self.flags]
    }

    fn output_words(&out: &u64) -> Vec<u64> {
        vec![out]
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
    const CLASS: Class = Class::Mulh;

    /// `mulh`, `mulhsu`, `mulhu`.
    const LEGAL: &'static [u64] = &[Self::SIGNED_1 | Self::SIGNED_2, Self::SIGNED_1, 0];

    /// The high word of the 128-bit product.
    type Output = u64;

    fn eval(&self) -> u64 {
        let widen = |v: u64, signed: bool| if signed { v as i64 as i128 } else { v as i128 };
        let (s1, s2) = (self.flags & Self::SIGNED_1 != 0, self.flags & Self::SIGNED_2 != 0);
        (widen(self.v1, s1).wrapping_mul(widen(self.v2, s2)) >> 64) as u64
    }

    fn input_words(&self) -> Vec<u64> {
        vec![self.v1, self.v2, self.flags]
    }

    fn output_words(&out: &u64) -> Vec<u64> {
        vec![out]
    }
}

impl ClassCircuit for Mul {
    /// The low word of the product: `(v1, v2, flags) -> out`.
    ///
    /// A word multiplication sign-extends the low 32 bits.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 1], &[64]);
        let (v1, v2, f) = (c.input(0), c.input(1), c.input(2));
        let (product, _) = Multiplier::build(&mut c, &v1, &v2, 64);
        let out = c.sext32_if(f[0], &product);
        c.output_word(0, &out);
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
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 2], &[64]);
        let (v1, v2, f) = (c.input(0), c.input(1), c.input(2));
        let (product, _) = Multiplier::build(&mut c, &v1, &v2, 128);
        let mut high = product[64..].to_vec();

        // Subtract the other operand for each signed negative one.
        for (signed, operand, other) in [(f[0], &v1, &v2), (f[1], &v2, &v1)] {
            let negative = c.and(signed, operand[63]);

            // high - other is high + !other + 1, all of it gated by negative.
            let subtrahend: Word = other
                .iter()
                .map(|&bit| {
                    let inverted = c.not(bit);
                    c.and(negative, inverted)
                })
                .collect();
            (high, _) = c.add_with_carry(&high, &subtrahend, negative);
        }

        c.output_word(0, &high);
        c.finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::semantics::tests::{circuit_matches_reference, edge_word};
    use proptest::prelude::*;
    use proptest::sample::select;
    use proptest::strategy::BoxedStrategy;

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
}
