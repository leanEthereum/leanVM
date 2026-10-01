//! The multiplications: the low and the high word of a product.

use super::{InstructionClass, sext32};
use crate::rv::entry::Class;

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::semantics::tests::edge_word;
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
}
