//! The extension-field multiplication: products in `E = K[y] / (y^3 + y + 1)`, over the extension registers.
//!
//! `K` is `GF(2)[x] / (x^64 + x^4 + x^3 + x + 1)`, the base field of the proof system.
//!
//! `E = GF(2^192)` is its cubic extension, the field the proof's challenges live in.
//!
//! An extension register holds one element of `E`, three words, its limbs:
//!
//! ```text
//!     c_0 + c_1 y + c_2 y^2
//! ```
//!
//! A word is an element of `K`, bit `i` its coefficient of `x^i`.
//!
//! The class has no circuit. `y^3 + y + 1` has its coefficients in `GF(2)`, so each limb of a product is a sum of
//! products of limbs, in `K`: the table proves the product by identities of degree 2 over `K`
//! (`tables::ClassTable::identities`).

use primitives::field::F192;

/// One extension-field instance: `op fd, fs1, fs2`, on extension registers.
///
/// ```text
///     extmul    c = a * b            extmulk    c = a * b_0
///     extmac    c = c + a * b        extmack    c = c + a * b_0
/// ```
///
/// - The plain forms multiply in `E`.
/// - The `k` forms multiply by a base-field element, the word an integer register holds.
/// - Each has a checked form, which only runs when its result is zero.
///
/// Every operand is read before `c` is written, so `fd` may be `fs1` or `fs2`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Ext {
    /// What the instruction computes: one of the legal words.
    pub flags: u64,
    /// `a`'s limbs.
    pub a: [u64; 3],
    /// `b`'s limbs: a base-field `b` has two zero limbs.
    pub b: [u64; 3],
    /// `c`'s limbs as found.
    pub c: [u64; 3],
}

impl Ext {
    /// Add the product to `c` instead of overwriting it.
    pub const ACCUMULATE: u64 = 1 << 0;
    /// `b` is a base-field element: the word an integer register holds.
    pub const BASE: u64 = 1 << 1;
    /// The result must be zero: any other traps.
    pub const ZERO: u64 = 1 << 2;
    /// Every combination of the three bits.
    pub const LEGAL: &'static [u64] = &[0, 1, 2, 3, 4, 5, 6, 7];

    /// `c`'s limbs after the instruction.
    pub fn eval(&self) -> [u64; 3] {
        debug_assert!(Self::LEGAL.contains(&self.flags));
        let element = |l: [u64; 3]| F192::new(l[0], l[1], l[2]);

        // The product, then the old `c` added on an accumulation.
        let mut c = element(self.a) * element(self.b);
        if self.flags & Self::ACCUMULATE != 0 {
            c += element(self.c);
        }
        [c.c0, c.c1, c.c2]
    }

    /// Whether the instruction runs: a checked form's result is zero.
    pub fn runs(&self) -> bool {
        self.flags & Self::ZERO == 0 || self.eval() == [0; 3]
    }
}

/// A move of one element between memory and an extension register: `eld` or `esd`.
///
/// The element's limbs are the three words at `address ^ 8k`, which are `address + 8k` for an element on a 32-byte
/// boundary; elsewhere the words are permuted, deterministically.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ElementAccess {
    /// The address of the element's first limb.
    pub address: u64,
    /// The limbs moved.
    pub limbs: [u64; 3],
    /// What the destination held: the register for a load, the three words for a store.
    pub old: [u64; 3],
}

impl ElementAccess {
    /// The address of limb `k`.
    pub const fn limb_address(address: u64, k: usize) -> u64 {
        address ^ (8 * k as u64)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::semantics::tests::edge_word;
    use proptest::prelude::*;

    /// The product by its definition: schoolbook in y, each K product shift and add.
    fn schoolbook(a: [u64; 3], b: [u64; 3]) -> [u64; 3] {
        // A product in K: add `a * x^i` for each set bit `i`, reducing each time the degree reaches 64.
        let k = |mut a: u64, b: u64| {
            let mut product = 0;
            for i in 0..64 {
                if b >> i & 1 == 1 {
                    product ^= a;
                }
                a = (a << 1) ^ if a >> 63 == 1 { 0x1B } else { 0 };
            }
            product
        };
        // The five coefficients of y^0 to y^4.
        let mut d = [0u64; 5];
        for i in 0..3 {
            for j in 0..3 {
                d[i + j] ^= k(a[i], b[j]);
            }
        }
        // y^3 = y + 1 and y^4 = y^2 + y.
        [d[0] ^ d[3], d[1] ^ d[3] ^ d[4], d[2] ^ d[4]]
    }

    proptest! {
        #[test]
        fn the_product_is_the_specified_field(
            a in proptest::array::uniform3(edge_word()),
            b in proptest::array::uniform3(edge_word()),
            old in proptest::array::uniform3(edge_word()),
            flags in proptest::sample::select(Ext::LEGAL),
        ) {
            // Invariant: each form is c = a * b (+ c) in K[y] / (y^3 + y + 1), K modulo x^64 + x^4 + x^3 + x + 1,
            // and a checked form runs exactly when that is zero.
            let product = schoolbook(a, b);
            let kept = if flags & Ext::ACCUMULATE != 0 { old } else { [0; 3] };
            let instance = Ext { flags, a, b, c: old };
            let c = instance.eval();
            prop_assert_eq!(c, std::array::from_fn(|i| product[i] ^ kept[i]));
            prop_assert_eq!(instance.runs(), flags & Ext::ZERO == 0 || c == [0; 3]);
        }
    }

    #[test]
    fn the_reductions_are_pinned() {
        // Invariant: y^2 * y = y^3 = y + 1, and x^63 * x = x^64 = x^4 + x^3 + x + 1.
        //
        //     (0, 0, 1) * (0, 1, 0)        ->  (1, 1, 0)
        //     (x^63, 0, 0) * (x, 0, 0)     ->  (0x1B, 0, 0)
        let product = |a: [u64; 3], b: [u64; 3]| {
            Ext {
                flags: 0,
                a,
                b,
                c: [0; 3],
            }
            .eval()
        };
        assert_eq!(product([0, 0, 1], [0, 1, 0]), [1, 1, 0]);
        assert_eq!(product([1 << 63, 0, 0], [2, 0, 0]), [0x1B, 0, 0]);
    }
}
