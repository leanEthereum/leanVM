//! Wrapping addition, as a ripple-carry adder.
//!
//! The carry into position `i + 1` is the majority of `a_i`, `b_i` and the carry `c_i`:
//!
//! ```text
//!     maj(a_i, b_i, c_i) = (a_i + c_i)(b_i + c_i) + c_i        one product
//! ```
//!
//! Every other wire is affine, so the circuit pays 63 products: the carry out of bit 63 falls off the modulus.
//! The witness is the native sum, whose carries are `(a + b) ^ a ^ b`.

use super::InstanceTables;
use crate::circuit::{Builder, Wire};

/// The carries into bits 1 to 63.
const CARRIES: u128 = (u64::MAX >> 1) as u128;

/// A built adder: where its carries' products sit.
pub(crate) struct Adder {
    /// The first of the carries' 63 product slots.
    slot: usize,
}

impl Adder {
    /// `a + b mod 2^64`, as wires.
    pub(crate) fn build(c: &mut Builder, a: &[Wire], b: &[Wire]) -> (Vec<Wire>, Self) {
        let slot = c.next_slot();
        let mut carry = None;
        let mut sum = Vec::with_capacity(64);
        for i in 0..64 {
            // The sum bit is free; the next carry costs one product.
            let ac = c.xor(a[i], carry);
            let bc = c.xor(b[i], carry);
            sum.push(c.xor(ac, b[i]));
            if i < 63 {
                let maj = c.and(ac, bc);
                carry = c.xor(maj, carry);
            }
        }
        (sum, Self { slot })
    }

    /// Write the carries' rows and return the sum.
    pub(super) fn witness(&self, a: u64, b: u64, tables: &mut InstanceTables<'_>) -> u128 {
        let sum = a.wrapping_add(b);
        // Bit `i` of `sum ^ a ^ b` is the carry into position `i`.
        let carry_in = sum ^ a ^ b;
        tables.products(self.slot, CARRIES, u128::from(a ^ carry_in), u128::from(b ^ carry_in));
        u128::from(sum)
    }
}
