//! u64 arithmetic in the gate-list language: wrapping addition, and multiplication wrapping or widening.
//!
//! A gadget takes wires and returns wires, so gadgets compose into larger circuits.
//! Its witness is word arithmetic on the structure its gate list is built from, never the generic walk.

#[cfg(any(test, feature = "bench"))]
pub(crate) mod add;
pub mod mul;
#[cfg(any(test, feature = "bench"))]
mod u64_circuit;

#[cfg(any(test, feature = "bench"))]
pub use u64_circuit::{U64Circuit, U64Op};

/// One instance's words of `z`, `A z` and `B z`, which a gadget's witness ORs its rows into.
struct InstanceTables<'a> {
    z: &'a mut [u64],
    az: &'a mut [u64],
    bz: &'a mut [u64],
}

impl InstanceTables<'_> {
    /// Product rows from `slot`, one per set position of `mask`, packed down to consecutive slots.
    ///
    /// ```text
    ///     A z = left    B z = right    z = left * right        at each position of mask
    /// ```
    fn products(&mut self, slot: usize, mask: u128, left: u128, right: u128) {
        if mask != 0 {
            // The mask is one run of positions, so a shift packs it into consecutive slots.
            let shift = mask.trailing_zeros();
            Self::or_bits(self.z, slot, (left & right & mask) >> shift);
            Self::or_bits(self.az, slot, (left & mask) >> shift);
            Self::or_bits(self.bz, slot, (right & mask) >> shift);
        }
    }

    /// `width` rows from `slot` against the constant.
    ///
    /// ```text
    ///     A z = z = v      B z = 1
    /// ```
    #[cfg(any(test, feature = "bench"))]
    fn unit_rows(&mut self, slot: usize, v: u128, width: usize) {
        Self::or_bits(self.z, slot, v);
        Self::or_bits(self.az, slot, v);
        Self::or_bits(self.bz, slot, u128::MAX >> (128 - width));
    }

    /// OR the 128 bits of `v` into `table` from bit `at` on.
    #[inline(always)]
    fn or_bits(table: &mut [u64], at: usize, v: u128) {
        let s = at % 64;
        // `v` spans at most three words from `at`; the split shifts never shift by 64.
        let words = [
            (v << s) as u64,
            ((v >> 1) >> (63 - s)) as u64,
            ((v >> 1) >> (127 - s)) as u64,
        ];
        for (w, x) in table[at / 64..].iter_mut().zip(words) {
            *w |= x;
        }
    }
}
