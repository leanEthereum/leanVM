//! u64 arithmetic in the gate-list vocabulary: wrapping addition, and multiplication wrapping or widening.
//!
//! The gadgets take wires and return wires, so they compose into larger circuits.
//! Their witness is word arithmetic on the structure the gate list is built from, not the generic walk.

#[cfg(any(test, feature = "bench"))]
pub(crate) mod add;
pub mod mul;
#[cfg(any(test, feature = "bench"))]
mod u64_circuit;

#[cfg(any(test, feature = "bench"))]
pub use u64_circuit::{U64Circuit, U64Op};

/// One instance's words of `z`, `A·z` and `B·z`.
struct Instance<'a> {
    z: &'a mut [u64],
    az: &'a mut [u64],
    bz: &'a mut [u64],
}

impl Instance<'_> {
    /// Product rows from `slot`, one per position of `mask`, with `A·z = left`,
    /// `B·z = right` and `z = left·right`.
    fn products(&mut self, slot: usize, mask: u128, left: u128, right: u128) {
        if mask != 0 {
            let shift = mask.trailing_zeros();
            or_bits(self.z, slot, (left & right & mask) >> shift);
            or_bits(self.az, slot, (left & mask) >> shift);
            or_bits(self.bz, slot, (right & mask) >> shift);
        }
    }
}

/// OR `v` into `buf` from bit `at`.
#[inline(always)]
fn or_bits(buf: &mut [u64], at: usize, v: u128) {
    let s = at % 64;
    let words = [
        (v << s) as u64,
        ((v >> 1) >> (63 - s)) as u64,
        ((v >> 1) >> (127 - s)) as u64,
    ];
    for (w, x) in buf[at / 64..].iter_mut().zip(words) {
        *w |= x;
    }
}
