//! The extension-field multiplication: products in `E = K[y] / (y^3 + y + 1)`, over memory.
//!
//! `K` is `GF(2)[x] / (x^64 + x^4 + x^3 + x + 1)`, the base field of the proof system.
//!
//! `E = GF(2^192)` is its cubic extension, the field the proof's challenges live in.
//!
//! An element of `E` is three words in memory, its limbs:
//!
//! ```text
//!     c_0 + c_1 y + c_2 y^2      at the byte addresses  p, p + 8, p + 16
//! ```
//!
//! A word is an element of `K`, bit `i` its coefficient of `x^i`.
//!
//! The class has no circuit. `y^3 + y + 1` has its coefficients in `GF(2)`, so each limb of a product is a sum of
//! products of limbs, in `K`: the table proves the product by three identities of degree 2 over `K`
//! (`tables::ClassTable::identities`), and its operand circuit computes the limbs' addresses.

use crate::rv::circuits::Products;
use flock::circuit::{Builder, Circuit, Wire};
use primitives::field::F192;

/// One extension-field instance: `extmul`, `extmac`, `extmulk` or `extmack`, on `rd, rs1, rs2`.
///
/// The three registers hold addresses: `a` at `rs1`, `b` at `rs2`, and `c` at `rd`.
///
/// ```text
///     extmul    c = a * b            extmulk    c = a * b_0
///     extmac    c = c + a * b        extmack    c = c + a * b_0
/// ```
///
/// - The plain forms multiply in `E`.
/// - The `k` forms multiply by a base-field element, the one word at `rs2`.
///
/// Every operand is read before `c` is written, so `c` may be `a` or `b`.
///
/// No register is written: `rd` names where the result goes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Ext {
    /// What the instruction computes: one of the legal words.
    pub flags: u64,
    /// The addresses of `a`, `b` and `c`: the values of `rs1`, `rs2` and `rd`.
    pub pointers: [u64; 3],
    /// The nine limbs as found: `a`'s, `b`'s, then `c`'s.
    ///
    /// A base-field `b`'s two high limbs are zero, and no access.
    pub limbs: [u64; Self::LIMBS],
}

/// Where one of an instance's limbs is read.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Limb {
    /// The memory word at this byte address.
    Memory(u64),
    /// No cell: a high limb of a base-field `b`, which is zero.
    Zero,
}

impl Ext {
    /// Add the product to `c` instead of overwriting it.
    pub const ACCUMULATE: u64 = 1 << 0;
    /// `b` is a base-field element: one word, its high limbs zero.
    pub const BASE: u64 = 1 << 1;
    /// Overwrite or accumulate, by an extension or a base-field element.
    pub const LEGAL: &'static [u64] = &[0, Self::ACCUMULATE, Self::BASE, Self::BASE | Self::ACCUMULATE];
    /// The limbs the row accesses: three for each of `a`, `b` and `c`.
    pub const LIMBS: usize = 9;
    /// The limbs whose bus address the operand circuit computes: every limb but the three pointers.
    pub const OFFSET_LIMBS: [usize; 6] = [1, 2, 4, 5, 7, 8];

    /// Where limb `k` of an instance with these pointers and flags is read.
    ///
    /// ```text
    ///     k:        0    1     2      3    4     5      6    7     8
    ///     limb:     a_0  a_1   a_2    b_0  b_1   b_2    c_0  c_1   c_2
    ///     address:  pa   pa+8  pa+16  pb   pb+8  pb+16  pc   pc+8  pc+16
    /// ```
    ///
    /// A base-field `b`'s `b_1` and `b_2` are no access.
    ///
    /// The addresses wrap modulo `2^64`, as RISC-V addresses do.
    pub const fn limb(pointers: [u64; 3], flags: u64, k: usize) -> Limb {
        let (operand, limb) = (k / 3, k % 3);
        if operand == 1 && limb > 0 && flags & Self::BASE != 0 {
            Limb::Zero
        } else {
            Limb::Memory(pointers[operand].wrapping_add(8 * limb as u64))
        }
    }

    /// The bus address of limb `k`: zero for a limb that is no access.
    pub const fn bus_address(pointers: [u64; 3], flags: u64, k: usize) -> u64 {
        match Self::limb(pointers, flags, k) {
            Limb::Zero => 0,
            Limb::Memory(address) => address,
        }
    }

    /// `c`'s limbs after the instruction.
    pub fn eval(&self) -> [u64; 3] {
        debug_assert!(Self::LEGAL.contains(&self.flags));
        let l = &self.limbs;
        let element = |i: usize| F192::new(l[3 * i], l[3 * i + 1], l[3 * i + 2]);

        // The product, then the old `c` added on an accumulation.
        let mut c = element(0) * element(1);
        if self.flags & Self::ACCUMULATE != 0 {
            c += element(2);
        }
        [c.c0, c.c1, c.c2]
    }

    /// The table's operand circuit: the flags' two bits, and the bus addresses of the limbs that are no pointer.
    ///
    /// ```text
    ///     inputs    v1, v2, vd, flags
    ///     outputs   accumulate, base, then the addresses of limbs 1, 2, 4, 5, 7 and 8
    /// ```
    ///
    /// - `accumulate` and `base` each fill a port, so each is a 0 or 1 field element.
    /// - The addresses are `p + 8` and `p + 16` for each pointer, `b`'s gated to zero for a base-field `b`.
    /// - A pointer off its word leaves its low bits in every limb's address, which then names no cell.
    pub fn operand_circuit() -> Circuit {
        let outputs = [1, 1]
            .into_iter()
            .chain([64; Self::OFFSET_LIMBS.len()])
            .collect::<Vec<_>>();
        let mut c = Builder::new(&[64, 64, 64, 2], &outputs);
        let [a, b, d] = [0, 1, 2].map(|i| c.input::<64>(i));
        let flags = c.input::<2>(3);
        let (accumulate, base) = (flags[0], flags[1]);
        c.output(0, 0, accumulate);
        c.output(1, 0, base);
        let not_base = c.not(base);
        for (i, pointer) in [a, b, d].iter().enumerate() {
            for (j, bit) in [3, 4].into_iter().enumerate() {
                let port = 2 + 2 * i + j;
                for (k, wire) in increment(&mut c, pointer, bit).into_iter().enumerate() {
                    if i == 1 {
                        c.and_output(port, k, not_base, wire);
                    } else {
                        c.output(port, k, wire);
                    }
                }
            }
        }
        c.finish()
    }

    /// One instance of the operand circuit's witness by word arithmetic, into zeroed buffers, from `v1, v2, vd, flags`.
    ///
    /// ```text
    ///     words 0 ..= 2    v1, v2, vd    z = A·z = the word,              B·z = all ones
    ///     word 3           flags         z = A·z = its two bits,          B·z = 0b11
    ///     words 4, 5       accumulate, base, copies of the flag bits:  z = A·z = the bit,  B·z = 1
    ///     words 6 ..= 11   p + 8, p + 16 for each pointer: copies,     z = A·z = the sum,  B·z = all ones,
    ///                      but v2's products:                          A·z = !base on every bit,  B·z = the sum
    ///     then             the constant, then each incrementer's carries
    /// ```
    ///
    /// Adding `2^bit` to `p` carries `c_i = p_bit & .. & p_{i-1}` into bit `i > bit`, so the products of bits
    /// `bit + 1 ..= 62` are `A·z = p_i`, `B·z = c_i`.
    pub fn operand_witness(inputs: &[u64], z: &mut [u64], az: &mut [u64], bz: &mut [u64]) {
        const BITS: [u32; 2] = [3, 4];
        let [pointers @ .., flags]: [u64; 4] = inputs.try_into().expect("three pointers and the flags");
        let base = flags >> 1 & 1;
        let sums = pointers.map(|p| BITS.map(|bit| p.wrapping_add(1 << bit)));
        for (k, &p) in pointers.iter().enumerate() {
            (z[k], az[k], bz[k]) = (p, p, !0);
        }
        (z[3], az[3], bz[3]) = (flags & 3, flags & 3, 3);
        (z[4], az[4], bz[4]) = (flags & 1, flags & 1, 1);
        (z[5], az[5], bz[5]) = (base, base, 1);
        let not_base = base.wrapping_sub(1);
        for (k, &sum) in sums.as_flattened().iter().enumerate() {
            (z[6 + k], az[6 + k], bz[6 + k]) = match k / 2 {
                1 => (not_base & sum, not_base, sum),
                _ => (sum, sum, !0),
            };
        }
        let mut products = Products::new([z, az, bz], 6 + Self::OFFSET_LIMBS.len());
        products.push(1, 1, 1);
        for (&p, sums) in pointers.iter().zip(&sums) {
            for (bit, sum) in BITS.into_iter().zip(sums) {
                let carries = sum ^ p ^ 1 << bit;
                let rows = 62 - bit;
                let run = (1 << rows) - 1;
                products.push(p >> (bit + 1) & run, carries >> (bit + 1) & run, rows);
            }
        }
        products.finish();
    }
}

/// `x + 2^bit` modulo `2^64`.
///
/// The carry enters at `bit` and ripples up, one product per position past it.
///
/// ```text
///     sum_i     = x_i ^ carry_i
///     carry_i+1 = x_i & carry_i        carry_bit = 1, so carry_bit+1 = x_bit is free
/// ```
fn increment(c: &mut Builder, x: &[Wire; 64], bit: usize) -> [Wire; 64] {
    let mut out = *x;
    let mut carry = Wire::ONE;
    for (i, wire) in out.iter_mut().enumerate().skip(bit) {
        let sum = c.xor(*wire, carry);
        // The carry out of the top position falls off the modulus.
        if i + 1 < 64 {
            carry = if i == bit { *wire } else { c.and(*wire, carry) };
        }
        *wire = sum;
    }
    out
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
            // a base-field b being the one word b_0 with zero high limbs.
            let b = if flags & Ext::BASE != 0 { [b[0], 0, 0] } else { b };
            let limbs = [a[0], a[1], a[2], b[0], b[1], b[2], old[0], old[1], old[2]];
            let product = schoolbook(a, b);
            let kept = if flags & Ext::ACCUMULATE != 0 { old } else { [0; 3] };
            let c = Ext { flags, pointers: [0; 3], limbs }.eval();
            prop_assert_eq!(c, std::array::from_fn(|i| product[i] ^ kept[i]));
        }

        #[test]
        fn the_operand_circuit_is_its_reference(
            pointers in proptest::array::uniform3(edge_word()),
            flags in proptest::sample::select(Ext::LEGAL),
        ) {
            // Invariant: the outputs are the flags' two bits and the bus addresses of the limbs that are no pointer,
            // wrapping past 2^64 and zero for a base-field b's high limbs; the word witness is the gate walk's.
            let circuit = Ext::operand_circuit();
            let inputs = [pointers[0], pointers[1], pointers[2], flags];
            let words = 1 << (circuit.k_log() - 6);
            let [mut walked, mut computed] = [(); 2].map(|()| (vec![0; words], vec![0; words], vec![0; words]));
            circuit.witness_instance(&inputs, &mut walked.0, &mut walked.1, &mut walked.2);
            Ext::operand_witness(&inputs, &mut computed.0, &mut computed.1, &mut computed.2);
            let addresses = Ext::OFFSET_LIMBS.map(|k| Ext::bus_address(pointers, flags, k));
            prop_assert_eq!(&walked.0[4..6], &[flags & 1, flags >> 1]);
            prop_assert_eq!(&walked.0[6..12], &addresses);
            prop_assert_eq!(walked, computed);
        }
    }

    #[test]
    fn the_reductions_are_pinned() {
        // Invariant: y^2 * y = y^3 = y + 1, and x^63 * x = x^64 = x^4 + x^3 + x + 1.
        //
        //     (0, 0, 1) * (0, 1, 0)        ->  (1, 1, 0)
        //     (x^63, 0, 0) * (x, 0, 0)     ->  (0x1B, 0, 0)
        let product = |a: [u64; 3], b: [u64; 3]| {
            let limbs = [a[0], a[1], a[2], b[0], b[1], b[2], 0, 0, 0];
            Ext {
                flags: 0,
                pointers: [0; 3],
                limbs,
            }
            .eval()
        };
        assert_eq!(product([0, 0, 1], [0, 1, 0]), [1, 1, 0]);
        assert_eq!(product([1 << 63, 0, 0], [2, 0, 0]), [0x1B, 0, 0]);
    }

    #[test]
    fn a_base_field_operand_has_no_high_limb_accesses() {
        // Fixture: b at 0x4000_0118, as an extension and as a base-field element.
        //
        //     limb:      b_0          b_1          b_2
        //     extension  0x4000_0118  0x4000_0120  0x4000_0128
        //     base       0x4000_0118  none         none
        let pointers = [0x4000_0000, 0x4000_0118, 0x4000_0200];
        let limbs = |flags| (3..6).map(|k| Ext::limb(pointers, flags, k)).collect::<Vec<_>>();
        let memory = |a| Limb::Memory(a);
        assert_eq!(
            limbs(0),
            [memory(0x4000_0118), memory(0x4000_0120), memory(0x4000_0128)]
        );
        assert_eq!(limbs(Ext::BASE), [memory(0x4000_0118), Limb::Zero, Limb::Zero]);
    }
}
