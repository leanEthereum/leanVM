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
//! Addition in `E` is XOR limb by limb, which the machine already has.

use super::InstructionClass;
use crate::rv::circuits::{ClassCircuit, Word, WordGadgets};
use crate::rv::entry::Class;
use crate::tables::Separator;
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
    /// A base-field `b` has two zero limbs, which the row reads from `x0`.
    pub limbs: [u64; Self::LIMBS],
}

/// Where one of an instance's limbs is read.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Limb {
    /// The memory word at this byte address.
    Memory(u64),
    /// The register `x0`, which holds zero: a high limb of a base-field `b`.
    Zero,
}

impl Ext {
    /// Add the product to `c` instead of overwriting it.
    pub const ACCUMULATE: u64 = 1 << 0;
    /// `b` is a base-field element: one word, its high limbs zero.
    pub const BASE: u64 = 1 << 1;
    /// The limbs the row accesses: three for each of `a`, `b` and `c`.
    pub const LIMBS: usize = 9;

    /// Where limb `k` of an instance with these pointers and flags is read.
    ///
    /// ```text
    ///     k:        0    1     2      3    4     5      6    7     8
    ///     limb:     a_0  a_1   a_2    b_0  b_1   b_2    c_0  c_1   c_2
    ///     address:  pa   pa+8  pa+16  pb   pb+8  pb+16  pc   pc+8  pc+16
    /// ```
    ///
    /// A base-field `b` reads `b_1` and `b_2` from `x0` instead.
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

    /// The bus separator of limb `k`: registers for a limb read from `x0`, memory otherwise.
    const fn separator(flags: u64, k: usize) -> u64 {
        match Self::limb([0; 3], flags, k) {
            Limb::Zero => Separator::Registers.value().0,
            Limb::Memory(_) => Separator::Memory.value().0,
        }
    }

    /// The bus address of limb `k`: the register number zero for a limb read from `x0`.
    const fn bus_address(pointers: [u64; 3], flags: u64, k: usize) -> u64 {
        match Self::limb(pointers, flags, k) {
            Limb::Zero => 0,
            Limb::Memory(address) => address,
        }
    }
}

/// What one instance computes: the limbs it writes, and where its limbs are on the bus.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExtResult {
    /// `c`'s limbs after the instruction.
    pub c: [u64; 3],
    /// The bus addresses of the limbs that are no pointer: limbs 1, 2, 4, 5, 7 and 8.
    pub addresses: [u64; 6],
    /// The bus separator of `b`'s high limbs, limbs 4 and 5.
    pub separator: u64,
}

impl ExtResult {
    /// The limbs whose bus address the circuit computes: every limb but the three pointers.
    pub const OFFSET_LIMBS: [usize; 6] = [1, 2, 4, 5, 7, 8];
    /// The limbs whose bus separator the circuit computes: `b`'s high limbs, which share it.
    pub const SEPARATED_LIMBS: [usize; 2] = [4, 5];
}

impl InstructionClass for Ext {
    const CLASS: Class = Class::Ext;

    /// Overwrite or accumulate, by an extension or a base-field element.
    const LEGAL: &'static [u64] = &[0, Self::ACCUMULATE, Self::BASE, Self::BASE | Self::ACCUMULATE];

    /// What the instance writes and where its limbs are.
    type Output = ExtResult;

    fn eval(&self) -> ExtResult {
        debug_assert!(Self::LEGAL.contains(&self.flags));
        let l = &self.limbs;
        let element = |i: usize| F192::new(l[3 * i], l[3 * i + 1], l[3 * i + 2]);

        // The product, then the old `c` added on an accumulation.
        let mut c = element(0) * element(1);
        if self.flags & Self::ACCUMULATE != 0 {
            c += element(2);
        }

        // Where the limbs that are no pointer go on the bus.
        let (pointers, flags) = (self.pointers, self.flags);
        ExtResult {
            c: [c.c0, c.c1, c.c2],
            addresses: ExtResult::OFFSET_LIMBS.map(|k| Self::bus_address(pointers, flags, k)),
            separator: Self::separator(flags, ExtResult::SEPARATED_LIMBS[0]),
        }
    }

    /// The three pointers, the flags, then the nine limbs.
    fn input_words(&self) -> Vec<u64> {
        let head = [self.pointers[0], self.pointers[1], self.pointers[2], self.flags];
        head.into_iter().chain(self.limbs).collect()
    }

    /// `c`'s new limbs, then the six computed addresses, then the separator.
    fn output_words(out: &ExtResult) -> Vec<u64> {
        out.c.into_iter().chain(out.addresses).chain([out.separator]).collect()
    }
}

impl ClassCircuit for Ext {
    /// The extension-field product: `(pa, pb, pc, flags, a, b, c) -> (c', addresses, separator)`.
    ///
    /// Products are made in four groups, in this order:
    ///
    /// ```text
    ///     multiply     a * b in E: 6 products in K by Karatsuba over y      6 * 729 = 4374
    ///     accumulate   c' = a * b + flags_0 * c                                       192
    ///     addresses    p + 8 and p + 16 for each pointer, by incrementers              351
    ///     base field   b's high limbs read from x0: addresses gated off               128
    /// ```
    ///
    /// Both reductions, `y^3 = y + 1` and `x^64 = x^4 + x^3 + x + 1`, are XORs.
    ///
    /// With 1472 port bits and the constant, the instance fills 6518 of its 8192 bits.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 64, 2, 64, 64, 64, 64, 64, 64, 64, 64, 64], &[64; 10]);
        let pointers: [Word; 3] = std::array::from_fn(|i| c.input(i));
        let flags = c.input(3);
        let (accumulate, base) = (flags[0], flags[1]);
        let limb: Vec<Word> = (0..Self::LIMBS).map(|k| c.input(4 + k)).collect();

        // Phase 1: the product of a and b, unreduced, by Karatsuba over y.
        //
        //     d_0 = a_0 b_0                d_3 = (a_1 + a_2)(b_1 + b_2) + a_1 b_1 + a_2 b_2
        //     d_1 = (a_0 + a_1)(b_0 + b_1) + a_0 b_0 + a_1 b_1
        //     d_2 = (a_0 + a_2)(b_0 + b_2) + a_0 b_0 + a_2 b_2 + a_1 b_1        d_4 = a_2 b_2
        let (a, b) = (&limb[0..3], &limb[3..6]);
        let p00 = karatsuba(&mut c, &a[0], &b[0]);
        let p11 = karatsuba(&mut c, &a[1], &b[1]);
        let p22 = karatsuba(&mut c, &a[2], &b[2]);
        let sum = |c: &mut Builder, i: usize, j: usize| {
            let (sa, sb) = (c.xor_word(&a[i], &a[j]), c.xor_word(&b[i], &b[j]));
            karatsuba(c, &sa, &sb)
        };
        let s01 = sum(&mut c, 0, 1);
        let s02 = sum(&mut c, 0, 2);
        let s12 = sum(&mut c, 1, 2);
        let xor_all = |c: &mut Builder, terms: &[&Word]| -> Word {
            terms
                .iter()
                .skip(1)
                .fold(terms[0].clone(), |acc, t| c.xor_word(&acc, t))
        };
        let d1 = xor_all(&mut c, &[&s01, &p00, &p11]);
        let d2 = xor_all(&mut c, &[&s02, &p00, &p22, &p11]);
        let d3 = xor_all(&mut c, &[&s12, &p11, &p22]);

        // The y-fold: y^3 = y + 1 and y^4 = y^2 + y, so d_3 lands on y^0, y^1 and d_4 on y^1, y^2.
        let e0 = c.xor_word(&p00, &d3);
        let e1 = xor_all(&mut c, &[&d1, &d3, &p22]);
        let e2 = c.xor_word(&d2, &p22);

        // Phase 2: each coefficient reduced in K, then the old c added on an accumulation.
        let c_old = &limb[6..9];
        for (i, e) in [e0, e1, e2].into_iter().enumerate() {
            let product = reduce(&mut c, e);
            let kept = c.and_word(accumulate, &c_old[i]);
            let out = c.xor_word(&product, &kept);
            c.output_word(i, &out);
        }

        // Phase 3: the six limb addresses that are no pointer, p + 8 and p + 16.
        let mut offsets: Vec<Word> = Vec::with_capacity(6);
        for pointer in &pointers {
            offsets.push(increment(&mut c, pointer, 3));
            offsets.push(increment(&mut c, pointer, 4));
        }

        // Phase 4: a base-field b reads its high limbs from x0, register number zero.
        //
        //     separator  base ? registers : memory      constants and base: no product
        //     address    base ? 0 : pb + 8k            one product per bit
        let not_base = c.not(base);
        for slot in [2, 3] {
            offsets[slot] = c.and_word(not_base, &offsets[slot]);
        }
        for (i, offset) in offsets.iter().enumerate() {
            c.output_word(3 + i, offset);
        }
        let separator: Word = (0..64)
            .map(|bit| {
                match (
                    Separator::Registers.value().0 >> bit & 1,
                    Separator::Memory.value().0 >> bit & 1,
                ) {
                    (1, 1) => c.one(),
                    (1, 0) => base,
                    (0, 1) => not_base,
                    _ => None,
                }
            })
            .collect();
        c.output_word(9, &separator);
        c.finish()
    }
}

/// The carry-less product of two polynomials of `n` coefficients, `n` a power of two: `2n - 1` coefficients.
///
/// Each level splits both factors in halves of `h = n / 2` coefficients:
///
/// ```text
///     (a_0 + a_1 x^h)(b_0 + b_1 x^h) = lo + (mid + lo + hi) x^h + hi x^(2h)
///
///     lo  = a_0 b_0     hi  = a_1 b_1     mid = (a_0 + a_1)(b_0 + b_1)
/// ```
///
/// Three half-size products instead of four: `3^6 = 729` single-bit products for 64 coefficients.
///
/// The products are made in the order `lo`, `hi`, `mid`, recursively, which fixes their slots.
fn karatsuba(c: &mut Builder, a: &[Wire], b: &[Wire]) -> Word {
    let n = a.len();
    debug_assert!(n.is_power_of_two() && b.len() == n);
    // One coefficient each: one product.
    if n == 1 {
        return vec![c.and(a[0], b[0])];
    }
    // The three half-size products, in their fixed order.
    let h = n / 2;
    let (a0, a1) = a.split_at(h);
    let (b0, b1) = b.split_at(h);
    let lo = karatsuba(c, a0, b0);
    let hi = karatsuba(c, a1, b1);
    let (sa, sb) = (c.xor_word(a0, a1), c.xor_word(b0, b1));
    let mid = karatsuba(c, &sa, &sb);
    // Each half-size product has 2h - 1 coefficients, placed at offsets 0, h and 2h.
    //
    //     coefficient:   0 ........ 2h-2
    //     lo             [   lo    ]
    //     mid+lo+hi            [ mid+lo+hi ]            at h
    //     hi                         [   hi    ]        at 2h
    let mut out: Word = vec![None; 2 * n - 1];
    for i in 0..2 * h - 1 {
        let cross = c.xor(mid[i], lo[i]);
        let cross = c.xor(cross, hi[i]);
        out[i] = c.xor(out[i], lo[i]);
        out[i + h] = c.xor(out[i + h], cross);
        out[i + 2 * h] = c.xor(out[i + 2 * h], hi[i]);
    }
    out
}

/// A product of 127 coefficients reduced modulo `x^64 + x^4 + x^3 + x + 1`: 64 coefficients.
///
/// Coefficient `d >= 64` folds back by `x^d = x^(d-64) (x^4 + x^3 + x + 1)`.
///
/// It lands at `d - 64`, `d - 63`, `d - 61` and `d - 60`.
///
/// The highest lands at 66, still above 63, so the folds run from the top down.
fn reduce(c: &mut Builder, mut p: Word) -> Word {
    debug_assert_eq!(p.len(), 127);
    for d in (64..p.len()).rev() {
        for offset in [64, 63, 61, 60] {
            p[d - offset] = c.xor(p[d - offset], p[d]);
        }
    }
    p.truncate(64);
    p
}

/// `x + 2^bit` modulo `2^64`.
///
/// The carry enters at `bit` and ripples up, one product per position past it.
///
/// ```text
///     sum_i     = x_i ^ carry_i
///     carry_i+1 = x_i & carry_i        carry_bit = 1, so carry_bit+1 = x_bit is free
/// ```
fn increment(c: &mut Builder, x: &[Wire], bit: usize) -> Word {
    let mut out = x.to_vec();
    let mut carry = c.one();
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
    use crate::rv::semantics::tests::{circuit_matches_reference, edge_word};
    use proptest::prelude::*;
    use proptest::sample::select;
    use proptest::strategy::BoxedStrategy;

    /// Any extension-field instance, as a run makes them.
    ///
    /// A base-field `b` reads its high limbs from `x0`, so they are zero.
    impl Arbitrary for Ext {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            let words = proptest::array::uniform9(edge_word());
            (select(Self::LEGAL), proptest::array::uniform3(edge_word()), words)
                .prop_map(|(flags, pointers, mut limbs)| {
                    if flags & Self::BASE != 0 {
                        (limbs[4], limbs[5]) = (0, 0);
                    }
                    Self { flags, pointers, limbs }
                })
                .boxed()
        }
    }

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
        fn the_product_is_the_specified_field(a in proptest::array::uniform3(edge_word()), b in proptest::array::uniform3(edge_word())) {
            // The reference multiplies in K[y] / (y^3 + y + 1), K modulo x^64 + x^4 + x^3 + x + 1.
            let limbs = [a[0], a[1], a[2], b[0], b[1], b[2], 0, 0, 0];
            let instance = Ext { flags: 0, pointers: [0; 3], limbs };
            prop_assert_eq!(instance.eval().c, schoolbook(a, b));
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
            .c
        };
        assert_eq!(product([0, 0, 1], [0, 1, 0]), [1, 1, 0]);
        assert_eq!(product([1 << 63, 0, 0], [2, 0, 0]), [0x1B, 0, 0]);
    }

    #[test]
    fn a_base_field_operand_reads_its_high_limbs_from_x0() {
        // Fixture: b at 0x4000_0100, as an extension and as a base-field element.
        //
        //     limb:      b_0          b_1          b_2
        //     extension  0x4000_0100  0x4000_0108  0x4000_0110
        //     base       0x4000_0100  x0           x0
        let pointers = [0x4000_0000, 0x4000_0100, 0x4000_0200];
        let limbs = |flags| (3..6).map(|k| Ext::limb(pointers, flags, k)).collect::<Vec<_>>();
        let memory = |a| Limb::Memory(a);
        assert_eq!(
            limbs(0),
            [memory(0x4000_0100), memory(0x4000_0108), memory(0x4000_0110)]
        );
        assert_eq!(limbs(Ext::BASE), [memory(0x4000_0100), Limb::Zero, Limb::Zero]);
    }

    #[test]
    fn the_product_takes_six_karatsuba_products() {
        // Invariant: 6 * 3^6 products for a * b, and the rest as the circuit's doc counts them.
        //
        //     multiply 4374 + accumulate 192 + addresses 351 + base field 128 = 5045
        assert_eq!(Ext::circuit().n_products(), 5045);
    }

    #[test]
    fn ext_circuit_matches_the_reference() {
        // Legal flags, edge-biased pointers and limbs pin the gate list to the reference function.
        circuit_matches_reference::<Ext>(2048);
    }
}
