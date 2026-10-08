//! The extension field `E = K[y] / (y^3 + y + 1)`: the machine's extension registers on the VM, portable Rust elsewhere.
//!
//! `K` is `GF(2)[x] / (x^64 + x^4 + x^3 + x + 1)`, a word with bit `i` its coefficient of `x^i`.
//!
//! An element of `E` is three words, its limbs `c_0 + c_1 y + c_2 y^2`, in that order.
//!
//! These are the fields the proof system works in, so a guest computes in the field its proof is over.
//!
//! The machine has 128 extension registers, `f0` to `f127`, one element each, and one instruction computing on them:
//!
//! ```text
//!     fd = fa * fb        or  fd = fd + fa * fb        b an extension register, or a base-field word
//! ```
//!
//! A register is named by its number, a constant of the program: the compiler allocates none of them.
//!
//! `f0`, `f1` and `f2` hold `1`, `y` and `y^2`, and are never written. They are how a word becomes an element:
//! `1 * w` is `w` in `E`, and an element is `1 * l_0 + y * l_1 + y^2 * l_2`.

/// The register holding the constant `1`.
pub const ONE: u8 = 0;
/// The register holding the constant `y`.
pub const Y: u8 = 1;
/// The register holding the constant `y^2`.
pub const Y2: u8 = 2;

/// How many extension registers there are.
const COUNT: usize = 128;

/// The extension registers.
///
/// On the VM they are the machine's, so a program makes one of these, in its `main`, and hands it down.
///
/// Elsewhere they are this value's own, starting as the machine's do: the constants, then zeros.
pub struct Registers {
    #[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
    cells: [[u64; 3]; COUNT],
}

impl Default for Registers {
    fn default() -> Self {
        Self::new()
    }
}

impl Registers {
    /// The registers as a run starts.
    pub const fn new() -> Self {
        #[cfg(all(target_arch = "riscv64", target_os = "none"))]
        {
            Self {}
        }
        #[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
        {
            let mut cells = [[0; 3]; COUNT];
            (cells[0][0], cells[1][1], cells[2][2]) = (1, 1, 1);
            Self { cells }
        }
    }

    /// `fD = fA * fB`.
    #[inline(always)]
    pub fn mul<const D: u8, const A: u8, const B: u8>(&mut self) {
        self.apply::<0, D, A, B>(0);
    }

    /// `fD = fD + fA * fB`.
    #[inline(always)]
    pub fn mul_add<const D: u8, const A: u8, const B: u8>(&mut self) {
        self.apply::<1, D, A, B>(0);
    }

    /// `fD = fA * b`, with `b` in the base field `K`.
    #[inline(always)]
    pub fn mul_base<const D: u8, const A: u8>(&mut self, b: u64) {
        self.apply::<2, D, A, 0>(b);
    }

    /// `fD = fD + fA * b`, with `b` in the base field `K`.
    ///
    /// An inner product with base-field words is one of these per term.
    #[inline(always)]
    pub fn mul_add_base<const D: u8, const A: u8>(&mut self, b: u64) {
        self.apply::<3, D, A, 0>(b);
    }

    /// `fD = fD + fA * fB`, and whether that is zero: whether `fD` was `fA * fB`.
    ///
    /// On the VM a run only goes on if it is, so this returns `true` there or never returns.
    #[inline(always)]
    #[must_use]
    pub fn mul_add_is_zero<const D: u8, const A: u8, const B: u8>(&mut self) -> bool {
        self.apply::<5, D, A, B>(0)
    }

    /// `fD = fD + fA * b`, with `b` in `K`, and whether that is zero, as [`Self::mul_add_is_zero`].
    #[inline(always)]
    #[must_use]
    pub fn mul_add_base_is_zero<const D: u8, const A: u8>(&mut self, b: u64) -> bool {
        self.apply::<7, D, A, 0>(b)
    }

    /// `fD = limbs`: `1 * l_0 + y * l_1 + y^2 * l_2`.
    #[inline(always)]
    pub fn load<const D: u8>(&mut self, limbs: &[u64; 3]) {
        self.mul_base::<D, ONE>(limbs[0]);
        self.mul_add_base::<D, Y>(limbs[1]);
        self.mul_add_base::<D, Y2>(limbs[2]);
    }

    /// The instruction `FUNCT3` on the VM, its definition elsewhere, and whether a checked form's result is zero.
    ///
    /// Bit 0 of `FUNCT3` accumulates, bit 1 takes the word `b` for `fB`, and bit 2 requires a zero result.
    #[inline(always)]
    fn apply<const FUNCT3: u32, const D: u8, const A: u8, const B: u8>(&mut self, b: u64) -> bool {
        const {
            assert!(D >= 3, "the constants are never written");
            assert!(
                (D as usize) < COUNT && (A as usize) < COUNT && (B as usize) < COUNT,
                "an extension register"
            );
        }
        #[cfg(all(target_arch = "riscv64", target_os = "none"))]
        {
            if FUNCT3 & 2 != 0 {
                crate::precompile::ext_base::<FUNCT3, D, A>(b);
            } else {
                crate::precompile::ext::<FUNCT3, D, A, B>();
            }
            true
        }
        #[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
        {
            let b = if FUNCT3 & 2 != 0 {
                [b, 0, 0]
            } else {
                self.cells[B as usize]
            };
            let product = portable::mul(&self.cells[A as usize], &b);
            let c = &mut self.cells[D as usize];
            let keep = FUNCT3 & 1 != 0;
            *c = core::array::from_fn(|i| product[i] ^ if keep { c[i] } else { 0 });
            FUNCT3 & 4 == 0 || *c == [0; 3]
        }
    }

    /// What register `r` holds: a host's view, which the VM has none of.
    #[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
    pub const fn get(&self, r: u8) -> [u64; 3] {
        self.cells[r as usize]
    }
}

/// The products by their definitions, for a host.
#[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
mod portable {
    /// The product in `E`: schoolbook in `y`, then `y^3 = y + 1` and `y^4 = y^2 + y`.
    pub fn mul(a: &[u64; 3], b: &[u64; 3]) -> [u64; 3] {
        // The five coefficients of y^0 to y^4.
        let mut d = [0u64; 5];
        for i in 0..3 {
            for j in 0..3 {
                d[i + j] ^= mul_base(a[i], b[j]);
            }
        }
        [d[0] ^ d[3], d[1] ^ d[3] ^ d[4], d[2] ^ d[4]]
    }

    /// The product in `K`: the carry-less product, reduced.
    fn mul_base(a: u64, b: u64) -> u64 {
        // One partial product `a * x^i` per set bit `i` of `b`.
        let wide = (0..64).fold(0u128, |p, i| p ^ (u128::from(a) * u128::from(b >> i & 1)) << i);
        reduce(wide)
    }

    /// Reduce a carry-less product of degree below 127 modulo `x^64 + x^4 + x^3 + x + 1`.
    ///
    /// ```text
    ///   hi * x^64 = f(hi),     f(v) = v ^ v<<1 ^ v<<3 ^ v<<4
    ///   the 4 bits f shifts past x^63 fold back once more
    /// ```
    const fn reduce(p: u128) -> u64 {
        let (lo, hi) = (p as u64, (p >> 64) as u64);
        // Folding the spill into `hi` first merges the two folds, as `f` is linear.
        let v = hi ^ (hi >> 63) ^ (hi >> 61) ^ (hi >> 60);
        lo ^ v ^ (v << 1) ^ (v << 3) ^ (v << 4)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::field::{F64, F192};
    use primitives::test_util::Rng;

    #[test]
    fn the_portable_field_is_the_proof_systems() {
        // Invariant: off the VM every form computes in the F192 the machine and the proof use.
        //
        // Fixture: limbs at the reduction edges, then random ones, loaded into f3, f4 and f5.
        let mut rng = Rng::new(0xE192);
        let edges = [0, 1, 2, 1 << 63, u64::MAX, 0x1B];
        let mut word = |i: usize| if i < 64 { edges[i % 6] } else { rng.next_u64() };
        let mut r = Registers::new();
        assert_eq!([r.get(ONE), r.get(Y), r.get(Y2)], [[1, 0, 0], [0, 1, 0], [0, 0, 1]]);
        for i in 0..2048 {
            let (a, b, old) = (
                [word(i), word(i + 1), word(i + 2)],
                [word(i + 3), word(i + 4), word(i + 5)],
                [word(i + 6), 7, 9],
            );
            let e = |v: [u64; 3]| F192::new(v[0], v[1], v[2]);
            let limbs = |v: F192| [v.c0, v.c1, v.c2];
            r.load::<3>(&a);
            r.load::<4>(&b);
            r.load::<5>(&old);
            assert_eq!([r.get(3), r.get(4), r.get(5)], [a, b, old]);

            // The forms, each against the host's field.
            r.mul::<6, 3, 4>();
            assert_eq!(r.get(6), limbs(e(a) * e(b)));
            assert!(r.mul_add_is_zero::<6, 3, 4>(), "c + c is zero");
            r.mul_base::<6, 3>(b[0]);
            assert_eq!(r.get(6), limbs(e(a).mul_base(F64(b[0]))));
            r.mul_add_base::<5, 3>(b[0]);
            assert_eq!(r.get(5), limbs(e(old) + e(a).mul_base(F64(b[0]))));
            r.mul_add::<5, 3, 4>();
            assert_eq!(r.get(5), limbs(e(old) + e(a).mul_base(F64(b[0])) + e(a) * e(b)));

            // A checked form says whether its result is zero.
            r.mul_base::<6, ONE>(1);
            assert!(!r.mul_add_base_is_zero::<6, ONE>(3));
            assert!(r.mul_add_base_is_zero::<6, ONE>(2));
        }
    }
}
