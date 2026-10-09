//! The extension field `E = K[y] / (y^3 + y + 1)`: the machine's instructions on the VM, portable Rust elsewhere.
//!
//! `K` is `GF(2)[x] / (x^64 + x^4 + x^3 + x + 1)`, a word with bit `i` its coefficient of `x^i`.
//!
//! An element of `E` is three words, its limbs `c_0 + c_1 y + c_2 y^2`, in that order.
//!
//! These are the fields the proof system works in, so a guest computes in the field its proof is over.
//!
//! Addition is XOR, limb by limb.

/// `c = a * b` in `E`.
#[inline(always)]
pub fn mul(c: &mut [u64; 3], a: &[u64; 3], b: &[u64; 3]) {
    apply::<0>(c, a, b.as_ptr());
}

/// `c = c + a * b` in `E`.
///
/// An inner product is one of these per term.
#[inline(always)]
pub fn mul_add(c: &mut [u64; 3], a: &[u64; 3], b: &[u64; 3]) {
    apply::<1>(c, a, b.as_ptr());
}

/// `c = a * b`, with `b` in the base field `K`.
#[inline(always)]
pub fn mul_base(c: &mut [u64; 3], a: &[u64; 3], b: &u64) {
    apply::<2>(c, a, b);
}

/// `c = c + a * b`, with `b` in the base field `K`.
#[inline(always)]
pub fn mul_add_base(c: &mut [u64; 3], a: &[u64; 3], b: &u64) {
    apply::<3>(c, a, b);
}

/// The instruction `FUNCT3` on the VM, its definition elsewhere.
///
/// Bit 0 of `FUNCT3` accumulates, and bit 1 reads one word at `b` instead of three.
#[inline(always)]
fn apply<const FUNCT3: u32>(c: &mut [u64; 3], a: &[u64; 3], b: *const u64) {
    #[cfg(all(target_arch = "riscv64", target_os = "none"))]
    {
        // SAFETY: `c` and `a` are elements, and `b` is an element or a word, as `FUNCT3` reads it.
        unsafe { crate::precompile::ext::<FUNCT3>(c, a, b) }
    }
    #[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
    {
        // SAFETY: the public functions pass an element for `b`, or a word when bit 1 is set.
        let b = unsafe {
            if FUNCT3 & 2 != 0 {
                [*b, 0, 0]
            } else {
                *b.cast::<[u64; 3]>()
            }
        };
        let product = portable::mul(a, &b);
        let keep = FUNCT3 & 1 != 0;
        *c = core::array::from_fn(|i| product[i] ^ if keep { c[i] } else { 0 });
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
        // Fixture: limbs at the reduction edges, then random ones.
        let mut rng = Rng::new(0xE192);
        let edges = [0, 1, 2, 1 << 63, u64::MAX, 0x1B];
        let mut word = |i: usize| if i < 64 { edges[i % 6] } else { rng.next_u64() };
        for i in 0..2048 {
            let (a, b, old) = (
                [word(i), word(i + 1), word(i + 2)],
                [word(i + 3), word(i + 4), word(i + 5)],
                [word(i + 6), 7, 9],
            );
            let e = |v: [u64; 3]| F192::new(v[0], v[1], v[2]);
            let limbs = |v: F192| [v.c0, v.c1, v.c2];

            // The four forms, each against the host's field.
            let mut c = old;
            mul(&mut c, &a, &b);
            assert_eq!(c, limbs(e(a) * e(b)));
            mul_add(&mut c, &a, &b);
            assert_eq!(c, [0; 3], "c + c is zero");
            mul_base(&mut c, &a, &b[0]);
            assert_eq!(c, limbs(e(a).mul_base(F64(b[0]))));
            let mut c = old;
            mul_add_base(&mut c, &a, &b[0]);
            assert_eq!(c, limbs(e(old) + e(a).mul_base(F64(b[0]))));
        }
    }
}
