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

/// Native field products delegated to the external polynomial-basis backend.
#[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
mod portable {
    use p3_binary_field::{Poly64, Poly192};

    pub fn mul(a: &[u64; 3], b: &[u64; 3]) -> [u64; 3] {
        let element = |words: &[u64; 3]| Poly192::new(words.map(Poly64::new));
        (element(a) * element(b)).coefficients().map(Poly64::to_bits)
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use primitives::test_util::Rng;
    use primitives::{F64, F192};

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
            let e = |v: [u64; 3]| F192::new([F64::new(v[0]), F64::new(v[1]), F64::new(v[2])]);
            let limbs = |v: F192| {
                [
                    v.coefficients()[0].to_bits(),
                    v.coefficients()[1].to_bits(),
                    v.coefficients()[2].to_bits(),
                ]
            };

            // The four forms, each against the host's field.
            let mut c = old;
            mul(&mut c, &a, &b);
            assert_eq!(c, limbs(e(a) * e(b)));
            mul_add(&mut c, &a, &b);
            assert_eq!(c, [0; 3], "c + c is zero");
            mul_base(&mut c, &a, &b[0]);
            assert_eq!(c, limbs(e(a) * F64::new(b[0])));
            let mut c = old;
            mul_add_base(&mut c, &a, &b[0]);
            assert_eq!(c, limbs(e(old) + (e(a) * F64::new(b[0]))));
        }
    }
}
