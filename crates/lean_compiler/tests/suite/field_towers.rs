//! Random cross-check of F128 = GF((2^64)^2) against its portable reference,
//! through the same `primitives` re-export path the VM uses. `primitives`
//! itself only pins the dispatched `Mul` against `software::mul` on a handful
//! of fixed Python-generated vectors (plus 10k random inputs on aarch64), so on
//! a pclmulqdq x86 host this is the random-input check on that dispatch.

use primitives::field::{F128, F128Unreduced};
use rand::Rng;

fn rand_f128(rng: &mut impl Rng) -> F128 {
    F128::new(rng.random(), rng.random())
}

#[test]
fn f128_field_behaviour() {
    let mut rng = rand::rng();
    for _ in 0..500 {
        let (a, b, c) = (rand_f128(&mut rng), rand_f128(&mut rng), rand_f128(&mut rng));
        // ring axioms + agreement with the portable reference
        assert_eq!(a * b, primitives::field::gf2_64x2::software::mul(a, b));
        assert_eq!(a * b, b * a);
        assert_eq!((a * b) * c, a * (b * c));
        assert_eq!(a * (b + c), a * b + a * c);
        assert_eq!(a.square(), a * a);
        if !a.is_zero() {
            assert_eq!(a * a.inv(), F128::ONE);
        }
        let mut acc = F128Unreduced::ZERO;
        acc ^= a.mul_unreduced(b);
        acc ^= a.mul_unreduced(c);
        assert_eq!(acc.reduce(), a * b + a * c);
    }
    // y^2 = x*y + 1 (the defining relation)
    let x = F128::from(primitives::field::F64::G);
    assert_eq!(F128::Y * F128::Y, x * F128::Y + F128::ONE);
}
