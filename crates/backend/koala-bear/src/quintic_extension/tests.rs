// Property tests for QuinticExtensionField and PackedQuinticExtensionField.
//
// These verify algebraic properties that any correct field extension must
// satisfy. They are a prerequisite for allowing the autoresearch loop to
// modify quintic_extension code — without them, a subtle arithmetic bug
// could pass the end-to-end WHIR test while silently corrupting proofs.
//
// Each test uses a seeded RNG for reproducibility and runs 200 random
// iterations (enough to hit alignment/packing edge cases without being slow).

#[cfg(test)]
mod tests {
    use crate::KoalaBear;
    use crate::quintic_extension::extension::QuinticExtensionField;
    use crate::quintic_extension::packed_extension::PackedQuinticExtensionField;
    use field::{Field, PackedFieldExtension, PackedValue, PrimeCharacteristicRing};
    use rand::rngs::StdRng;
    use rand::{RngExt, SeedableRng};

    type QEF = QuinticExtensionField<KoalaBear>;
    type PQEF = PackedQuinticExtensionField<KoalaBear, <KoalaBear as Field>::Packing>;

    const ITERS: usize = 200;

    fn rng() -> StdRng {
        StdRng::seed_from_u64(0xdeadbeef_cafef00d)
    }

    fn rand_nonzero(rng: &mut StdRng) -> QEF {
        loop {
            let x: QEF = rng.random();
            if !x.is_zero() {
                return x;
            }
        }
    }

    // ---------------------------------------------------------------
    // Scalar QuinticExtensionField arithmetic properties
    // ---------------------------------------------------------------

    #[test]
    fn mul_commutative() {
        let mut rng = rng();
        for _ in 0..ITERS {
            let a: QEF = rng.random();
            let b: QEF = rng.random();
            assert_eq!(a * b, b * a, "commutativity: a*b != b*a");
        }
    }

    #[test]
    fn mul_associative() {
        let mut rng = rng();
        for _ in 0..ITERS {
            let a: QEF = rng.random();
            let b: QEF = rng.random();
            let c: QEF = rng.random();
            assert_eq!((a * b) * c, a * (b * c), "associativity: (a*b)*c != a*(b*c)");
        }
    }

    #[test]
    fn mul_distributive_over_add() {
        let mut rng = rng();
        for _ in 0..ITERS {
            let a: QEF = rng.random();
            let b: QEF = rng.random();
            let c: QEF = rng.random();
            assert_eq!(a * (b + c), a * b + a * c, "distributivity: a*(b+c) != a*b + a*c");
        }
    }

    #[test]
    fn mul_identity() {
        let mut rng = rng();
        let one = QEF::ONE;
        let zero = QEF::ZERO;
        for _ in 0..ITERS {
            let a: QEF = rng.random();
            assert_eq!(a * one, a, "a * ONE != a");
            assert_eq!(a * zero, zero, "a * ZERO != ZERO");
        }
    }

    #[test]
    fn add_sub_roundtrip() {
        let mut rng = rng();
        for _ in 0..ITERS {
            let a: QEF = rng.random();
            let b: QEF = rng.random();
            assert_eq!((a + b) - b, a, "(a+b)-b != a");
            assert_eq!((a - b) + b, a, "(a-b)+b != a");
        }
    }

    #[test]
    fn neg_double_is_identity() {
        let mut rng = rng();
        for _ in 0..ITERS {
            let a: QEF = rng.random();
            assert_eq!(-(-a), a, "--a != a");
            assert_eq!(a + (-a), QEF::ZERO, "a + (-a) != 0");
        }
    }

    #[test]
    fn square_equals_self_mul() {
        let mut rng = rng();
        for _ in 0..ITERS {
            let a: QEF = rng.random();
            assert_eq!(a.square(), a * a, "a.square() != a * a");
        }
    }

    #[test]
    fn inverse_roundtrip() {
        let mut rng = rng();
        let one = QEF::ONE;
        for _ in 0..ITERS {
            let a = rand_nonzero(&mut rng);
            let inv = a.try_inverse().expect("nonzero element should be invertible");
            assert_eq!(a * inv, one, "a * a^-1 != 1");
            assert_eq!(inv * a, one, "a^-1 * a != 1");
        }
    }

    #[test]
    fn zero_not_invertible() {
        assert!(QEF::ZERO.try_inverse().is_none(), "zero should not be invertible");
    }

    #[test]
    fn base_field_embedding() {
        let mut rng = rng();
        for _ in 0..ITERS {
            let x: KoalaBear = rng.random();
            let y: KoalaBear = rng.random();
            let ex = QEF::from(x);
            let ey = QEF::from(y);
            assert_eq!(QEF::from(x * y), ex * ey, "embedding must preserve mul");
            assert_eq!(QEF::from(x + y), ex + ey, "embedding must preserve add");
        }
    }

    // frobenius is private; skip automorphism test.
    // If frobenius becomes pub, uncomment and test:
    // fn frobenius_is_automorphism() { ... }

    // ---------------------------------------------------------------
    // Packed ↔ scalar consistency
    // ---------------------------------------------------------------

    const WIDTH: usize = <<KoalaBear as Field>::Packing as PackedValue>::WIDTH;

    fn make_packed(elems: &[QEF]) -> PQEF {
        assert_eq!(elems.len(), WIDTH);
        PQEF::from_ext_slice(elems)
    }

    fn unpack(p: PQEF) -> Vec<QEF> {
        <PQEF as PackedFieldExtension<KoalaBear, QEF>>::to_ext_iter([p]).collect()
    }

    #[test]
    fn packed_add_matches_scalar() {
        let mut rng = rng();
        for _ in 0..ITERS {
            let a: Vec<QEF> = (0..WIDTH).map(|_| rng.random()).collect();
            let b: Vec<QEF> = (0..WIDTH).map(|_| rng.random()).collect();
            let pa = make_packed(&a);
            let pb = make_packed(&b);
            let result = unpack(pa + pb);
            for i in 0..WIDTH {
                assert_eq!(result[i], a[i] + b[i], "packed add lane {i} mismatch");
            }
        }
    }

    #[test]
    fn packed_sub_matches_scalar() {
        let mut rng = rng();
        for _ in 0..ITERS {
            let a: Vec<QEF> = (0..WIDTH).map(|_| rng.random()).collect();
            let b: Vec<QEF> = (0..WIDTH).map(|_| rng.random()).collect();
            let pa = make_packed(&a);
            let pb = make_packed(&b);
            let result = unpack(pa - pb);
            for i in 0..WIDTH {
                assert_eq!(result[i], a[i] - b[i], "packed sub lane {i} mismatch");
            }
        }
    }

    #[test]
    fn packed_mul_matches_scalar() {
        let mut rng = rng();
        for _ in 0..ITERS {
            let a: Vec<QEF> = (0..WIDTH).map(|_| rng.random()).collect();
            let b: Vec<QEF> = (0..WIDTH).map(|_| rng.random()).collect();
            let pa = make_packed(&a);
            let pb = make_packed(&b);
            let result = unpack(pa * pb);
            for i in 0..WIDTH {
                assert_eq!(result[i], a[i] * b[i], "packed mul lane {i} mismatch");
            }
        }
    }

    #[test]
    fn packed_base_mul_matches_scalar() {
        let mut rng = rng();
        for _ in 0..ITERS {
            let a: Vec<QEF> = (0..WIDTH).map(|_| rng.random()).collect();
            let s: KoalaBear = rng.random();
            let pa = make_packed(&a);
            let result = unpack(pa * s);
            for i in 0..WIDTH {
                assert_eq!(result[i], a[i] * QEF::from(s), "packed base-mul lane {i} mismatch");
            }
        }
    }

    #[test]
    fn packed_roundtrip() {
        let mut rng = rng();
        for _ in 0..ITERS {
            let elems: Vec<QEF> = (0..WIDTH).map(|_| rng.random()).collect();
            let packed = make_packed(&elems);
            let unpacked = unpack(packed);
            assert_eq!(unpacked, elems, "pack → unpack roundtrip failed");
        }
    }
}
