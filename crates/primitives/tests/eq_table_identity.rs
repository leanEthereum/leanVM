//! `eq_table` feeds the verifier (via the leanvm_core constraint and GKR paths and
//! flock's univariate skip), so its rewrite must be bit-identical to the
//! two-multiply form, not merely algebraically equal.
//!
//! Old: `hi = e · r`, `lo = e · (1 + r)` : two products.
//! New: `hi = e · r`, `lo = e + e · r`   : one product.
//!
//! These agree by distributivity in characteristic 2, and F192 stores a
//! canonical reduced `(c0, c1, c2)`, so the bit patterns must match exactly.
use primitives::field::F192;
use primitives::test_util::Rng;

/// Verbatim copy of the pre-change implementation.
fn eq_table_old(r: &[F192]) -> Vec<F192> {
    let mut eq = vec![F192::ZERO; 1usize << r.len()];
    eq[0] = F192::ONE;
    let mut half = 1usize;
    for &rk in r {
        let one_plus = F192::ONE + rk;
        for i in (0..half).rev() {
            let e = eq[i];
            eq[i + half] = e * rk;
            eq[i] = e * one_plus;
        }
        half <<= 1;
    }
    eq
}

#[test]
fn eq_table_is_bit_identical_to_two_multiply_form() {
    let mut rng = Rng::new(0xE0_1D_5E_ED);
    for n in [0usize, 1, 2, 3, 6, 7, 11, 12, 13, 14, 16, 17] {
        for _ in 0..4 {
            let r: Vec<F192> = (0..n).map(|_| rng.ext()).collect();
            let want = eq_table_old(&r);
            let got = primitives::multilinear::eq_table(&r);
            assert_eq!(got.len(), want.len(), "length differs at n={n}");
            for (x, (g, w)) in got.iter().zip(want.iter()).enumerate() {
                assert_eq!(g, w, "bit mismatch at n={n}, x={x}");
            }
        }
    }
}

/// Boolean points are where a representation difference would most likely
/// surface, since `1 + r` collapses to 0 or 1 there.
#[test]
fn eq_table_is_bit_identical_at_boolean_points() {
    for n in 1..=10usize {
        for mask in 0..(1usize << n) {
            let r: Vec<F192> = (0..n)
                .map(|i| if (mask >> i) & 1 == 1 { F192::ONE } else { F192::ZERO })
                .collect();
            assert_eq!(
                primitives::multilinear::eq_table(&r),
                eq_table_old(&r),
                "bit mismatch at n={n}, mask={mask}"
            );
        }
    }
}

#[test]
fn a_seeded_eq_table_is_the_scaled_table() {
    // Invariant: the seeded fill, and the arena build, are the plain table scaled by the seed, on both sides of the
    // tensor-product threshold.
    let mut rng = Rng::new(21);
    for n in [0usize, 1, 6, 13, 15, 17] {
        let point: Vec<F192> = (0..n).map(|_| rng.ext()).collect();
        let plain = eq_table_old(&point);
        assert_eq!(
            &*primitives::multilinear::eq_table_arena(&point),
            &plain[..],
            "arena build, n={n}"
        );
        let seed = rng.ext();
        let mut seeded = zk_alloc::alloc_uninit(1 << n);
        primitives::multilinear::fill_eq_table_uninit(&point, seed, &mut seeded);
        // SAFETY: the fill writes every entry.
        let seeded = unsafe { zk_alloc::assume_init(seeded) };
        let scaled: Vec<F192> = plain.iter().map(|&e| seed * e).collect();
        assert_eq!(&*seeded, &scaled, "seeded fill, n={n}");
    }
}
