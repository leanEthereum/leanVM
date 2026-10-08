//! The verified skip domain against `flock::zerocheck::SkipDomain` at the native arithmetic.
//!
//! Production's public surface is `SkipDomain::FLOCK` with `vanishing` and `lagrange_at` (which run the private
//! `vanishing_coefficients`, `linearized`, `inverses`, `lagrange_scale` and `lagrange_with`); those are compared
//! directly. `SkipDomain::new` and `first_round_at` are crate-private and only run inside a whole zerocheck, so for
//! every other size, and for `first_round_at`, the copy is compared with what production's own tests compare
//! production with (`skip_domain::tests`): the product `prod_i (z + s_i)` and the weights of
//! `primitives::multilinear::skip_lagrange_weights`.
use fiat_shamir::arith::Native;
use flock::zerocheck::{SkipDomain, K_SKIP};
use leanvm_verus::gf2_64x3::F192 as VF192;
use leanvm_verus::skip_domain as verified;
use primitives::field::{F192, PHI_8_TABLE_192};
use primitives::multilinear::skip_lagrange_weights;
use primitives::test_util::Rng;

fn to_v(e: F192) -> VF192 {
    VF192::new(e.c0, e.c1, e.c2)
}

fn from_v(e: VF192) -> F192 {
    F192::new(e.c0, e.c1, e.c2)
}

/// Random points, then every node of the largest window (where production returns zero).
fn points(rng: &mut Rng) -> Vec<F192> {
    let mut out = rng.ext_vec(40);
    out.extend_from_slice(&PHI_8_TABLE_192[..]);
    out
}

#[test]
fn the_flock_domain_matches() {
    let mut rng = Rng::new(0x5D0);
    let domain = SkipDomain::FLOCK;
    let vdomain = verified::SkipDomain::FLOCK;
    assert_eq!(
        (verified::K_SKIP, vdomain.k_skip(), vdomain.size()),
        (K_SKIP, K_SKIP, 1 << K_SKIP)
    );
    for z in points(&mut rng) {
        let vanishing = domain.vanishing(&mut Native, z);
        let vvanishing = vdomain.vanishing(&mut verified::Native, to_v(z));
        assert_eq!(from_v(vvanishing), vanishing, "z={z:?}");
        let values = rng.ext_vec(1 << K_SKIP);
        let vvalues: Vec<VF192> = values.iter().copied().map(to_v).collect();
        let want = domain.lagrange_at(&mut Native, z, vanishing, &values);
        let got = vdomain.lagrange_at(&mut verified::Native, to_v(z), vvanishing, &vvalues);
        assert_eq!(from_v(got), want, "z={z:?}");
    }
}

#[test]
fn every_size_matches_the_references() {
    let mut rng = Rng::new(0x5D1);
    for k_skip in 0..8 {
        let domain = verified::SkipDomain::new(k_skip);
        let size = domain.size();
        for z in rng.ext_vec(8) {
            let vz = to_v(z);
            let vanishing = domain.vanishing(&mut verified::Native, vz);
            let product = PHI_8_TABLE_192[..size].iter().fold(F192::ONE, |acc, &s| acc * (z + s));
            assert_eq!(from_v(vanishing), product, "k_skip {k_skip}");

            let values = rng.ext_vec(size);
            let vvalues: Vec<VF192> = values.iter().copied().map(to_v).collect();
            let lagrange =
                (skip_lagrange_weights(k_skip, z).iter().zip(&values)).fold(F192::ZERO, |acc, (&w, &v)| acc + w * v);
            assert_eq!(
                from_v(domain.lagrange_at(&mut verified::Native, vz, vanishing, &vvalues)),
                lagrange,
                "k_skip {k_skip}"
            );

            let window = skip_lagrange_weights(k_skip + 1, z)[size..]
                .iter()
                .zip(&values)
                .fold(F192::ZERO, |acc, (&w, &v)| acc + w * v);
            assert_eq!(
                from_v(domain.first_round_at(&mut verified::Native, vz, vanishing, &vvalues)),
                window,
                "k_skip {k_skip}"
            );
        }
    }
}
