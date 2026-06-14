//! Tests for the deferred multiply-accumulate protocol.
//! scalar Goldilocks override (T2) and the eager default path.
//!
//! Oracle: plain canonical field arithmetic (`acc + a*b` / `acc - a*b` chains).
//! "Debug with code": failures print operand history and expected-vs-actual.

use field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField64};
use goldilocks::{CubicExtensionFieldGL, Goldilocks, P};

/// Deterministic xorshift64* PRNG (no new deps; seeded for reproducibility).
struct XorShift(u64);
impl XorShift {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
}

/// Boundary operand set (includes non-canonical representatives).
const EPS: u64 = 0xFFFF_FFFF; // 2^32 - 1 = NEG_ORDER
fn boundary_vals() -> Vec<u64> {
    vec![
        0,
        1,
        EPS,
        P - 1,
        P,
        P + 1,
        1u64 << 32,
        (1u64 << 33) - 1,
        1u64 << 63,
        u64::MAX,
    ]
}

/// Eager oracle: canonical accumulate of signed products.
fn eager_chain(terms: &[(u64, u64, bool)]) -> Goldilocks {
    let mut acc = Goldilocks::ZERO;
    for &(a, b, is_sub) in terms {
        let prod = Goldilocks::new(a) * Goldilocks::new(b);
        if is_sub {
            acc -= prod;
        } else {
            acc += prod;
        }
    }
    acc
}

/// Lazy path under test.
fn lazy_chain(terms: &[(u64, u64, bool)]) -> Goldilocks {
    let mut acc = Goldilocks::lazy_acc_zero();
    let mut n_sub = 0u64;
    for &(a, b, is_sub) in terms {
        let t = Goldilocks::unreduced_mul(Goldilocks::new(a), Goldilocks::new(b));
        if is_sub {
            acc = Goldilocks::lazy_acc_sub(acc, t);
            n_sub += 1;
        } else {
            acc = Goldilocks::lazy_acc_add(acc, t);
        }
    }
    Goldilocks::lazy_acc_finish(acc, n_sub)
}

fn assert_chains_equal(terms: &[(u64, u64, bool)], ctx: &str) {
    let expected = eager_chain(terms);
    let actual = lazy_chain(terms);
    assert_eq!(
        expected.as_canonical_u64(),
        actual.as_canonical_u64(),
        "{ctx}: lazy != eager.\n terms (a, b, is_sub) = {terms:?}\n expected {} actual {}",
        expected.as_canonical_u64(),
        actual.as_canonical_u64()
    );
}

#[test]
fn scalar_boundary_pairs_add_sub_mixed() {
    let vals = boundary_vals();
    for &a in &vals {
        for &b in &vals {
            assert_chains_equal(&[(a, b, false)], "single add");
            assert_chains_equal(&[(a, b, true)], "single sub");
            for &c in &vals {
                // add then sub, sub then add — exercises mixed-sign limb traffic.
                assert_chains_equal(&[(a, b, false), (b, c, true)], "add+sub pair");
                assert_chains_equal(&[(a, b, true), (b, c, false)], "sub+add pair");
                assert_chains_equal(&[(a, b, true), (b, c, true)], "sub+sub pair");
            }
        }
    }
}

#[test]
fn scalar_randomized_equivalence_10m() {
    // 10^7 randomized scalar iterations against the eager oracle.
    // Checked in chunks of <= 5 terms (the protocol's per-iteration term shape).
    let mut rng = XorShift(0x5EED_0001);
    let mut total = 0usize;
    while total < 10_000_000 {
        let len = 1 + (rng.next() % 5) as usize;
        let terms: Vec<(u64, u64, bool)> = (0..len)
            .map(|_| (rng.next(), rng.next(), rng.next() & 1 == 1))
            .collect();
        assert_chains_equal(&terms, "randomized chunk");
        total += len;
    }
}

#[test]
fn scalar_mixed_walks_with_prefix_checks() {
    // mixed add/sub random walks, lengths 1..8192, checking prefixes.
    let mut rng = XorShift(0x5EED_0002);
    for walk in 0..64 {
        let len = 1 + (rng.next() % 8192) as usize;
        let terms: Vec<(u64, u64, bool)> = (0..len)
            .map(|_| (rng.next(), rng.next(), rng.next() & 1 == 1))
            .collect();
        // check every prefix for short walks, end-only for long ones
        if len <= 256 {
            for p in 1..=len {
                assert_chains_equal(&terms[..p], &format!("walk {walk} prefix {p}"));
            }
        } else {
            assert_chains_equal(&terms, &format!("walk {walk} full"));
        }
    }
}

#[test]
fn scalar_worst_case_counter_growth() {
    // 2^20 iterations x 5 max-magnitude terms; exercises the overflow
    // l2-drift bound (debug_assert in finish fires if violated) and equivalence.
    let max = u64::MAX;
    let t = Goldilocks::unreduced_mul(Goldilocks::new(max), Goldilocks::new(max));
    let n: u64 = 5 * (1 << 20);

    // all-adds
    let mut acc = Goldilocks::lazy_acc_zero();
    for _ in 0..n {
        acc = Goldilocks::lazy_acc_add(acc, t);
    }
    let lazy_adds = Goldilocks::lazy_acc_finish(acc, 0);
    let prod = Goldilocks::new(max) * Goldilocks::new(max);
    let eager_adds = prod * Goldilocks::new(n);
    assert_eq!(lazy_adds.as_canonical_u64(), eager_adds.as_canonical_u64());

    // max-sub pattern
    let mut acc = Goldilocks::lazy_acc_zero();
    for _ in 0..n {
        acc = Goldilocks::lazy_acc_sub(acc, t);
    }
    let lazy_subs = Goldilocks::lazy_acc_finish(acc, n);
    let eager_subs = -eager_adds;
    assert_eq!(lazy_subs.as_canonical_u64(), eager_subs.as_canonical_u64());

    // alternating (worst mixed-sign limb churn around the OFFSET192 seed)
    let mut acc = Goldilocks::lazy_acc_zero();
    let mut n_sub = 0;
    for i in 0..n {
        if i & 1 == 0 {
            acc = Goldilocks::lazy_acc_add(acc, t);
        } else {
            acc = Goldilocks::lazy_acc_sub(acc, t);
            n_sub += 1;
        }
    }
    let lazy_alt = Goldilocks::lazy_acc_finish(acc, n_sub);
    let eager_alt = prod * Goldilocks::new(n / 2 + (n & 1)) - prod * Goldilocks::new(n / 2);
    assert_eq!(lazy_alt.as_canonical_u64(), eager_alt.as_canonical_u64());
}

#[test]
fn scalar_zero_products_interleaved() {
    // Zero products inside sub patterns (relevant to the packed ~t_hi edge in T3;
    // pinned here for the scalar path too).
    let mut rng = XorShift(0x5EED_0003);
    for _ in 0..1000 {
        let mut terms: Vec<(u64, u64, bool)> = (0..16).map(|_| (rng.next(), rng.next(), rng.next() & 1 == 1)).collect();
        terms[3] = (0, 0, true);
        terms[7] = (0, rng.next(), true);
        terms[11] = (rng.next(), 0, false);
        assert_chains_equal(&terms, "zero-product interleave");
    }
}

/// T3: packed AVX-512 override — lane-by-lane equivalence against the scalar
/// T2 override (itself pinned against the eager oracle above).
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
mod packed {
    use super::*;
    use goldilocks::PackedGoldilocksAVX512 as PG;

    const W: usize = 8;

    /// Run the same (a, b, is_sub) chain on all 8 lanes (lane i gets chain i)
    /// through the packed protocol; compare each lane's finish vs scalar lazy.
    #[allow(clippy::needless_range_loop)] // cross-indexing chains[i][j] reads clearer as index loops
    fn assert_packed_matches_scalar(chains: &[Vec<(u64, u64, bool)>; W], ctx: &str) {
        let len = chains[0].len();
        assert!(chains.iter().all(|c| c.len() == len));
        let mut acc = PG::lazy_acc_zero();
        let mut n_sub = 0u64;
        for j in 0..len {
            let a = PG(core::array::from_fn(|i| Goldilocks::new(chains[i][j].0)));
            let b = PG(core::array::from_fn(|i| Goldilocks::new(chains[i][j].1)));
            let t = PG::unreduced_mul(a, b);
            // protocol restriction: one op per step across all lanes — callers
            // (the T4 kernel) always do uniform ops, so chains share is_sub at j.
            if chains[0][j].2 {
                acc = PG::lazy_acc_sub(acc, t);
                n_sub += 1;
            } else {
                acc = PG::lazy_acc_add(acc, t);
            }
        }
        let packed = PG::lazy_acc_finish(acc, n_sub);
        for i in 0..W {
            let expected = lazy_chain(&chains[i]);
            assert_eq!(
                expected.as_canonical_u64(),
                packed.0[i].as_canonical_u64(),
                "{ctx}: lane {i} mismatch.\n chain = {:?}\n expected {} actual {}",
                chains[i],
                expected.as_canonical_u64(),
                packed.0[i].as_canonical_u64()
            );
        }
    }

    fn chains_from(rng: &mut XorShift, len: usize, sub_pattern: impl Fn(usize) -> bool) -> [Vec<(u64, u64, bool)>; W] {
        core::array::from_fn(|_| (0..len).map(|j| (rng.next(), rng.next(), sub_pattern(j))).collect())
    }

    #[test]
    fn packed_boundary_lanes() {
        // Pack the boundary set across lanes; all add, all sub, alternating.
        let vals = boundary_vals();
        for &b in &vals {
            for is_sub in [false, true] {
                let chains: [Vec<(u64, u64, bool)>; W] =
                    core::array::from_fn(|i| vec![(vals[i % vals.len()], b, is_sub)]);
                assert_packed_matches_scalar(&chains, "boundary single");
            }
        }
    }

    #[test]
    fn packed_randomized_walks() {
        let mut rng = XorShift(0x5EED_1001);
        for walk in 0..200 {
            let len = 1 + (rng.next() % 512) as usize;
            // uniform sub pattern per step (kernel-shaped); random pattern seed
            let pat = rng.next();
            let chains = chains_from(&mut rng, len, |j| (pat >> (j % 64)) & 1 == 1);
            assert_packed_matches_scalar(&chains, &format!("walk {walk}"));
        }
    }

    #[test]
    fn packed_zero_products_in_sub_patterns() {
        // The ~t_hi = 2^64-1 edge: zero (and small) products inside subs —
        // exercises the mandatory separate-K-counter design.
        let mut rng = XorShift(0x5EED_1002);
        for _ in 0..200 {
            let mut chains = chains_from(&mut rng, 32, |j| j % 3 == 1);
            for c in chains.iter_mut() {
                c[1] = (0, 0, true);
                c[4] = (0, rng.next(), true);
                c[7] = (rng.next(), 0, true);
                c[10] = (1, 1, true);
            }
            assert_packed_matches_scalar(&chains, "zero-product subs");
        }
    }

    #[test]
    fn packed_worst_case_counter_growth() {
        // 5*2^20 max-magnitude terms, all-add then
        // max-sub pattern; equivalence against the scalar override result.
        let n: u64 = 5 * (1 << 20);
        let max = PG(core::array::from_fn(|_| Goldilocks::new(u64::MAX)));
        let t = PG::unreduced_mul(max, max);

        let mut acc = PG::lazy_acc_zero();
        for _ in 0..n {
            acc = PG::lazy_acc_add(acc, t);
        }
        let packed_adds = PG::lazy_acc_finish(acc, 0);

        let mut acc = PG::lazy_acc_zero();
        for _ in 0..n {
            acc = PG::lazy_acc_sub(acc, t);
        }
        let packed_subs = PG::lazy_acc_finish(acc, n);

        let prod = Goldilocks::new(u64::MAX) * Goldilocks::new(u64::MAX);
        let eager_adds = prod * Goldilocks::new(n);
        for i in 0..W {
            assert_eq!(packed_adds.0[i].as_canonical_u64(), eager_adds.as_canonical_u64());
            assert_eq!(packed_subs.0[i].as_canonical_u64(), (-eager_adds).as_canonical_u64());
        }
    }
}

#[test]
fn default_path_is_pure_sugar_cubic_extension() {
    // CubicExtensionFieldGL does NOT override the protocol -> exercises the
    // eager defaults; pins that the trait surface is value-preserving sugar.
    type EF = CubicExtensionFieldGL;
    let mut rng = XorShift(0x5EED_0004);
    let rand_ef = |rng: &mut XorShift| -> EF { EF::from_basis_coefficients_fn(|_| Goldilocks::new(rng.next())) };
    for _ in 0..1000 {
        let terms: Vec<(EF, EF, bool)> = (0..8)
            .map(|_| (rand_ef(&mut rng), rand_ef(&mut rng), rng.next() & 1 == 1))
            .collect();
        let mut eager = EF::ZERO;
        let mut acc = EF::lazy_acc_zero();
        let mut n_sub = 0;
        for &(a, b, s) in &terms {
            let t = EF::unreduced_mul(a, b);
            if s {
                eager -= a * b;
                acc = EF::lazy_acc_sub(acc, t);
                n_sub += 1;
            } else {
                eager += a * b;
                acc = EF::lazy_acc_add(acc, t);
            }
        }
        assert_eq!(eager, EF::lazy_acc_finish(acc, n_sub));
    }
}
