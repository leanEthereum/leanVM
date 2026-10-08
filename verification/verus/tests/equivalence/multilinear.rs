//! The verified `eq` tables, their marginalizations, the split table and the MLE evaluation against
//! `primitives::multilinear`.
//!
//! `fill_eq_doubling`, `fold_low_k`, `fold_ladder` and `packed_eq` are private in production; they are reached
//! through `fill_eq_table_uninit` (the doubling below `EQ_PAR_LEN` entries) and `mle_eval` (the other three).
use leanvm_verus::gf2_64::F64 as VF64;
use leanvm_verus::gf2_64x3::F192 as VF192;
use leanvm_verus::multilinear as verified;
use primitives::field::{F192, F64};
use primitives::multilinear as production;
use primitives::test_util::Rng;
use std::mem::MaybeUninit;

fn to_v(e: F192) -> VF192 {
    VF192::new(e.c0, e.c1, e.c2)
}

fn to_vs(v: &[F192]) -> Vec<VF192> {
    v.iter().copied().map(to_v).collect()
}

fn from_vs(v: &[VF192]) -> Vec<F192> {
    v.iter().map(|e| F192::new(e.c0, e.c1, e.c2)).collect()
}

/// Random elements with zero and one mixed in, so the products hit their edge cases.
fn point(rng: &mut Rng, n: usize) -> Vec<F192> {
    (0..n)
        .map(|_| match rng.next_u32() % 5 {
            0 => F192::ZERO,
            1 => F192::ONE,
            _ => rng.ext(),
        })
        .collect()
}

#[test]
fn interpolations_match() {
    let mut rng = Rng::new(0x1A7E);
    for _ in 0..20_000 {
        let (lo, hi, t) = (rng.ext(), rng.ext(), point(&mut rng, 1)[0]);
        assert_eq!(
            from_vs(&[verified::interp(to_v(lo), to_v(hi), to_v(t))]),
            [production::interp(lo, hi, t)]
        );
        let (a, b) = (rng.next_u64(), rng.next_u64());
        assert_eq!(
            from_vs(&[verified::interp_k(VF64(a), VF64(b), to_v(t))]),
            [production::interp_k(F64(a), F64(b), t)]
        );
    }
}

#[test]
fn eq_evals_match() {
    let mut rng = Rng::new(0xE0E7);
    for n in 0..12 {
        for _ in 0..200 {
            let (r, x) = (point(&mut rng, n), point(&mut rng, n));
            assert_eq!(
                from_vs(&[verified::eq_eval(&to_vs(&r), &to_vs(&x))]),
                [production::eq_eval(&r, &x)],
                "n={n}"
            );
        }
    }
}

#[test]
fn eq_tables_match() {
    // Up to 17 variables: from 16 on, production takes the parallel tensor pass.
    let mut rng = Rng::new(0xE07A);
    for n in 0..=17 {
        let rounds = if n < 12 { 20 } else { 2 };
        for _ in 0..rounds {
            let (r, seed) = (point(&mut rng, n), rng.ext());
            assert_eq!(
                from_vs(&verified::eq_table(&to_vs(&r))),
                production::eq_table(&r),
                "n={n}"
            );
            let want = production::eq_table_seeded(&r, seed);
            assert_eq!(
                from_vs(&verified::eq_table_seeded(&to_vs(&r), to_v(seed))),
                want,
                "n={n}"
            );

            let mut out = vec![MaybeUninit::<F192>::uninit(); 1 << n];
            production::fill_eq_table_uninit(&r, seed, &mut out);
            // SAFETY: the fill writes every entry.
            let filled: Vec<F192> = out.iter().map(|e| unsafe { e.assume_init() }).collect();
            let mut vout = vec![VF192::ZERO; 1 << n];
            verified::fill_eq_table_uninit(&to_vs(&r), to_v(seed), &mut vout);
            assert_eq!(from_vs(&vout), filled, "n={n}");
        }
    }
}

#[test]
fn shrinks_match() {
    let mut rng = Rng::new(0x5A81);
    for n in 0..=12 {
        for _ in 0..10 {
            // Any table, not only an `eq` table: the copies are the pairwise sums of whatever they get.
            let t: Vec<F192> = if rng.bit() {
                production::eq_table_seeded(&point(&mut rng, n), rng.ext())
            } else {
                rng.ext_vec(1 << n)
            };
            let (mut p, mut v) = (t.clone(), to_vs(&t));
            production::shrink_eq_low(&mut p);
            verified::shrink_eq_low(&mut v);
            assert_eq!(from_vs(&v), p, "low n={n}");
            let (mut p, mut v) = (t.clone(), to_vs(&t));
            production::shrink_eq_high(&mut p);
            verified::shrink_eq_high(&mut v);
            assert_eq!(from_vs(&v), p, "high n={n}");
        }
    }
}

#[test]
fn split_tables_match() {
    let mut rng = Rng::new(0x5B17);
    for n in 0..=12 {
        let r = point(&mut rng, n);
        let vr = to_vs(&r);
        for max in [0, 1, 3, 5, 12, 20] {
            let (p, v) = (
                production::SplitEq::with_low_vars(&r, max),
                verified::SplitEq::with_low_vars(&vr, max),
            );
            assert_eq!(
                (from_vs(&v.low), from_vs(&v.high), v.low_log()),
                (p.low.clone(), p.high.clone(), p.low_log())
            );
            for x in 0..1usize << n {
                assert_eq!(from_vs(&[v.at(x)]), [p.at(x)], "n={n} max_low={max} x={x}");
            }
            let (p, v) = (
                production::SplitEq::with_high_vars(&r, max),
                verified::SplitEq::with_high_vars(&vr, max),
            );
            assert_eq!(
                (from_vs(&v.low), from_vs(&v.high), v.low_log()),
                (p.low.clone(), p.high.clone(), p.low_log())
            );
            for x in 0..1usize << n {
                assert_eq!(from_vs(&[v.at(x)]), [p.at(x)], "n={n} max_high={max} x={x}");
            }
        }
    }
}

#[test]
fn mle_evals_match() {
    // Below three variables production folds the table directly; from three on it packs the low table, and from
    // eleven on there is more than one row.
    let mut rng = Rng::new(0x31E0);
    for n in 0..=14 {
        for _ in 0..(if n < 10 { 20 } else { 3 }) {
            let table: Vec<F64> = (0..1usize << n).map(|_| F64(rng.next_u64())).collect();
            let p = point(&mut rng, n);
            let vt: Vec<VF64> = table.iter().map(|w| VF64(w.0)).collect();
            assert_eq!(
                from_vs(&[verified::mle_eval(&vt, &to_vs(&p))]),
                [production::mle_eval(&table, &p)],
                "n={n}"
            );
        }
    }
}

#[test]
fn window_denominators_match() {
    for log in 0..=8 {
        let size = 1usize << log;
        assert_eq!(
            from_vs(&[verified::window_denominator(size)]),
            [production::window_denominator(size)],
            "size {size}"
        );
        assert_eq!(
            from_vs(&[verified::DENOMINATORS[log]]),
            [production::window_denominator(size)],
            "log {log}"
        );
    }
}
