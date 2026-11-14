//! `kernel-multilinear`: `primitives::multilinear` (eq tables serial and tensored, MLE evaluation serial and pooled,
//! packed weights) and `verifier::Bytecode::evaluate` (bucketed by distinct word and byte) against naive sums.

use super::reference as r;
use super::{bulk_e, bulk_k, check, edge_e};
use crate::{Ctx, Outcome, Source};
use primitives::field::{F64, F128, Weights8, dot_base};
use primitives::multilinear::{
    eq_eval, eq_table, eq_table_serial, fill_eq_table, interp, interp_k, mle_eval, mle_eval_par, packed_eq, poly_eval,
    shrink_eq_high,
};
use verifier::{Bytecode, E};

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    match src.below(5) {
        0 => eq_tables(src, ctx),
        1 => mle(src, ctx),
        2 => bytecode(src, ctx),
        3 => small(src, ctx),
        _ => packed(src, ctx),
    }
}

/// A point, often with Boolean or zero coordinates (where the eq weights degenerate).
fn point(src: &mut Source, n: usize) -> Vec<F128> {
    let mut p = bulk_e(src, n);
    match src.below(4) {
        0 => p.iter_mut().for_each(|x| *x = F128::new(src.below(2) as u64, 0)),
        1 => {
            for _ in 0..src.below(n + 1) {
                let i = src.below(n.max(1));
                if i < n {
                    p[i] = *src.pick(&[F128::ZERO, F128::ONE]);
                }
            }
        }
        _ => {}
    }
    p
}

/// `eq(r, .)` by doubling, with the reference product, LSB-first.
fn eq_ref(point: &[F128], seed: F128) -> Vec<F128> {
    let mut t = vec![seed];
    for &rk in point {
        let hi: Vec<F128> = t.iter().map(|&x| r::mul_e(x, rk)).collect();
        let lo: Vec<F128> = t.iter().zip(&hi).map(|(&x, &h)| r::add_e(x, h)).collect();
        t = [lo, hi].concat();
    }
    t
}

fn eq_tables(src: &mut Source, ctx: &Ctx) -> Outcome {
    let n = match src.below(8) {
        0 => src.range(15, 17),
        _ => src.below(13),
    };
    ctx.note(format!("eq vars {}", if n >= 16 { "tensored" } else { "doubling" }));
    let p = point(src, n);
    let want = eq_ref(&p, F128::ONE);
    check!(eq_table(&p) == want, "eq_table", "{n} variables");
    if n <= 13 {
        check!(eq_table_serial(&p) == want, "eq_table_serial", "{n} variables");
    }
    let seed = edge_e(src);
    let mut out = vec![F128::new(7, 7); 1 << n];
    fill_eq_table(&p, seed, &mut out);
    check!(out == eq_ref(&p, seed), "fill_eq_table", "{n} variables, seed {seed:?}");
    for _ in 0..3 {
        let i = src.below(1 << n);
        let x: Vec<F128> = (0..n).map(|k| F128::new((i >> k & 1) as u64, 0)).collect();
        check!(eq_eval(&p, &x) == want[i], "eq_eval", "{n} variables at index {i}");
    }
    if n > 0 {
        let mut t = want.clone();
        shrink_eq_high(&mut t);
        check!(t == eq_ref(&p[..n - 1], F128::ONE), "shrink_eq_high", "{n} variables");
    }
    Ok(())
}

/// `sum_i table[i] eq(point, i)` with the reference product.
fn mle_ref(table: &[F64], point: &[F128]) -> F128 {
    let eq = eq_ref(point, F128::ONE);
    table
        .iter()
        .zip(&eq)
        .fold(F128::ZERO, |s, (k, &w)| r::add_e(s, r::mul_base(w, k.0)))
}

fn table(src: &mut Source, n: usize) -> Vec<F64> {
    let mut t = bulk_k(src, 1 << n);
    match src.below(5) {
        0 => {
            // Sparse: a few nonzero words.
            let nonzero: Vec<usize> = (0..src.below(6)).map(|_| src.below(1 << n)).collect();
            for (i, w) in t.iter_mut().enumerate() {
                if !nonzero.contains(&i) {
                    *w = F64::ZERO;
                }
            }
        }
        1 => {
            // Few distinct words, as a bytecode table has.
            let words: Vec<u64> = (0..src.range(1, 6)).map(|_| src.edgy_u64()).collect();
            let picks = src.bulk(1 << n);
            for (w, &b) in t.iter_mut().zip(&picks) {
                *w = F64(if b & 1 == 0 { 0 } else { words[b as usize % words.len()] });
            }
        }
        2 => {
            // Whole zero blocks of the verifier's 2^14-word blocking.
            for (i, w) in t.iter_mut().enumerate() {
                if (i >> 14) % 2 == 1 || i >> 13 == 0 {
                    *w = F64::ZERO;
                }
            }
        }
        _ => {}
    }
    t
}

fn mle(src: &mut Source, ctx: &Ctx) -> Outcome {
    let n = match src.below(8) {
        0 => src.range(12, 16),
        _ => src.below(12),
    };
    ctx.note(format!("mle vars {}", n.min(12)));
    let t = table(src, n);
    let p = point(src, n);
    let want = mle_ref(&t, &p);
    check!(mle_eval(&t, &p) == want, "mle_eval", "{n} variables");
    check!(mle_eval_par(&t, &p) == want, "mle_eval_par", "{n} variables");
    let words: Vec<u64> = t.iter().map(|w| w.0).collect();
    let ve = Bytecode::new(&words).evaluate(&p.iter().map(|x| E::new(x.c0, x.c1)).collect::<Vec<_>>());
    check!(
        ve.as_ref().map(|e| F128::new(e.c0, e.c1)) == Ok(want),
        "verifier Bytecode::evaluate",
        "{n} variables: {ve:?}, want {want:?}"
    );
    Ok(())
}

/// The verifier's bucketed evaluation on bytecode-shaped tables, beyond one 2^14-word block, and its refusal of a
/// point of the wrong length.
fn bytecode(src: &mut Source, ctx: &Ctx) -> Outcome {
    let n = match src.below(4) {
        0 => src.range(14, 16),
        _ => src.below(14),
    };
    ctx.note(format!("bytecode vars {}", n.min(14)));
    let t = table(src, n);
    let words: Vec<u64> = t.iter().map(|w| w.0).collect();
    let bc = Bytecode::new(&words);
    check!(
        bc.len() == 1 << n && !bc.is_empty(),
        "verifier Bytecode::len",
        "{n} variables"
    );
    let p = point(src, n);
    let want = mle_ref(&t, &p);
    let vp: Vec<E> = p.iter().map(|x| E::new(x.c0, x.c1)).collect();
    let got = bc.evaluate(&vp);
    check!(
        got.map(|e| F128::new(e.c0, e.c1)) == Ok(want),
        "verifier Bytecode::evaluate",
        "{n} variables: got {got:?}, want {want:?}"
    );
    // A point of another length is an error, not a panic.
    let other = match src.below(3) {
        0 => n + 1,
        1 => n.saturating_sub(1),
        _ => 64 + src.below(4),
    };
    if other != n {
        let wrong: Vec<E> = (0..other).map(|_| E::new(1, 0)).collect();
        check!(
            bc.evaluate(&wrong).is_err(),
            "verifier Bytecode::evaluate",
            "accepted a point of {other} coordinates for 2^{n} words"
        );
    }
    Ok(())
}

fn small(src: &mut Source, ctx: &Ctx) -> Outcome {
    ctx.note("small");
    let (lo, hi, t) = (edge_e(src), edge_e(src), edge_e(src));
    check!(
        interp(lo, hi, t) == r::add_e(lo, r::mul_e(t, r::add_e(lo, hi))),
        "interp",
        "{lo:?} {hi:?} {t:?}"
    );
    let (kl, kh) = (F64(src.u64()), F64(src.edgy_u64()));
    check!(
        interp_k(kl, kh, t) == r::add_e(F128::from(kl), r::mul_base(t, kl.0 ^ kh.0)),
        "interp_k",
        "{kl:?} {kh:?} {t:?}"
    );
    let n = src.below(10);
    let coeffs = bulk_e(src, n);
    let x = edge_e(src);
    let mut want = F128::ZERO;
    let mut power = F128::ONE;
    for &c in &coeffs {
        want = r::add_e(want, r::mul_e(c, power));
        power = r::mul_e(power, x);
    }
    check!(
        poly_eval(&coeffs, x) == want,
        "poly_eval",
        "{} coefficients at {x:?}",
        coeffs.len()
    );
    Ok(())
}

fn packed(src: &mut Source, ctx: &Ctx) -> Outcome {
    let n = src.range(3, 11);
    ctx.note(format!("packed vars {}", n.min(6)));
    let p = point(src, n);
    let eq = eq_ref(&p, F128::ONE);
    let packed = packed_eq(&p);
    check!(
        packed.len() == eq.len() / 8,
        "packed_eq",
        "{n} variables: {} groups",
        packed.len()
    );
    for (g, w) in packed.iter().enumerate() {
        for i in 0..8 {
            check!(
                w.get(i) == eq[8 * g + i],
                "packed_eq",
                "{n} variables, weight {}",
                8 * g + i
            );
        }
    }
    let k = bulk_k(src, eq.len());
    let want = eq
        .iter()
        .zip(&k)
        .fold(F128::ZERO, |s, (&w, x)| r::add_e(s, r::mul_base(w, x.0)));
    check!(dot_base(&packed, &k).reduce() == want, "dot_base", "{n} variables");
    let rebuilt: Vec<Weights8> = eq.as_chunks::<8>().0.iter().map(Weights8::new).collect();
    check!(
        dot_base(&rebuilt, &k).reduce() == want,
        "dot_base",
        "{n} variables, packed by hand"
    );
    Ok(())
}
