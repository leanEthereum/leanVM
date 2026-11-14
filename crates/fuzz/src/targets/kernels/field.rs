//! `kernel-field`: every public product, square, power and inverse of `K` and `E`, scalar and batched, against the
//! schoolbook reference and the verifier's field.

use super::reference as r;
use super::{bulk_e, bulk_k, check, edge_e, edge_k};
use crate::{Ctx, Outcome, Source};
use primitives::field::{
    self, F64, F64x8, F128, F128Unreduced, F128x8, Prod8, Weights8, dot_base, fold_lones8_ext, fold_pairs8_ext, g_pow,
    g_pow32_by_lookup, g_powers, gf2_64, msg_lone8_ext, msg_terms8_ext, mul_base_splat8, mul_unreduced4, mul2, mul4,
    powers, xor_into8,
};
use verifier::{E, K};

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    match src.below(8) {
        0 => base(src, ctx),
        1 => extension(src, ctx),
        2 => batched(src, ctx),
        3 => wide8(src, ctx),
        4 => g_powers_case(src, ctx),
        5 => inverses(src, ctx),
        6 => verifier_field(src, ctx),
        _ => accumulate(src, ctx),
    }
}

fn base(src: &mut Source, ctx: &Ctx) -> Outcome {
    ctx.note("base");
    let (a, b) = (edge_k(src), edge_k(src));
    let want = r::mul_k(a.0, b.0);
    check!(
        (a * b).0 == want,
        "F64 mul",
        "{a:?} * {b:?}: got {:?}, want {want:#x}",
        a * b
    );
    let mut c = a;
    c *= b;
    check!(c.0 == want, "F64 mul_assign", "{a:?} * {b:?}");
    check!(
        gf2_64::mul_wide(a.0, b.0) == r::clmul(a.0, b.0),
        "mul_wide",
        "{a:?} {b:?}"
    );
    check!(
        gf2_64::software::clmul(a.0, b.0) == r::clmul(a.0, b.0),
        "software::clmul",
        "{a:?} {b:?}"
    );
    check!(gf2_64::square_wide(a.0) == r::clmul(a.0, a.0), "square_wide", "{a:?}");
    let p = (u128::from(src.u64()) << 64) | u128::from(src.u64());
    check!(gf2_64::reduce(p) == r::reduce(p), "gf2_64::reduce", "{p:#x}");
    check!(a.square().0 == r::mul_k(a.0, a.0), "F64 square", "{a:?}");
    let e = u128::from(src.edgy_u64())
        | if src.chance(1, 4) {
            u128::from(src.u64()) << 64
        } else {
            0
        };
    check!(a.pow(e).0 == r::pow_k(a.0, e), "F64 pow", "{a:?}^{e}");
    check!(
        field::mul_by_g(a).0 == r::mul_k(a.0, 2),
        "mul_by_g",
        "{a:?}: got {:?}",
        field::mul_by_g(a)
    );
    check!(
        field::div_by_g(field::mul_by_g(a)) == a,
        "div_by_g",
        "{a:?} after mul_by_g"
    );
    check!(
        r::mul_k(field::div_by_g(a).0, 2) == a.0,
        "div_by_g",
        "{a:?}: got {:?}",
        field::div_by_g(a)
    );
    let n = src.below(9);
    let xs = bulk_k(src, n);
    let sum: F64 = xs.iter().sum();
    let prod: F64 = xs.iter().product();
    check!(sum.0 == xs.iter().fold(0, |s, x| s ^ x.0), "F64 sum", "{xs:?}");
    check!(
        prod.0 == xs.iter().fold(1, |p, x| r::mul_k(p, x.0)),
        "F64 product",
        "{xs:?}"
    );
    #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
    {
        // SAFETY: the cfg enables pclmulqdq.
        let got = unsafe { gf2_64::x86_64::mul(a.0, b.0) };
        check!(got == want, "gf2_64::x86_64::mul", "{a:?} * {b:?}");
        // SAFETY: the cfg enables pclmulqdq.
        let got = unsafe { gf2_64::x86_64::clmul(a.0, b.0) };
        check!(got == r::clmul(a.0, b.0), "gf2_64::x86_64::clmul", "{a:?} * {b:?}");
    }
    #[cfg(all(target_arch = "x86_64", target_feature = "bmi2"))]
    {
        // SAFETY: the cfg enables bmi2.
        let got = unsafe { gf2_64::x86_64::spread(a.0) };
        check!(got == r::clmul(a.0, a.0), "gf2_64::x86_64::spread", "{a:?}");
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    {
        // SAFETY: the cfg enables aes.
        let got = unsafe { gf2_64::aarch64::mul_shift_tail(a, b) };
        check!(got.0 == want, "gf2_64::aarch64::mul_shift_tail", "{a:?} * {b:?}");
    }
    Ok(())
}

fn extension(src: &mut Source, ctx: &Ctx) -> Outcome {
    ctx.note("extension");
    let (a, b, k) = (edge_e(src), edge_e(src), edge_k(src));
    let want = r::mul_e(a, b);
    check!(
        a * b == want,
        "F128 mul",
        "{a:?} * {b:?}: got {:?}, want {want:?}",
        a * b
    );
    let mut c = a;
    c *= b;
    check!(c == want, "F128 mul_assign", "{a:?} * {b:?}");
    check!(
        a.mul_unreduced(b).reduce() == want,
        "F128 mul_unreduced",
        "{a:?} * {b:?}"
    );
    check!(
        field::gf2_64x2::software::mul(a, b) == want,
        "gf2_64x2::software::mul",
        "{a:?} * {b:?}"
    );
    check!(
        field::gf2_64x2::software::mul_unreduced(a, b) == a.mul_unreduced(b),
        "F128 mul_unreduced coefficients",
        "{a:?} * {b:?}: unreduced products are exact polynomials and must agree across kernels"
    );
    let base = r::mul_base(a, k.0);
    check!(a.mul_base(k) == base, "F128 mul_base", "{a:?} * {k:?}");
    check!(
        a.mul_base_unreduced(k).reduce() == base,
        "F128 mul_base_unreduced",
        "{a:?} * {k:?}"
    );
    check!(
        a.mul_base_unreduced(k) == a.mul_unreduced(F128::from(k)),
        "F128 mul_base_unreduced coefficients",
        "{a:?} * {k:?}"
    );
    check!(a * F128::from(k) == base, "F128 mul by an embedded K", "{a:?} * {k:?}");
    check!(a.square() == r::mul_e(a, a), "F128 square", "{a:?}");
    check!(
        a.frobenius() == r::pow_e(a, 1 << 64),
        "F128 frobenius",
        "{a:?}: got {:?}",
        a.frobenius()
    );
    check!(a + b == r::add_e(a, b), "F128 add", "{a:?} + {b:?}");
    let mut s = a;
    s += b;
    check!(s == r::add_e(a, b), "F128 add_assign", "{a:?} + {b:?}");
    check!(
        F128::from_limbs(a.to_limbs()) == a && a.to_limbs() == [a.c0, a.c1],
        "F128 limbs",
        "{a:?}"
    );
    check!(
        a.as_base() == (a.c1 == 0).then_some(F64(a.c0)),
        "F128 as_base",
        "{a:?}"
    );
    check!(a.is_zero() == (a == F128::ZERO), "F128 is_zero", "{a:?}");
    let n = src.below(9);
    let xs = bulk_e(src, n);
    let sum: F128 = xs.iter().sum();
    let prod: F128 = xs.iter().product();
    check!(
        sum == xs.iter().fold(F128::ZERO, |s, &x| r::add_e(s, x)),
        "F128 sum",
        "{xs:?}"
    );
    check!(
        prod == xs.iter().fold(F128::ONE, |p, &x| r::mul_e(p, x)),
        "F128 product",
        "{xs:?}"
    );
    let n = src.below(40);
    let x = edge_e(src);
    let mut p = F128::ONE;
    for (i, &got) in powers(x, n).iter().enumerate() {
        check!(got == p, "powers", "{x:?}^{i}");
        p = r::mul_e(p, x);
    }
    check!(powers(x, n).len() == n, "powers", "length {n}");
    let index = src.below(12);
    let zeta = bulk_e(src, index);
    let mut want = F128::ONE;
    for (k, &z) in zeta.iter().enumerate() {
        let g2k = r::pow_k(2, 1u128 << k);
        want = r::mul_e(want, r::add_e(F128::ONE, r::mul_base(z, 1 ^ g2k)));
    }
    check!(field::index_mle(&zeta) == want, "index_mle", "{zeta:?}");
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    {
        use field::gf2_64x2::aarch64 as neon;
        check!(
            neon::mul(a, b) == want_mul(a, b),
            "gf2_64x2::aarch64::mul",
            "{a:?} * {b:?}"
        );
        check!(
            neon::mul_base(a, k) == base,
            "gf2_64x2::aarch64::mul_base",
            "{a:?} * {k:?}"
        );
        check!(neon::square(a) == r::mul_e(a, a), "gf2_64x2::aarch64::square", "{a:?}");
        check!(
            neon::reduce(neon::mul_unreduced(a, b)) == want_mul(a, b),
            "gf2_64x2::aarch64::mul_unreduced",
            "{a:?} * {b:?}"
        );
        check!(
            neon::reduce(neon::mul_base_unreduced(a, k)) == base,
            "gf2_64x2::aarch64::mul_base_unreduced",
            "{a:?} * {k:?}"
        );
    }
    Ok(())
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
fn want_mul(a: F128, b: F128) -> F128 {
    r::mul_e(a, b)
}

fn arr8(src: &mut Source) -> [F128; 8] {
    bulk_e(src, 8).try_into().unwrap()
}

fn arr8k(src: &mut Source) -> [F64; 8] {
    bulk_k(src, 8).try_into().unwrap()
}

fn batched(src: &mut Source, ctx: &Ctx) -> Outcome {
    ctx.note("batched");
    let (a, b) = (arr8(src), arr8(src));
    let want: [F128; 8] = std::array::from_fn(|i| r::mul_e(a[i], b[i]));
    let two = mul2([a[0], a[1]], [b[0], b[1]]);
    check!(two == [want[0], want[1]], "mul2", "{a:?} * {b:?}");
    let four = mul4([a[0], a[1], a[2], a[3]], [b[0], b[1], b[2], b[3]]);
    check!(four[..] == want[..4], "mul4", "{a:?} * {b:?}");
    let un = mul_unreduced4([a[4], a[5], a[6], a[7]], [b[4], b[5], b[6], b[7]]);
    for i in 0..4 {
        check!(
            un[i].reduce() == want[4 + i],
            "mul_unreduced4",
            "lane {i}: {a:?} * {b:?}"
        );
        check!(
            un[i] == a[4 + i].mul_unreduced(b[4 + i]),
            "mul_unreduced4 coefficients",
            "lane {i}: {a:?} * {b:?}"
        );
    }
    // Weights8 round trips, and dot_base is the mixed inner product.
    let n = src.range(0, 6);
    let weights: Vec<[F128; 8]> = (0..n).map(|_| arr8(src)).collect();
    let packed: Vec<Weights8> = weights.iter().map(Weights8::new).collect();
    for (w, p) in weights.iter().zip(&packed) {
        for (i, &wi) in w.iter().enumerate() {
            check!(p.get(i) == wi, "Weights8", "weight {i} of {w:?}");
        }
    }
    let ks = bulk_k(src, 8 * n);
    let want = weights
        .as_flattened()
        .iter()
        .zip(&ks)
        .fold(F128::ZERO, |s, (&w, k)| r::add_e(s, r::mul_base(w, k.0)));
    check!(dot_base(&packed, &ks).reduce() == want, "dot_base", "{n} groups");
    Ok(())
}

fn wide8(src: &mut Source, ctx: &Ctx) -> Outcome {
    ctx.note("wide8");
    let (x0, x1, y0, y1) = (arr8(src), arr8(src), arr8(src), arr8(src));
    let (k0, k1) = (arr8k(src), arr8k(src));
    let rr = edge_e(src);
    let lane = |f: &dyn Fn(usize) -> F128| -> [F128; 8] { std::array::from_fn(f) };
    let dot = |x: &[F128; 8], y: &[F128; 8]| (0..8).fold(F128::ZERO, |s, j| r::add_e(s, r::mul_e(x[j], y[j])));
    let interp = |lo: F128, hi: F128, t: F128| r::add_e(lo, r::mul_e(t, r::add_e(lo, hi)));

    check!(
        fold_pairs8_ext(&x0, &x1, rr) == lane(&|j| interp(x0[j], x1[j], rr)),
        "fold_pairs8_ext",
        "r = {rr:?}"
    );
    check!(
        fold_lones8_ext(&x0, rr) == lane(&|j| r::add_e(x0[j], r::mul_e(rr, x0[j]))),
        "fold_lones8_ext",
        "r = {rr:?}"
    );
    let (u0, u2) = msg_terms8_ext(&x0, &x1, &y0, &y1);
    let xs = lane(&|j| r::add_e(x0[j], x1[j]));
    let ys = lane(&|j| r::add_e(y0[j], y1[j]));
    check!(u0.reduce() == dot(&x0, &y0), "msg_terms8_ext", "first term");
    check!(u2.reduce() == dot(&xs, &ys), "msg_terms8_ext", "second term");
    check!(msg_lone8_ext(&x0, &y0).reduce() == dot(&x0, &y0), "msg_lone8_ext", "");
    let mut per: Prod8 = mul_base_splat8(rr, &k0);
    per ^= mul_base_splat8(x0[0], &k1);
    check!(
        per.reduce_lanes().to_array() == lane(&|j| r::add_e(r::mul_base(rr, k0[j].0), r::mul_base(x0[0], k1[j].0))),
        "mul_base_splat8",
        ""
    );
    let mut sum = x0;
    xor_into8(&mut sum, &x1);
    check!(sum == xs, "xor_into8", "");

    let (xa, xb, xc) = (
        F128x8::from_array(&x0),
        F128x8::from_array(&x1),
        F128x8::from_array(&y0),
    );
    check!(xa.to_array() == x0, "F128x8 from_array", "");
    check!(F128x8::splat(rr).to_array() == [rr; 8], "F128x8 splat", "");
    check!((xa + xb).to_array() == xs, "F128x8 add", "");
    check!(
        (xa * xb).to_array() == lane(&|j| r::mul_e(x0[j], x1[j])),
        "F128x8 mul",
        "{x0:?} * {x1:?}"
    );
    let sums = (xa.mul_unreduced(xb) ^ xc.mul_unreduced(xa)).reduce_lanes();
    check!(
        sums.to_array() == lane(&|j| r::add_e(r::mul_e(x0[j], x1[j]), r::mul_e(y0[j], x0[j]))),
        "F128x8 mul_unreduced",
        ""
    );
    check!(xa.mul_unreduced(xb).reduce() == dot(&x0, &x1), "Prod8 reduce", "");
    let (even, odd) = F128x8::even_odd(xa, xb);
    check!(
        even.to_array() == lane(&|j| if j < 4 { x0[2 * j] } else { x1[2 * (j - 4)] }),
        "F128x8 even_odd",
        "even"
    );
    check!(
        odd.to_array() == lane(&|j| if j < 4 { x0[2 * j + 1] } else { x1[2 * (j - 4) + 1] }),
        "F128x8 even_odd",
        "odd"
    );
    let (ka, kb) = (F64x8::from_array(&k0), F64x8::from_array(&k1));
    check!(
        F128x8::from(ka + kb).to_array() == lane(&|j| F128::from(F64(k0[j].0 ^ k1[j].0))),
        "F64x8 add",
        ""
    );
    check!(
        xa.mul_base_unreduced(ka).reduce_lanes().to_array() == lane(&|j| r::mul_base(x0[j], k0[j].0)),
        "F128x8 mul_base_unreduced",
        ""
    );
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
    x8(src, ctx, &x0, &x1, &k0)?;
    Ok(())
}

/// The AVX-512 coefficient-major lanes, `primitives::field::x8`.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
fn x8(src: &mut Source, ctx: &Ctx, x0: &[F128; 8], x1: &[F128; 8], k0: &[F64; 8]) -> Outcome {
    use primitives::field::x8::{F64x8 as K8, F128x8 as E8, Mixed8, Sum8};
    ctx.note("x8");
    let (a, b) = (E8::load(x0), E8::load(x1));
    check!(a.to_array() == *x0, "x8::F128x8 load/store", "");
    let mut out = [F128::ZERO; 8];
    (a * b).store(&mut out);
    check!(
        out == std::array::from_fn(|j| r::mul_e(x0[j], x1[j])),
        "x8::F128x8 mul",
        "{x0:?} * {x1:?}"
    );
    check!(
        (a + b).to_array() == std::array::from_fn(|j| r::add_e(x0[j], x1[j])),
        "x8::F128x8 add",
        ""
    );
    let mut s = a;
    s += b;
    check!(s.to_array() == (a + b).to_array(), "x8::F128x8 add_assign", "");
    let dot = (0..8).fold(F128::ZERO, |s, j| r::add_e(s, r::mul_e(x0[j], x1[j])));
    check!(a.mul_sum(b).reduce() == dot, "x8::F128x8 mul_sum", "");
    check!((Sum8::ZERO ^ a.mul_sum(b)).reduce() == dot, "x8::Sum8 xor", "");
    let (ev, od) = E8::deinterleave(a, b);
    check!(
        ev.to_array() == std::array::from_fn(|j| if j < 4 { x0[2 * j] } else { x1[2 * (j - 4)] }),
        "x8::F128x8 deinterleave",
        ""
    );
    check!(
        od.to_array() == std::array::from_fn(|j| if j < 4 { x0[2 * j + 1] } else { x1[2 * (j - 4) + 1] }),
        "x8::F128x8 deinterleave",
        ""
    );
    let (lo, hi) = E8::interleave(ev, od);
    check!(
        lo.to_array() == *x0 && hi.to_array() == *x1,
        "x8::F128x8 interleave",
        "not the inverse of deinterleave"
    );
    let block: [F128; 64] = bulk_e(src, 64).try_into().unwrap();
    let runs = E8::load_runs(&block);
    for (j, run) in runs.iter().enumerate() {
        check!(
            run.to_array() == std::array::from_fn(|p| block[8 * p + j]),
            "x8::F128x8 load_runs",
            "run {j}"
        );
    }
    let k = K8::load(k0);
    check!(
        k.to_array() == *k0 && K8::new(*k0).to_array() == *k0,
        "x8::F64x8 load",
        ""
    );
    check!(K8::splat(k0[0]).to_array() == [k0[0]; 8], "x8::F64x8 splat", "");
    check!(
        (k * K8::load(&[k0[7]; 8])).to_array() == std::array::from_fn(|j| F64(r::mul_k(k0[j].0, k0[7].0))),
        "x8::F64x8 mul",
        ""
    );
    let mut m = Mixed8::ZERO;
    m.add(a, k);
    m.add(b, k);
    check!(
        m.reduce().to_array()
            == std::array::from_fn(|j| r::add_e(r::mul_base(x0[j], k0[j].0), r::mul_base(x1[j], k0[j].0))),
        "x8::Mixed8",
        ""
    );
    Ok(())
}

fn g_powers_case(src: &mut Source, ctx: &Ctx) -> Outcome {
    ctx.note("g-powers");
    let i = match src.below(4) {
        0 => src.below(1 << 17),
        1 => (1 << 16) + src.below(3) - 1,
        2 => src.edgy_u64() as u32 as usize,
        _ => src.u32() as usize,
    };
    let want = r::pow_k(2, i as u128);
    check!(g_pow(i).0 == want, "g_pow", "g^{i}");
    check!(g_pow32_by_lookup(i as u32).0 == want, "g_pow32_by_lookup", "g^{i}");
    // `ord(g) = 2^64 - 1`: the exponent wraps there and nowhere before.
    let e = src.u64() as u128;
    check!(
        F64::G.pow(e + u128::from(u64::MAX)) == F64::G.pow(e),
        "F64 pow",
        "g^({e} + 2^64 - 1) != g^{e}"
    );
    let n = match src.below(4) {
        0 => src.below(5),
        1 => (1 << 12) + src.below(3) - 1,
        _ => src.below(20_000),
    };
    let table = g_powers(n);
    check!(table.len() == n, "g_powers", "length {} for {n}", table.len());
    let mut p = 1u64;
    for (k, &got) in table.iter().enumerate() {
        check!(got.0 == p, "g_powers", "entry {k} of {n}");
        p = r::mul_k(p, 2);
    }
    Ok(())
}

fn inverses(src: &mut Source, ctx: &Ctx) -> Outcome {
    ctx.note("inverses");
    let a = edge_k(src);
    let inv = a.inv();
    if a.0 == 0 {
        check!(inv.0 == 0, "F64 inv", "inv(0) = {inv:?}");
    } else {
        check!(r::mul_k(a.0, inv.0) == 1, "F64 inv", "{a:?} * {inv:?} != 1");
    }
    check!(
        inv.0 == r::pow_k(a.0, u128::from(u64::MAX) - 1),
        "F64 inv",
        "{a:?}: not a^(2^64-2)"
    );
    let e = edge_e(src);
    let einv = e.inv();
    if e.is_zero() {
        check!(einv.is_zero(), "F128 inv", "inv(0) = {einv:?}");
    } else {
        check!(r::mul_e(e, einv) == F128::ONE, "F128 inv", "{e:?} * {einv:?} != 1");
    }
    let ve = E::new(e.c0, e.c1).inv();
    check!(
        (ve.c0, ve.c1) == (einv.c0, einv.c1),
        "verifier E inv",
        "{e:?}: verifier {ve:?}, prover {einv:?}"
    );
    check!(K(a.0).inv().0 == inv.0, "verifier K inv", "{a:?}");
    Ok(())
}

fn verifier_field(src: &mut Source, ctx: &Ctx) -> Outcome {
    ctx.note("verifier");
    let (a, b, k) = (edge_e(src), edge_e(src), edge_k(src));
    let (va, vb) = (E::new(a.c0, a.c1), E::new(b.c0, b.c1));
    let lift = |e: E| F128::new(e.c0, e.c1);
    check!(lift(va * vb) == r::mul_e(a, b), "verifier E mul", "{a:?} * {b:?}");
    let mut m = va;
    m *= vb;
    check!(lift(m) == r::mul_e(a, b), "verifier E mul_assign", "{a:?} * {b:?}");
    check!(lift(va + vb) == r::add_e(a, b), "verifier E add", "{a:?} + {b:?}");
    check!(lift(va.square()) == r::mul_e(a, a), "verifier E square", "{a:?}");
    let e = src.edgy_u64();
    check!(
        lift(va.pow(e)) == r::pow_e(a, u128::from(e)),
        "verifier E pow",
        "{a:?}^{e}"
    );
    check!(
        lift(va * K(k.0)) == r::mul_base(a, k.0),
        "verifier E mul K",
        "{a:?} * {k:?}"
    );
    check!(lift(E::from(K(k.0))) == F128::from(k), "verifier E from K", "{k:?}");
    check!(
        (K(a.c0) * K(k.0)).0 == r::mul_k(a.c0, k.0),
        "verifier K mul",
        "{:#x} * {k:?}",
        a.c0
    );
    check!((K(a.c0) + K(k.0)).0 == a.c0 ^ k.0, "verifier K add", "");
    check!(K(k.0).square().0 == r::mul_k(k.0, k.0), "verifier K square", "{k:?}");
    check!(K(k.0).to_bytes() == k.0.to_le_bytes(), "verifier K to_bytes", "{k:?}");
    let mask = src.edgy_u64();
    check!(
        lift(va.masked(mask)) == F128::new(a.c0 & mask, a.c1 & mask),
        "verifier E masked",
        "{a:?} & {mask:#x}"
    );
    let n = src.below(6);
    let xs = bulk_e(src, n);
    let vs: Vec<E> = xs.iter().map(|x| E::new(x.c0, x.c1)).collect();
    check!(
        lift(E::sum(vs)) == xs.iter().fold(F128::ZERO, |s, &x| r::add_e(s, x)),
        "verifier E sum",
        ""
    );
    Ok(())
}

/// Many products XORed unreduced then reduced once, as the sumcheck kernels accumulate, against the sum of reduced
/// products: the unreduced coefficients may not overflow or alias.
fn accumulate(src: &mut Source, ctx: &Ctx) -> Outcome {
    ctx.note("accumulate");
    let n = src.range(1, 64);
    let (xs, ys, ks) = (bulk_e(src, n), bulk_e(src, n), bulk_k(src, n));
    let mut acc = F128Unreduced::ZERO;
    let mut want = F128::ZERO;
    for i in 0..n {
        if src.bool() {
            acc ^= xs[i].mul_unreduced(ys[i]);
            want = r::add_e(want, r::mul_e(xs[i], ys[i]));
        } else {
            acc ^= xs[i].mul_base_unreduced(ks[i]);
            want = r::add_e(want, r::mul_base(xs[i], ks[i].0));
        }
        if src.chance(1, 8) {
            acc ^= F128Unreduced::from(ys[i]);
            want = r::add_e(want, ys[i]);
        }
    }
    check!(acc.reduce() == want, "F128Unreduced accumulation", "{n} terms");
    Ok(())
}
