use leanvm_verus::gf2_64 as vk;
use leanvm_verus::gf2_64x3 as verified;
use primitives::field as production;
use primitives::test_util::Rng;

const CORNER_WORDS: [u64; 6] = [0, 1, u64::MAX, 1 << 63, 0xF000_0000_0000_0000, 0x1B];

fn to_v(e: production::F192) -> verified::F192 {
    verified::F192::new(e.c0, e.c1, e.c2)
}

fn same(v: verified::F192, p: production::F192) -> bool {
    (v.c0, v.c1, v.c2) == (p.c0, p.c1, p.c2)
}

/// The unreduced values compared word for word, through their (identical) `Debug` forms: the production
/// fields are private.
fn same_unreduced(v: &verified::F192Unreduced, p: &production::F192Unreduced) -> bool {
    format!("{v:?}") == format!("{p:?}")
}

fn elements(rng: &mut Rng, n: usize) -> Vec<production::F192> {
    let mut out: Vec<production::F192> = (0..n)
        .map(|_| production::F192::new(rng.next_u64(), rng.next_u64(), rng.next_u64()))
        .collect();
    for &a in &CORNER_WORDS {
        for &b in &CORNER_WORDS {
            out.push(production::F192::new(a, b, a ^ b));
            out.push(production::F192::new(a, 0, b));
        }
    }
    out
}

#[test]
fn products_match() {
    let mut rng = Rng::new(0x192);
    let xs = elements(&mut rng, 20_000);
    let ys = elements(&mut rng, 20_000);
    for (&a, &b) in xs.iter().zip(&ys) {
        let (va, vb) = (to_v(a), to_v(b));
        assert!(same(va * vb, a * b), "mul {a:?} {b:?}");
        assert!(same(
            verified::software::mul(va, vb),
            production::gf2_64x3::software::mul(a, b)
        ));
        assert!(
            same_unreduced(&va.mul_unreduced(vb), &a.mul_unreduced(b)),
            "mul_unreduced {a:?} {b:?}"
        );
        assert!(same_unreduced(
            &verified::software::mul_unreduced(va, vb),
            &production::gf2_64x3::software::mul_unreduced(a, b)
        ));
        assert!(same(va.square(), a.square()), "square {a:?}");
        assert!(same(va.frobenius(), a.frobenius()));
        assert!(same(va + vb, a + b));
        let k = b.c1;
        assert!(
            same(va.mul_base(vk::F64(k)), a.mul_base(production::F64(k))),
            "mul_base {a:?} {k:#x}"
        );
        assert!(same_unreduced(
            &va.mul_base_unreduced(vk::F64(k)),
            &a.mul_base_unreduced(production::F64(k))
        ));
        assert!(same(
            verified::F192::from(vk::F64(k)),
            production::F192::from(production::F64(k))
        ));
        assert!(same_unreduced(
            &verified::F192Unreduced::from(va),
            &production::F192Unreduced::from(a)
        ));
        let (mut sv, mut sp) = (va, a);
        sv += vb;
        sp += b;
        assert!(same(sv, sp));
        sv *= vb;
        sp *= b;
        assert!(same(sv, sp));
    }
}

#[test]
fn lazy_reduction_matches() {
    let mut rng = Rng::new(0x1A2);
    let xs = elements(&mut rng, 4_000);
    let mut acc_v = verified::F192Unreduced::ZERO;
    let mut acc_p = production::F192Unreduced::ZERO;
    for w in xs.windows(2) {
        let (a, b) = (w[0], w[1]);
        acc_v ^= to_v(a).mul_unreduced(to_v(b));
        acc_p ^= a.mul_unreduced(b);
        acc_v = acc_v ^ to_v(b).mul_base_unreduced(vk::F64(a.c2));
        acc_p = acc_p ^ b.mul_base_unreduced(production::F64(a.c2));
        assert!(same_unreduced(&acc_v, &acc_p));
        assert!(same(acc_v.reduce(), acc_p.reduce()));
    }
}

#[test]
fn batched_products_match() {
    let mut rng = Rng::new(0x48);
    let xs = elements(&mut rng, 4_000);
    for c in xs.chunks_exact(8) {
        let a: [production::F192; 4] = [c[0], c[1], c[2], c[3]];
        let b: [production::F192; 4] = [c[4], c[5], c[6], c[7]];
        let (va, vb) = (a.map(to_v), b.map(to_v));
        let (r2v, r2p) = (
            verified::mul2([va[0], va[1]], [vb[0], vb[1]]),
            production::mul2([a[0], a[1]], [b[0], b[1]]),
        );
        assert!(r2v.iter().zip(&r2p).all(|(&v, &p)| same(v, p)));
        let (r4v, r4p) = (verified::mul4(va, vb), production::mul4(a, b));
        assert!(r4v.iter().zip(&r4p).all(|(&v, &p)| same(v, p)));
        let (u4v, u4p) = (verified::mul_unreduced4(va, vb), production::mul_unreduced4(a, b));
        assert!(u4v.iter().zip(&u4p).all(|(v, p)| same_unreduced(v, p)));
        let ks: [u64; 8] = std::array::from_fn(|i| c[i].c0 ^ c[i].c2);
        let (m8v, m8p) = (
            verified::mul_base8(va[0], ks.map(vk::F64)),
            production::mul_base8(a[0], ks.map(production::F64)),
        );
        assert!(m8v.iter().zip(&m8p).all(|(&v, &p)| same(v, p)));
    }
}

#[test]
fn weights_and_dot_base_match() {
    let mut rng = Rng::new(0xD07);
    for len in [0usize, 1, 2, 5, 16] {
        let ws = elements(&mut rng, 8 * len);
        let ws = &ws[..8 * len];
        let ks: Vec<u64> = (0..8 * len).map(|_| rng.next_u64()).collect();
        let packed_v: Vec<verified::Weights8> = ws
            .chunks_exact(8)
            .map(|c| verified::Weights8::new(&std::array::from_fn(|i| to_v(c[i]))))
            .collect();
        let packed_p: Vec<production::Weights8> = ws
            .chunks_exact(8)
            .map(|c| production::Weights8::new(&std::array::from_fn(|i| c[i])))
            .collect();
        for (v, p) in packed_v.iter().zip(&packed_p) {
            for i in 0..8 {
                assert!(same(v.get(i), p.get(i)));
            }
        }
        let kv: Vec<vk::F64> = ks.iter().map(|&k| vk::F64(k)).collect();
        let kp: Vec<production::F64> = ks.iter().map(|&k| production::F64(k)).collect();
        let (dv, dp) = (verified::dot_base(&packed_v, &kv), production::dot_base(&packed_p, &kp));
        assert!(same_unreduced(&dv, &dp), "dot_base, len {len}");
    }
}

#[test]
fn inverses_match() {
    let mut rng = Rng::new(0x1A7);
    for a in elements(&mut rng, 1_000) {
        assert!(same(to_v(a).inv(), a.inv()), "inv {a:?}");
    }
}

#[test]
fn constants_match() {
    assert!(same(verified::F192::ZERO, production::F192::ZERO));
    assert!(same(verified::F192::ONE, production::F192::ONE));
    assert!(same(verified::F192::Y, production::F192::Y));
    assert!(same_unreduced(
        &verified::F192Unreduced::ZERO,
        &production::F192Unreduced::ZERO
    ));
}

#[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
#[test]
fn x86_register_products_and_memory_match() {
    use core::mem::MaybeUninit;
    use production::gf2_64x3::x86_64 as p;
    use verified::x86_64 as v;
    let mut rng = Rng::new(0x192_01);
    let xs = elements(&mut rng, 4096);
    let mut va = v::F192x1Unreduced::zero();
    let mut pa = p::F192x1Unreduced::zero();
    for pair in xs.windows(2) {
        let (a, b) = (pair[0], pair[1]);
        let (vx, vy) = (v::F192x1::load(&to_v(a)), v::F192x1::new(to_v(b)));
        let (px, py) = (p::F192x1::load(&a), p::F192x1::new(b));
        assert!(same(verified::F192::from(vx), a));
        assert!(same(verified::F192::from(vx + vy), production::F192::from(px + py)));
        assert!(same(verified::F192::from(vx * vy), production::F192::from(px * py)));
        let (vu, pu) = (vx.mul_unreduced(vy), px.mul_unreduced(py));
        assert!(same_unreduced(&vu.into(), &pu.into()));
        va ^= vu;
        pa ^= pu;
        va = va ^ vx.mul_base_unreduced(vk::F64(b.c2));
        pa = pa ^ px.mul_base_unreduced(production::F64(b.c2));
        assert!(same_unreduced(&va.into(), &pa.into()));
        let (mut vo, mut po) = (MaybeUninit::uninit(), MaybeUninit::uninit());
        va.reduce().store(&mut vo);
        pa.reduce().store(&mut po);
        assert!(same(unsafe { vo.assume_init() }, unsafe { po.assume_init() }));
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
#[test]
fn x86_lane_wrappers_transpose_and_accumulation_match() {
    use core::mem::MaybeUninit;
    let mut rng = Rng::new(0x192_04);
    let xs = elements(&mut rng, 4096);
    let (mut vu, mut pu) = (verified::F192x4Unreduced::zero(), production::F192x4Unreduced::zero());
    let (mut vs, mut ps) = (verified::MixedSums8::default(), production::MixedSums8::default());
    for c in xs.chunks_exact(16) {
        let rows: [[production::F192; 4]; 4] = std::array::from_fn(|i| std::array::from_fn(|j| c[4 * i + j]));
        let vr = rows.map(|row| verified::F192x4::load(&row.map(to_v)));
        let pr = rows.map(|row| production::F192x4::load(&row));
        let (vt, pt) = (verified::F192x4::transpose(vr), production::F192x4::transpose(pr));
        for i in 0..4 {
            let (v, p) = (vt[i].to_array(), pt[i].to_array());
            for j in 0..4 {
                assert!(same(v[j], p[j]));
                assert_eq!(p[j], rows[j][i]);
            }
        }
        let (v, p) = (
            verified::F192x4::new(rows[0].map(to_v)),
            production::F192x4::new(rows[0]),
        );
        let (vb, pb) = (verified::F192x4::splat(to_v(c[7])), production::F192x4::splat(c[7]));
        for (v, p) in [(v + vb, p + pb), (v * vb, p * pb)] {
            let mut vo = [MaybeUninit::uninit(); 4];
            let mut po = [MaybeUninit::uninit(); 4];
            v.store(&mut vo);
            p.store(&mut po);
            for i in 0..4 {
                assert!(same(unsafe { vo[i].assume_init() }, unsafe { po[i].assume_init() }));
            }
        }
        vu ^= v.mul_unreduced(vb);
        pu ^= p.mul_unreduced(pb);
        vu = vu ^ vr[1].mul_unreduced(vr[2]);
        pu = pu ^ pr[1].mul_unreduced(pr[2]);
        assert!(same_unreduced(&vu.sum(), &pu.sum()));
        for (v, p) in vu.reduce().to_array().into_iter().zip(pu.reduce().to_array()) {
            assert!(same(v, p));
        }
        let k: [u64; 8] = std::array::from_fn(|i| c[i].c1);
        vs.add(to_v(c[0]), k.map(vk::F64));
        ps.add(c[0], k.map(production::F64));
        for (v, p) in vs.reduce().into_iter().zip(ps.reduce()) {
            assert!(same(v, p));
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
#[test]
fn x86_arbitrary_wide_reductions_match() {
    use core::arch::x86_64::*;
    use core::mem::{transmute, MaybeUninit};
    use production::gf2_64x3::x86_64 as p;
    use verified::x86_64 as v;
    let mut rng = Rng::new(0x192_ffff);
    for n in 0..512 {
        let words: [[[u64; 2]; 3]; 4] = std::array::from_fn(|i| {
            std::array::from_fn(|j| {
                std::array::from_fn(|k| {
                    if n < 6 {
                        CORNER_WORDS[(n + i + j + k) % 6]
                    } else {
                        rng.next_u64()
                    }
                })
            })
        });
        #[cfg(target_feature = "avx512f")]
        let d: v::Wide4 = std::array::from_fn(|c| unsafe {
            transmute::<[u64; 8], __m512i>(std::array::from_fn(|j| words[j / 2][c][j % 2]))
        });
        #[cfg(not(target_feature = "avx512f"))]
        let d: v::Wide4 = std::array::from_fn(|h| {
            std::array::from_fn(|c| unsafe {
                transmute::<[u64; 4], __m256i>(std::array::from_fn(|j| words[2 * h + j / 2][c][j % 2]))
            })
        });
        unsafe {
            let mut vo = [MaybeUninit::uninit(); 4];
            let mut po = [MaybeUninit::uninit(); 4];
            v::store_lanes4(v::reduce_lanes4(d), &mut vo);
            p::store_lanes4(p::reduce_lanes4(d), &mut po);
            for i in 0..4 {
                let expected = verified::F192Unreduced { coeffs: words[i] }.reduce();
                assert_eq!(vo[i].assume_init(), expected);
                assert!(same(expected, po[i].assume_init()));
            }
            assert!(same_unreduced(&v::sum_lanes4(d), &p::sum_lanes4(d)));
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[test]
fn x86_planar_products_and_sums_match() {
    use core::arch::x86_64::__m512i;
    use core::mem::transmute;
    use production::gf2_64x3::x86_64 as p;
    use verified::x86_64 as v;
    let mut rng = Rng::new(0x192_08);
    let xs = elements(&mut rng, 4096);
    // SAFETY: this test is compiled only with both required target features.
    let (mut vs, mut ps) = unsafe { (v::F192x8Sum::zero(), p::F192x8Sum::zero()) };
    let mut expected = production::F192::ZERO;
    for c in xs.chunks_exact(16) {
        let pack = |slice: &[production::F192]| -> [__m512i; 3] {
            std::array::from_fn(|k| unsafe {
                transmute::<[u64; 8], __m512i>(std::array::from_fn(|i| [slice[i].c0, slice[i].c1, slice[i].c2][k]))
            })
        };
        let (a, b) = (pack(&c[..8]), pack(&c[8..]));
        let results = unsafe {
            [
                (v::F192x8(a).add(v::F192x8(b)), p::F192x8(a).add(p::F192x8(b)), false),
                (v::F192x8(a).mul(v::F192x8(b)), p::F192x8(a).mul(p::F192x8(b)), true),
            ]
        };
        for (vr, pr, mul) in results {
            let vw: [[u64; 8]; 3] = vr.0.map(|v| unsafe { transmute(v) });
            let pw: [[u64; 8]; 3] = pr.0.map(|v| unsafe { transmute(v) });
            assert_eq!(vw, pw);
            for i in 0..8 {
                let e = if mul {
                    production::gf2_64x3::software::mul(c[i], c[8 + i])
                } else {
                    c[i] + c[8 + i]
                };
                assert_eq!([vw[0][i], vw[1][i], vw[2][i]], [e.c0, e.c1, e.c2]);
            }
        }
        unsafe {
            vs.mul_add(v::F192x8(a), v::F192x8(b));
            ps.mul_add(p::F192x8(a), p::F192x8(b));
        }
        for i in 0..8 {
            expected += production::gf2_64x3::software::mul(c[i], c[8 + i]);
        }
        let (vt, pt) = unsafe { (vs.total(), ps.total()) };
        assert!(same_unreduced(&vt, &pt));
        assert!(same(vt.reduce(), expected));
    }
}

/// The aarch64 kernels, each against production's, and the register-resident `F192x1` / `F192x1Unreduced`
/// (whose fields are private on both sides) through their conversions to `F192` and `F192Unreduced`.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[test]
fn aarch64_kernels_match() {
    use core::mem::MaybeUninit;
    use production::gf2_64x3::aarch64 as pa;
    use verified::aarch64 as va;
    let mut rng = Rng::new(0xA192);
    let xs = elements(&mut rng, 10_000);
    let ys = elements(&mut rng, 10_000);
    let mut acc_v = va::F192x1Unreduced::zero();
    let mut acc_p = pa::F192x1Unreduced::zero();
    assert!(same_unreduced(
        &verified::F192Unreduced::from(acc_v),
        &production::F192Unreduced::from(acc_p)
    ));
    for (&a, &b) in xs.iter().zip(&ys) {
        let (vx, vy) = (to_v(a), to_v(b));
        let k = a.c2 ^ b.c0;
        assert!(same(va::mul(vx, vy), pa::mul(a, b)), "mul {a:?} {b:?}");
        assert!(
            same_unreduced(&va::mul_unreduced(vx, vy), &pa::mul_unreduced(a, b)),
            "mul_unreduced {a:?} {b:?}"
        );
        assert!(same(va::mul_base(vx, vk::F64(k)), pa::mul_base(a, production::F64(k))));
        assert!(same_unreduced(
            &va::mul_base_unreduced(vx, vk::F64(k)),
            &pa::mul_base_unreduced(a, production::F64(k))
        ));
        assert!(same(va::square(vx), pa::square(a)), "square {a:?}");
        // An unreduced sum, as an accumulator holds (production's fields and `from_wide` are private).
        let u = va::mul_unreduced(vx, vy) ^ verified::F192Unreduced::from(vy);
        let up = pa::mul_unreduced(a, b) ^ production::F192Unreduced::from(b);
        assert!(same_unreduced(&u, &up));
        assert!(same(va::reduce(u), pa::reduce(up)), "reduce {u:?}");
        // Registers.
        let (x1, y1) = (va::F192x1::load(&vx), va::F192x1::new(vy));
        let (px1, py1) = (pa::F192x1::load(&a), pa::F192x1::new(b));
        assert!(same(verified::F192::from(x1), production::F192::from(px1)));
        assert!(same(verified::F192::from(x1 + y1), production::F192::from(px1 + py1)));
        assert!(same(verified::F192::from(x1 * y1), production::F192::from(px1 * py1)));
        let (mut out_v, mut out_p) = (MaybeUninit::uninit(), MaybeUninit::uninit());
        (x1 * y1).store(&mut out_v);
        (px1 * py1).store(&mut out_p);
        assert!(
            same(unsafe { out_v.assume_init() }, unsafe { out_p.assume_init() }),
            "store"
        );
        let (pv, pp) = (x1.mul_unreduced(y1), px1.mul_unreduced(py1));
        let (bv, bp) = (
            y1.mul_base_unreduced(vk::F64(k)),
            py1.mul_base_unreduced(production::F64(k)),
        );
        assert!(same_unreduced(
            &verified::F192Unreduced::from(pv ^ bv),
            &production::F192Unreduced::from(pp ^ bp)
        ));
        assert!(same(
            verified::F192::from((pv ^ bv).reduce()),
            production::F192::from((pp ^ bp).reduce())
        ));
        acc_v ^= pv;
        acc_v ^= bv;
        acc_p ^= pp;
        acc_p ^= bp;
        assert!(same_unreduced(
            &verified::F192Unreduced::from(acc_v),
            &production::F192Unreduced::from(acc_p)
        ));
        assert!(same(
            verified::F192::from(acc_v.reduce()),
            production::F192::from(acc_p.reduce())
        ));
    }
}
