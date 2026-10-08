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
    let mut out: Vec<production::F192> =
        (0..n).map(|_| production::F192::new(rng.next_u64(), rng.next_u64(), rng.next_u64())).collect();
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
        assert!(same(verified::software::mul(va, vb), production::gf2_64x3::software::mul(a, b)));
        assert!(same_unreduced(&va.mul_unreduced(vb), &a.mul_unreduced(b)), "mul_unreduced {a:?} {b:?}");
        assert!(same_unreduced(
            &verified::software::mul_unreduced(va, vb),
            &production::gf2_64x3::software::mul_unreduced(a, b)
        ));
        assert!(same(va.square(), a.square()), "square {a:?}");
        assert!(same(va.frobenius(), a.frobenius()));
        assert!(same(va + vb, a + b));
        let k = b.c1;
        assert!(same(va.mul_base(vk::F64(k)), a.mul_base(production::F64(k))), "mul_base {a:?} {k:#x}");
        assert!(same_unreduced(
            &va.mul_base_unreduced(vk::F64(k)),
            &a.mul_base_unreduced(production::F64(k))
        ));
        assert!(same(verified::F192::from(vk::F64(k)), production::F192::from(production::F64(k))));
        assert!(same_unreduced(&verified::F192Unreduced::from(va), &production::F192Unreduced::from(a)));
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
        let (r2v, r2p) = (verified::mul2([va[0], va[1]], [vb[0], vb[1]]), production::mul2([a[0], a[1]], [b[0], b[1]]));
        assert!(r2v.iter().zip(&r2p).all(|(&v, &p)| same(v, p)));
        let (r4v, r4p) = (verified::mul4(va, vb), production::mul4(a, b));
        assert!(r4v.iter().zip(&r4p).all(|(&v, &p)| same(v, p)));
        let (u4v, u4p) = (verified::mul_unreduced4(va, vb), production::mul_unreduced4(a, b));
        assert!(u4v.iter().zip(&u4p).all(|(v, p)| same_unreduced(v, p)));
        let ks: [u64; 8] = std::array::from_fn(|i| c[i].c0 ^ c[i].c2);
        let (m8v, m8p) = (verified::mul_base8(va[0], ks.map(vk::F64)), production::mul_base8(a[0], ks.map(production::F64)));
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
        let packed_v: Vec<verified::Weights8> =
            ws.chunks_exact(8).map(|c| verified::Weights8::new(&std::array::from_fn(|i| to_v(c[i])))).collect();
        let packed_p: Vec<production::Weights8> =
            ws.chunks_exact(8).map(|c| production::Weights8::new(&std::array::from_fn(|i| c[i]))).collect();
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
    assert!(same_unreduced(&verified::F192Unreduced::ZERO, &production::F192Unreduced::ZERO));
}
