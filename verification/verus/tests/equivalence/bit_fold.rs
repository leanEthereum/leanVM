//! The portable `Imp` is private and compiled only without AVX2; it is reached through `BitFold`, `F192Map` and
//! `Sliced`, which on this machine dispatch to the arm the target enables (AVX-512 with GFNI, AVX2, or portable).
use leanvm_verus::bit_fold as verified;
use leanvm_verus::gf2_64x3 as vx;
use primitives::bit_fold as production;
use primitives::field::F192;
use primitives::test_util::Rng;

const BLOCK: usize = production::BLOCK;

fn to_v(e: F192) -> vx::F192 {
    vx::F192::new(e.c0, e.c1, e.c2)
}

fn same(v: vx::F192, p: F192) -> bool {
    (v.c0, v.c1, v.c2) == (p.c0, p.c1, p.c2)
}

/// Random weights, then the edge cases: all zero, all ones, one coordinate bit each.
fn weight_sets(rng: &mut Rng, n: usize, random: usize) -> Vec<Vec<F192>> {
    let mut sets: Vec<Vec<F192>> = (0..random).map(|_| rng.ext_vec(n)).collect();
    sets.push(vec![F192::ZERO; n]);
    sets.push(vec![F192::new(u64::MAX, u64::MAX, u64::MAX); n]);
    sets.push(
        (0..n)
            .map(|b| {
                let mut w = [0u64; 3];
                w[(b / 64) % 3] = 1 << (b % 64);
                F192::new(w[0], w[1], w[2])
            })
            .collect(),
    );
    sets
}

fn check_fold<const CHUNKS: usize>(rng: &mut Rng) {
    assert_eq!(verified::BLOCK, BLOCK);
    for weights in weight_sets(rng, 8 * CHUNKS, 20) {
        let vw: Vec<vx::F192> = weights.iter().map(|&w| to_v(w)).collect();
        let (fv, fp) = (verified::BitFold::new(&vw), production::BitFold::new(&weights));
        assert_eq!(fv.n_chunks(), fp.n_chunks());
        for len in [BLOCK, BLOCK, 5, 1, 0] {
            let mut rows: Vec<[u8; CHUNKS]> = (0..len).map(|_| std::array::from_fn(|_| rng.next_u8())).collect();
            // Edge rows: all clear, all set, one set bit.
            if len == BLOCK {
                rows[0] = [0; CHUNKS];
                rows[1] = [0xFF; CHUNKS];
                rows[2] = std::array::from_fn(|j| if j == CHUNKS - 1 { 0x80 } else { 0 });
            }
            // Only `out[..rows.len()]` is specified: past it the portable arm keeps what `out` held and the SIMD
            // arms store the fold of a zero row.
            let before: [F192; BLOCK] = std::array::from_fn(|_| rng.ext());
            let (mut ov, mut op) = (before.map(to_v), before);
            fv.fold_block(&rows, &mut ov);
            fp.fold_block(&rows, &mut op);
            for p in 0..len {
                assert!(same(ov[p], op[p]), "CHUNKS={CHUNKS}, len={len}, row {p}");
            }
            assert!(ov[len..].iter().zip(&before[len..]).all(|(&v, &b)| same(v, b)));
        }
    }
}

#[test]
fn fold_block_matches() {
    let mut rng = Rng::new(0xB17_F01D_0E);
    check_fold::<8>(&mut rng);
    check_fold::<16>(&mut rng);
    check_fold::<32>(&mut rng);
    check_fold::<64>(&mut rng);
    check_fold::<128>(&mut rng);
}

/// Random values, then zero, all ones and every coordinate vector.
fn blocks(rng: &mut Rng) -> Vec<[F192; BLOCK]> {
    let mut out: Vec<[F192; BLOCK]> = (0..4).map(|_| std::array::from_fn(|_| rng.ext())).collect();
    let mut edge = [F192::ZERO; BLOCK];
    edge[1] = F192::new(u64::MAX, u64::MAX, u64::MAX);
    edge[2] = F192::new(1, 0, 1 << 63);
    out.push(edge);
    for chunk in 0..3 {
        out.push(std::array::from_fn(|i| {
            let b = BLOCK * chunk + i;
            let mut w = [0u64; 3];
            w[b / 64] = 1 << (b % 64);
            F192::new(w[0], w[1], w[2])
        }));
    }
    out
}

#[test]
fn f192_map_matches() {
    let mut rng = Rng::new(0x0F19_23A9_0E);
    for weights in weight_sets(&mut rng, 192, 20) {
        let vw: Vec<vx::F192> = weights.iter().map(|&w| to_v(w)).collect();
        let (mv, mp) = (verified::F192Map::new(&vw), production::F192Map::new(&weights));
        let c = rng.ext();
        let (cv, cp) = (mv.after_mul(to_v(c)), mp.after_mul(c));
        for xs in blocks(&mut rng) {
            let xv = xs.map(to_v);
            let (sv, sp) = (verified::Sliced::new(&xv), production::Sliced::new(&xs));
            for len in [BLOCK, 7, 1, 0] {
                let before: Vec<F192> = (0..len).map(|_| rng.ext()).collect();
                let mut ov: Vec<vx::F192> = before.iter().map(|&b| to_v(b)).collect();
                let mut op = before.clone();
                mv.apply_add(&xv, &mut ov);
                mp.apply_add(&xs, &mut op);
                assert!(ov.iter().zip(&op).all(|(&v, &p)| same(v, p)), "apply_add, len={len}");

                let mut ov: Vec<vx::F192> = before.iter().map(|&b| to_v(b)).collect();
                let mut op = before.clone();
                mv.apply_sliced_add(&sv, &mut ov);
                mp.apply_sliced_add(&sp, &mut op);
                assert!(
                    ov.iter().zip(&op).all(|(&v, &p)| same(v, p)),
                    "apply_sliced_add, len={len}"
                );

                let mut ov: Vec<vx::F192> = before.iter().map(|&b| to_v(b)).collect();
                let mut op = before.clone();
                cv.apply_sliced_add(&sv, &mut ov);
                cp.apply_sliced_add(&sp, &mut op);
                assert!(ov.iter().zip(&op).all(|(&v, &p)| same(v, p)), "after_mul, len={len}");
            }
        }
    }
}
