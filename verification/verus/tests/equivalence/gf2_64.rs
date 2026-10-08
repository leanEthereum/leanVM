use leanvm_verus::gf2_64 as verified;
use primitives::field::gf2_64 as production;
use primitives::test_util::Rng;

/// Operands that exercise the reduction's spill and the identities.
const CORNERS: [u64; 9] = [0, 1, 2, u64::MAX, 1 << 63, 0xF000_0000_0000_0000, 0x1B, 0x8000_0000_0000_001B, 0x5555_5555_5555_5555];

fn pairs() -> impl Iterator<Item = (u64, u64)> {
    let mut rng = Rng::new(0x6464_6464);
    let random: Vec<(u64, u64)> = (0..100_000).map(|_| (rng.next_u64(), rng.next_u64())).collect();
    let corners = CORNERS.iter().flat_map(|&a| CORNERS.iter().map(move |&b| (a, b)));
    random.into_iter().chain(corners)
}

#[test]
fn products_and_reduction_match() {
    for (a, b) in pairs() {
        assert_eq!(verified::software::clmul(a, b), production::software::clmul(a, b), "clmul {a:#x} {b:#x}");
        assert_eq!(verified::mul_wide(a, b), production::mul_wide(a, b), "mul_wide {a:#x} {b:#x}");
        assert_eq!(verified::square_wide(a), production::square_wide(a), "square_wide {a:#x}");
        let wide = (u128::from(a) << 64) | u128::from(b);
        assert_eq!(verified::reduce(wide), production::reduce(wide), "reduce {wide:#x}");
        let p = verified::software::clmul(a, b);
        assert_eq!(verified::reduce(p), production::reduce(p), "reduce {p:#x}");
        assert_eq!(
            (verified::F64(a) * verified::F64(b)).0,
            (production::F64(a) * production::F64(b)).0,
            "mul {a:#x} {b:#x}"
        );
        assert_eq!((verified::F64(a) + verified::F64(b)).0, (production::F64(a) + production::F64(b)).0);
        assert_eq!(verified::F64(a).square().0, production::F64(a).square().0, "square {a:#x}");
    }
}

#[test]
fn inverses_match() {
    let mut rng = Rng::new(0x1A7);
    for a in (0..2_000).map(|_| rng.next_u64()).chain(CORNERS) {
        assert_eq!(verified::F64(a).inv().0, production::F64(a).inv().0, "inv {a:#x}");
    }
}

#[test]
fn constants_match() {
    assert_eq!(verified::R64, production::R64);
    assert_eq!(verified::F64::DEGREE, production::F64::DEGREE);
    assert_eq!(verified::F64::ZERO.0, production::F64::ZERO.0);
    assert_eq!(verified::F64::ONE.0, production::F64::ONE.0);
    assert_eq!(verified::F64::G.0, production::F64::G.0);
}
