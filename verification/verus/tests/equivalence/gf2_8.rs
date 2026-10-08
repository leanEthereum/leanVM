use leanvm_verus::gf2_8 as verified;
use primitives::field::gf2_8 as production;

/// Every pair of bytes. Production's `clmul8` / `clmul8_software` are private: the verified `clmul8_software` is
/// checked through production's public `gf8_reduce` against production's `F8` product.
#[test]
fn products_match_exhaustively() {
    for a in 0..=u8::MAX {
        for b in 0..=u8::MAX {
            let want = (production::F8(a) * production::F8(b)).0;
            assert_eq!((verified::F8(a) * verified::F8(b)).0, want, "mul {a:#x} {b:#x}");
            assert_eq!(production::gf8_reduce(verified::clmul8_software(a, b)), want, "clmul8 {a:#x} {b:#x}");
            let (mut v, mut p) = (verified::F8(a), production::F8(a));
            v *= verified::F8(b);
            p *= production::F8(b);
            assert_eq!(v.0, p.0, "mul_assign {a:#x} {b:#x}");
            assert_eq!((verified::F8(a) + verified::F8(b)).0, (production::F8(a) + production::F8(b)).0);
            let (mut v, mut p) = (verified::F8(a), production::F8(a));
            v += verified::F8(b);
            p += production::F8(b);
            assert_eq!(v.0, p.0, "add_assign {a:#x} {b:#x}");
        }
    }
}

/// Every `u16`, including the degree-15 inputs outside the documented `deg <= 14`.
#[test]
fn reduction_matches_on_every_u16() {
    for p in 0..=u16::MAX {
        assert_eq!(verified::gf8_reduce(p), production::gf8_reduce(p), "reduce {p:#x}");
    }
}

#[test]
fn inverses_match_exhaustively() {
    for a in 0..=u8::MAX {
        assert_eq!(verified::F8(a).inv().0, production::F8(a).inv().0, "inv {a:#x}");
    }
}

#[test]
fn constants_match() {
    assert_eq!(verified::F8::ZERO.0, production::F8::ZERO.0);
    assert_eq!(verified::F8::ONE.0, production::F8::ONE.0);
}
