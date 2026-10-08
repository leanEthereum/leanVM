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
            assert_eq!(
                production::gf8_reduce(verified::clmul8_software(a, b)),
                want,
                "clmul8 {a:#x} {b:#x}"
            );
            let (mut v, mut p) = (verified::F8(a), production::F8(a));
            v *= verified::F8(b);
            p *= production::F8(b);
            assert_eq!(v.0, p.0, "mul_assign {a:#x} {b:#x}");
            assert_eq!(
                (verified::F8(a) + verified::F8(b)).0,
                (production::F8(a) + production::F8(b)).0
            );
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

/// `clmul8_neon` (production's is private) against the verified portable `clmul8_software`, which the test above
/// ties to production, and through production's `gf8_reduce` against production's product, which dispatches to
/// production's `clmul8_neon` in this build.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[test]
fn clmul8_neon_matches_exhaustively() {
    for a in 0..=u8::MAX {
        for b in 0..=u8::MAX {
            let got = unsafe { verified::clmul8_neon(a, b) };
            assert_eq!(got, verified::clmul8_software(a, b), "clmul8_neon {a:#x} {b:#x}");
            assert_eq!(verified::clmul8(a, b), got);
            assert_eq!(production::gf8_reduce(got), (production::F8(a) * production::F8(b)).0);
        }
    }
}

/// The NEON reduction on every 16-bit polynomial lane, and the NEON product on every pair of bytes.
#[cfg(target_arch = "aarch64")]
#[test]
fn neon_helpers_match_exhaustively() {
    use core::arch::aarch64::uint8x16_t;
    use core::mem::transmute;
    let b16 = |v: uint8x16_t| unsafe { transmute::<uint8x16_t, [u8; 16]>(v) };
    for first in (0..=u16::MAX).step_by(16) {
        let p: [u16; 16] = std::array::from_fn(|i| first + i as u16);
        let (lo, hi): ([u16; 8], [u16; 8]) = (p[..8].try_into().unwrap(), p[8..].try_into().unwrap());
        let (c0, c1) = unsafe {
            (
                transmute::<[u16; 8], uint8x16_t>(lo),
                transmute::<[u16; 8], uint8x16_t>(hi),
            )
        };
        let (v, q) = unsafe {
            (
                b16(verified::neon::gf8_reduce_vec16(c0, c1)),
                b16(production::neon::gf8_reduce_vec16(c0, c1)),
            )
        };
        assert_eq!(v, q, "gf8_reduce_vec16 first={first:#06x}");
    }
    for b in 0..=u8::MAX {
        for a0 in (0..=u8::MAX).step_by(16) {
            let a: [u8; 16] = std::array::from_fn(|i| a0.wrapping_add(i as u8));
            let bs: [u8; 16] = std::array::from_fn(|i| b.wrapping_add((i as u8).wrapping_mul(17)));
            let (va, vb) = unsafe {
                (
                    transmute::<[u8; 16], uint8x16_t>(a),
                    transmute::<[u8; 16], uint8x16_t>(bs),
                )
            };
            let (v, q) = unsafe {
                (
                    b16(verified::neon::gf8_mul_vec16(va, vb)),
                    b16(production::neon::gf8_mul_vec16(va, vb)),
                )
            };
            assert_eq!(v, q, "gf8_mul_vec16 a={a:x?} b={bs:x?}");
        }
    }
}

/// The AVX2 product on every pair of bytes (built with AVX2, like production's `avx2` module).
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[test]
fn avx2_gf8_mul_vec32_matches_exhaustively() {
    use core::arch::x86_64::__m256i;
    use core::mem::transmute;
    for b in 0..=u8::MAX {
        for a0 in (0..256usize).step_by(32) {
            let a: [u8; 32] = std::array::from_fn(|i| (a0 + i) as u8);
            let bs: [u8; 32] = std::array::from_fn(|i| b.wrapping_add((i as u8).wrapping_mul(9)));
            let (va, vb) = unsafe { (transmute::<[u8; 32], __m256i>(a), transmute::<[u8; 32], __m256i>(bs)) };
            let (v, q) = unsafe {
                (
                    transmute::<__m256i, [u8; 32]>(verified::avx2::gf8_mul_vec32(va, vb)),
                    transmute::<__m256i, [u8; 32]>(production::avx2::gf8_mul_vec32(va, vb)),
                )
            };
            assert_eq!(v, q, "gf8_mul_vec32 a={a:x?} b={bs:x?}");
        }
    }
}
