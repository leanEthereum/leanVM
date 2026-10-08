use leanvm_verus::bits as verified;
use primitives::bits as production;
use primitives::test_util::Rng;

/// Zero, all ones, the diagonal, the anti-diagonal, one row, one column, then random matrices.
fn matrices() -> impl Iterator<Item = [u64; 64]> {
    let edges: [[u64; 64]; 6] = [
        [0; 64],
        [u64::MAX; 64],
        std::array::from_fn(|r| 1 << r),
        std::array::from_fn(|r| 1 << (63 - r)),
        std::array::from_fn(|r| if r == 5 { u64::MAX } else { 0 }),
        [1 << 37; 64],
    ];
    let mut rng = Rng::new(0x6464_7777);
    edges
        .into_iter()
        .chain((0..10_000).map(move |_| std::array::from_fn(|_| rng.next_u64())))
}

#[test]
fn transpose_64x64_matches() {
    for m in matrices() {
        let (mut v, mut p) = (m, m);
        verified::transpose_64x64(&mut v);
        production::transpose_64x64(&mut p);
        assert_eq!(v, p);
    }
}

/// Zero, all ones, one bit per byte, then random blocks.
fn blocks() -> impl Iterator<Item = [u8; 64]> {
    let edges: [[u8; 64]; 4] = [
        [0; 64],
        [0xFF; 64],
        std::array::from_fn(|i| 1 << (i % 8)),
        std::array::from_fn(|i| i as u8),
    ];
    let mut rng = Rng::new(0xB17_7777);
    edges
        .into_iter()
        .chain((0..10_000).map(move |_| std::array::from_fn(|_| rng.next_u8())))
}

/// Production's portable arm is private: the verified copy is compared with the dispatched public function, whichever
/// arm this target compiles.
#[test]
fn bit_transpose_64bytes_matches() {
    for input in blocks() {
        let (mut v, mut p) = ([0u8; 64], [0u8; 64]);
        verified::bit_transpose_64bytes_portable(&input, &mut v);
        production::bit_transpose_64bytes(&input, &mut p);
        assert_eq!(v, p);
    }
}

/// Production's `transpose_8x8_bits` is private: the verified copy is checked against the definition, and against
/// the public 64-byte transpose, whose row `b` is the 8x8 transpose of byte column `b`.
#[test]
fn transpose_8x8_bits_matches() {
    let mut rng = Rng::new(0x88_7777);
    for x in [0, u64::MAX, 1, 1 << 63, 0x8040_2010_0804_0201]
        .into_iter()
        .chain((0..10_000).map(|_| rng.next_u64()))
    {
        let mut want = 0u64;
        for r in 0..8 {
            for c in 0..8 {
                want |= ((x >> (r * 8 + c)) & 1) << (c * 8 + r);
            }
        }
        assert_eq!(verified::transpose_8x8_bits(x), want, "definition {x:#x}");
    }
    for input in blocks() {
        let mut p = [0u8; 64];
        production::bit_transpose_64bytes(&input, &mut p);
        for b in 0..8 {
            let column = u64::from_le_bytes(std::array::from_fn(|x| input[8 * x + b]));
            let row = u64::from_le_bytes(p[8 * b..8 * b + 8].try_into().unwrap());
            assert_eq!(verified::transpose_8x8_bits(column), row, "column {b}");
        }
    }
}

/// The definition, one bit at a time.
fn reference(input: &[u8; 64]) -> [u8; 64] {
    let mut output = [0u8; 64];
    for x in 0..8 {
        for b in 0..8 {
            for t in 0..8 {
                output[b * 8 + t] |= ((input[x * 8 + b] >> t) & 1) << x;
            }
        }
    }
    output
}

/// Every verified arm this build compiles, against the definition and against production's dispatched function
/// (production's arms are private), like production's `every_arm_matches_reference`. Built with
/// `target-cpu=native` on an AVX-512 VBMI and GFNI machine this runs the three x86 arms; under `--target aarch64-*`
/// the NEON one.
#[test]
fn every_arm_matches_reference() {
    for input in blocks() {
        let want = reference(&input);
        let mut p = [0u8; 64];
        production::bit_transpose_64bytes(&input, &mut p);
        assert_eq!(p, want, "production");
        let mut got = [0u8; 64];
        verified::bit_transpose_64bytes(&input, &mut got);
        assert_eq!(got, want, "dispatched");
        verified::bit_transpose_64bytes_portable(&input, &mut got);
        assert_eq!(got, want, "portable");
        #[cfg(all(target_arch = "x86_64", target_feature = "avx512vbmi", target_feature = "gfni"))]
        {
            // SAFETY: compiled only with the features enabled.
            unsafe { verified::bit_transpose_64bytes_gfni(&input, &mut got) };
            assert_eq!(got, want, "gfni");
        }
        #[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "gfni"))]
        {
            // SAFETY: compiled only with the features enabled.
            unsafe { verified::bit_transpose_64bytes_gfni_avx2(&input, &mut got) };
            assert_eq!(got, want, "gfni avx2");
        }
        #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
        {
            // SAFETY: compiled only with the feature enabled.
            unsafe { verified::bit_transpose_64bytes_avx2(&input, &mut got) };
            assert_eq!(got, want, "avx2");
        }
        #[cfg(target_arch = "aarch64")]
        {
            // SAFETY: aarch64 always has NEON.
            unsafe { verified::bit_transpose_64bytes_neon(&input, &mut got) };
            assert_eq!(got, want, "neon");
        }
    }
}
