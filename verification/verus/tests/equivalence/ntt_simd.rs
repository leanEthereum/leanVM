//! The verified SIMD butterfly kernels and `lane_butterflies` against production.
//!
//! Production's kernels and `lane_butterflies` are private. Each verified kernel is run on random and edge rows,
//! offsets and twiddles (0, 1, all ones, ...) and compared with production's butterfly in the production field
//! (`u' = u + v t, v' = v + u'`; transposed `s = u + v, u' = s, v' = v + s t`), in both directions; production's
//! own kernels are reached through `encode_interleaved_in_place`, whose row pairs of 8 or more lanes go through
//! them, and which a layer-by-layer driver built from the verified `butterfly_lanes` must reproduce. Each test
//! runs the arm its build compiles: natively, with the AVX2 flags, and under qemu for NEON.
use leanvm_verus::gf2_64::F64 as VF64;
use leanvm_verus::ntt as verified;
use pcs::ntt::AdditiveNttF64 as Production;
use primitives::field::F64;
use primitives::test_util::Rng;

/// Edge words: zero, one, all ones, the top bit, the reduction constant, alternating bits, every top nibble.
const EDGES: [u64; 10] = [
    0,
    1,
    u64::MAX,
    1 << 63,
    0x1B,
    0x5555_5555_5555_5555,
    0xAAAA_AAAA_AAAA_AAAA,
    0xF << 60,
    0x7 << 60,
    1 << 60,
];

/// Twiddles: the edge ones first (0, 1, all ones, ...), then random.
fn twiddles(rng: &mut Rng) -> Vec<u64> {
    let mut t = EDGES.to_vec();
    t.extend((0..40).map(|_| rng.next_u64()));
    t
}

/// Rows of `n` words: edge words cycled from `k`, or random.
fn row(rng: &mut Rng, n: usize, k: usize) -> Vec<u64> {
    if k % 3 == 0 {
        (0..n).map(|i| EDGES[(k / 3 + i * (k % 7 + 1)) % EDGES.len()]).collect()
    } else {
        (0..n).map(|_| rng.next_u64()).collect()
    }
}

/// Production's butterfly of one lane, in the production field.
fn production_butterfly(transposed: bool, u: u64, v: u64, t: u64) -> (u64, u64) {
    let (u, v, t) = (F64(u), F64(v), F64(t));
    if transposed {
        let s = u + v;
        (s.0, (v + s * t).0)
    } else {
        let nu = u + v * t;
        (nu.0, (v + nu).0)
    }
}

/// Runs `kernel` on `width` words at every offset of `n`-word rows, and checks every word: production's butterfly
/// on `at .. at + width`, unchanged elsewhere.
fn check_kernel(name: &str, width: usize, transposed: bool, kernel: impl Fn(&mut [VF64], &mut [VF64], usize, u64)) {
    let mut rng = Rng::new(0x5_1AD + width as u64 + u64::from(transposed));
    let n = width + 5;
    for (k, t) in twiddles(&mut rng).into_iter().enumerate() {
        for rep in 0..30 {
            let (u, v) = (row(&mut rng, n, k + rep), row(&mut rng, n, k + 2 * rep + 1));
            for at in 0..=n - width {
                let mut top: Vec<VF64> = u.iter().map(|&x| VF64(x)).collect();
                let mut bot: Vec<VF64> = v.iter().map(|&x| VF64(x)).collect();
                kernel(&mut top, &mut bot, at, t);
                for j in 0..n {
                    let want = if (at..at + width).contains(&j) {
                        production_butterfly(transposed, u[j], v[j], t)
                    } else {
                        (u[j], v[j])
                    };
                    assert_eq!(
                        (top[j].0, bot[j].0),
                        want,
                        "{name} transposed={transposed} t={t:#x} at={at} word {j}"
                    );
                }
            }
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[test]
fn avx512_kernel_matches_production_butterfly() {
    use leanvm_verus::ntt_simd::butterfly_lanes_avx512;
    check_kernel("avx512", 8, false, |t, b, at, tw| unsafe {
        butterfly_lanes_avx512::<false>(t, b, at, tw)
    });
    check_kernel("avx512", 8, true, |t, b, at, tw| unsafe {
        butterfly_lanes_avx512::<true>(t, b, at, tw)
    });
}

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "vpclmulqdq",
    target_feature = "avx2",
    not(target_feature = "avx512f")
))]
#[test]
fn avx2_kernel_matches_production_butterfly() {
    use leanvm_verus::ntt_simd::{butterfly_lanes_avx2, SPILL};
    // The listed nibble table is production's formula.
    for n in 0..16u8 {
        assert_eq!(SPILL[n as usize], n ^ (n >> 1) ^ (n >> 3));
    }
    check_kernel("avx2", 4, false, |t, b, at, tw| unsafe {
        butterfly_lanes_avx2::<false>(t, b, at, tw)
    });
    check_kernel("avx2", 4, true, |t, b, at, tw| unsafe {
        butterfly_lanes_avx2::<true>(t, b, at, tw)
    });
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[test]
fn neon_kernels_match_production_butterfly() {
    use leanvm_verus::ntt_simd::{butterfly_lane_pair_neon, butterfly_lanes_neon_8};
    check_kernel("neon_8", 8, false, |t, b, at, tw| unsafe {
        butterfly_lanes_neon_8::<false>(t, b, at, tw)
    });
    check_kernel("neon_8", 8, true, |t, b, at, tw| unsafe {
        butterfly_lanes_neon_8::<true>(t, b, at, tw)
    });
    check_kernel("pair", 2, false, |t, b, at, tw| unsafe {
        butterfly_lane_pair_neon::<false>(t, b, at, tw)
    });
    check_kernel("pair", 2, true, |t, b, at, tw| unsafe {
        butterfly_lane_pair_neon::<true>(t, b, at, tw)
    });
}

/// `lane_butterflies` (through `butterfly_lanes` and `transposed_butterfly_lanes`), whatever arm this build
/// dispatches to, on every row length up to 40: the SIMD blocks, the NEON pair tail and the scalar tail.
#[test]
fn lane_butterflies_match_production_butterfly() {
    let mut rng = Rng::new(0x1A_4E5);
    for n in 0..=40usize {
        for (k, t) in twiddles(&mut rng).into_iter().enumerate() {
            let (u, v) = (row(&mut rng, n, k), row(&mut rng, n, k + 1));
            for transposed in [false, true] {
                let mut top: Vec<VF64> = u.iter().map(|&x| VF64(x)).collect();
                let mut bot: Vec<VF64> = v.iter().map(|&x| VF64(x)).collect();
                if transposed {
                    verified::transposed_butterfly_lanes(&mut top, &mut bot, VF64(t));
                } else {
                    verified::butterfly_lanes(&mut top, &mut bot, VF64(t));
                }
                for j in 0..n {
                    assert_eq!(
                        (top[j].0, bot[j].0),
                        production_butterfly(transposed, u[j], v[j], t),
                        "n={n} transposed={transposed} t={t:#x} word {j}"
                    );
                }
            }
        }
    }
}

/// Production's encoder runs its own `lane_butterflies` (and so its SIMD kernels) on row pairs of `lanes` words; a
/// layer-by-layer forward transform made of the verified `butterfly_lanes` on the same row pairs must agree.
#[test]
fn verified_lane_butterflies_reproduce_the_encoder() {
    let mut rng = Rng::new(0xE1C0);
    for log_d in 1..=9usize {
        for lanes in [8usize, 9, 10, 11, 12, 16, 17, 24, 31] {
            let msg: Vec<F64> = (0..lanes << log_d).map(|_| F64(rng.next_u64())).collect();
            let ntt = verified::AdditiveNttF64::standard(log_d);
            let mut data: Vec<VF64> = msg.iter().map(|x| VF64(x.0)).collect();
            for layer in 0..log_d {
                let block_size = 1usize << (log_d - layer);
                let half = block_size / 2;
                for block in 0..1usize << layer {
                    let twiddle = ntt.twiddle(layer, block);
                    let rows = &mut data[block * block_size * lanes..(block + 1) * block_size * lanes];
                    let (tops, bots) = rows.split_at_mut(half * lanes);
                    for r in 0..half {
                        verified::butterfly_lanes(
                            &mut tops[r * lanes..(r + 1) * lanes],
                            &mut bots[r * lanes..(r + 1) * lanes],
                            twiddle,
                        );
                    }
                }
            }
            let mut got = msg;
            Production::standard(log_d).encode_interleaved_in_place(&mut got, lanes, 0);
            let want: Vec<F64> = data.iter().map(|x| F64(x.0)).collect();
            assert_eq!(got, want, "log_d={log_d}, lanes={lanes}");
        }
    }
}
