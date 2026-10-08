//! The x86-64 intrinsic specifications against the hardware.
//!
//! Each test runs the real intrinsic on edge and random operands, reads its result through the same `transmute` the
//! specification's view is defined by, and compares every lane with the executable twin of the specification. A test
//! whose ISA extension this CPU lacks says so and passes.
use core::arch::x86_64::*;
use core::mem::transmute;
use leanvm_verus::intrinsics::x86 as spec;
use primitives::test_util::Rng;

const N: usize = 20_000;

/// Edge words: zero, one, all ones, the top bit, the reduction constant, alternating bits, a single middle bit.
const EDGES: [u64; 8] = [
    0,
    1,
    u64::MAX,
    1 << 63,
    0x1B,
    0x5555_5555_5555_5555,
    0xAAAA_AAAA_AAAA_AAAA,
    1 << 32,
];

/// `n` words: the edge words cycled, then random ones.
fn words<const W: usize>(rng: &mut Rng, k: usize) -> [u64; W] {
    if k < EDGES.len() * EDGES.len() {
        std::array::from_fn(|i| EDGES[(k / EDGES.len() * (i + 1) + k % EDGES.len() * i) % EDGES.len()])
    } else {
        std::array::from_fn(|_| rng.next_u64())
    }
}

fn has(feature: bool, name: &str) -> bool {
    if !feature {
        eprintln!("this CPU has no {name}: its intrinsics are not tested here");
    }
    feature
}

fn m128(w: [u64; 2]) -> __m128i {
    unsafe { transmute(w) }
}
fn m256(w: [u64; 4]) -> __m256i {
    unsafe { transmute(w) }
}
fn m512(w: [u64; 8]) -> __m512i {
    unsafe { transmute(w) }
}
fn w128(v: __m128i) -> [u64; 2] {
    unsafe { transmute(v) }
}
fn w256(v: __m256i) -> [u64; 4] {
    unsafe { transmute(v) }
}
fn w512(v: __m512i) -> [u64; 8] {
    unsafe { transmute(v) }
}

#[test]
fn sse2_moves_and_xor() {
    let mut rng = Rng::new(0x5_5E2);
    for k in 0..N {
        let (a, b) = (words::<2>(&mut rng, k), words::<2>(&mut rng, k + 3));
        unsafe {
            assert_eq!(w128(_mm_cvtsi64_si128(a[0] as i64)), [a[0], 0]);
            assert_eq!(_mm_cvtsi128_si64(m128(a)) as u64, a[0]);
            assert_eq!(w128(_mm_set_epi64x(a[1] as i64, a[0] as i64)), a);
            assert_eq!(w128(_mm_xor_si128(m128(a), m128(b))), [a[0] ^ b[0], a[1] ^ b[1]]);
            let lo = w128(_mm_unpacklo_epi64(m128(a), m128(b)));
            let hi = w128(_mm_unpackhi_epi64(m128(a), m128(b)));
            for i in 0..2 {
                assert_eq!(lo[i], spec::model_unpacklo_lane(&a, &b, i));
                assert_eq!(hi[i], spec::model_unpackhi_lane(&a, &b, i));
            }
            // The layout axioms of a 128-bit register.
            for k in 0..16 {
                assert_eq!(
                    transmute::<__m128i, [u8; 16]>(m128(a))[k],
                    (a[k / 8] >> (8 * (k % 8))) as u8
                );
            }
            assert_eq!(
                transmute::<__m128i, u128>(m128(a)),
                u128::from(a[0]) | u128::from(a[1]) << 64
            );
        }
    }
}

macro_rules! check_clmul {
    ($f:ident, $view:ident, $make:ident, $a:expr, $b:expr, $($imm:literal),*) => {$({
        let r = $view($f::<$imm>($make($a), $make($b)));
        for i in 0..r.len() {
            assert_eq!(r[i], spec::model_clmul_lane(&$a, &$b, $imm as u8, i), "{} imm {:#x} lane {i}", stringify!($f), $imm);
        }
    })*};
}

#[test]
fn pclmulqdq() {
    if !has(is_x86_feature_detected!("pclmulqdq"), "pclmulqdq") {
        return;
    }
    #[target_feature(enable = "pclmulqdq")]
    fn run(a: [u64; 2], b: [u64; 2]) {
        check_clmul!(_mm_clmulepi64_si128, w128, m128, a, b, 0x00, 0x01, 0x10, 0x11);
    }
    let mut rng = Rng::new(0xC1_0001);
    for k in 0..N {
        let (a, b) = (words::<2>(&mut rng, k), words::<2>(&mut rng, k + 5));
        unsafe { run(a, b) };
    }
}

#[test]
fn bmi2_pdep() {
    if !has(is_x86_feature_detected!("bmi2"), "bmi2") {
        return;
    }
    #[target_feature(enable = "bmi2")]
    fn run(a: u64, mask: u64) {
        assert_eq!(_pdep_u64(a, mask), spec::model_pdep(a, mask), "pdep {a:#x} {mask:#x}");
    }
    let mut rng = Rng::new(0xBD_E9);
    for k in 0..N {
        let [a, mask] = words::<2>(&mut rng, k);
        unsafe { run(a, mask) };
    }
}

#[test]
fn avx2() {
    if !has(is_x86_feature_detected!("avx2"), "avx2") {
        return;
    }
    #[target_feature(enable = "avx2")]
    fn run(a: [u64; 4], b: [u64; 4], x: [u64; 2]) {
        let (va, vb) = (m256(a), m256(b));
        let lanes = |r: __m256i, f: &dyn Fn(usize) -> u64, name: &str| {
            let r = w256(r);
            for i in 0..4 {
                assert_eq!(r[i], f(i), "{name} lane {i}");
            }
        };
        lanes(_mm256_xor_si256(va, vb), &|i| a[i] ^ b[i], "xor");
        lanes(_mm256_and_si256(va, vb), &|i| a[i] & b[i], "and");
        lanes(_mm256_add_epi64(va, vb), &|i| a[i].wrapping_add(b[i]), "add");
        lanes(
            _mm256_unpacklo_epi64(va, vb),
            &|i| spec::model_unpacklo_lane(&a, &b, i),
            "unpacklo",
        );
        lanes(
            _mm256_unpackhi_epi64(va, vb),
            &|i| spec::model_unpackhi_lane(&a, &b, i),
            "unpackhi",
        );
        lanes(_mm256_set1_epi64x(a[0] as i64), &|_| a[0], "set1");
        lanes(
            _mm256_set_epi64x(a[3] as i64, a[2] as i64, a[1] as i64, a[0] as i64),
            &|i| a[i],
            "set",
        );
        lanes(_mm256_broadcastsi128_si256(m128(x)), &|i| x[i % 2], "broadcastsi128");
        macro_rules! shifts {
            ($($imm:literal),*) => {$(
                lanes(_mm256_slli_epi64::<$imm>(va), &|i| spec::model_shl_imm(a[i], $imm), "slli");
                lanes(_mm256_srli_epi64::<$imm>(va), &|i| spec::model_shr_imm(a[i], $imm), "srli");
            )*};
        }
        shifts!(0, 1, 3, 4, 8, 32, 56, 60, 61, 63, 64, 200);
        macro_rules! permutes {
            ($($imm:literal),*) => {$(
                lanes(_mm256_permute4x64_epi64::<$imm>(va), &|i| spec::model_permute4x64_lane(&a, $imm, i), "permute4x64");
            )*};
        }
        permutes!(0x00, 0x1B, 0x4E, 0x8D, 0xB1, 0xD8, 0xE4, 0xFF, 0x44, 0xEE);
        let (ba, bb) = (unsafe { transmute::<[u64; 4], [u8; 32]>(a) }, unsafe {
            transmute::<[u64; 4], [u8; 32]>(b)
        });
        let r = unsafe { transmute::<__m256i, [u8; 32]>(_mm256_shuffle_epi8(va, vb)) };
        for k in 0..32 {
            assert_eq!(
                r[k],
                spec::model_shuffle_epi8_lane(&ba, &bb, k),
                "shuffle_epi8 byte {k}"
            );
        }
        // The layout axioms of a 256-bit register: as pairs, as bytes.
        for k in 0..32 {
            assert_eq!(
                unsafe { transmute::<__m256i, [u8; 32]>(va) }[k],
                (a[k / 8] >> (8 * (k % 8))) as u8
            );
        }
        assert_eq!(
            unsafe { transmute::<__m256i, [[u64; 2]; 2]>(va) },
            [[a[0], a[1]], [a[2], a[3]]]
        );
    }
    let mut rng = Rng::new(0xA_2);
    for k in 0..N {
        let (a, b, x) = (
            words::<4>(&mut rng, k),
            words::<4>(&mut rng, k + 7),
            words::<2>(&mut rng, k + 1),
        );
        unsafe { run(a, b, x) };
    }
}

#[test]
fn vpclmulqdq_avx2() {
    if !has(
        is_x86_feature_detected!("vpclmulqdq") && is_x86_feature_detected!("avx2"),
        "vpclmulqdq with avx2",
    ) {
        return;
    }
    #[target_feature(enable = "vpclmulqdq,avx2")]
    fn run(a: [u64; 4], b: [u64; 4]) {
        check_clmul!(_mm256_clmulepi64_epi128, w256, m256, a, b, 0x00, 0x01, 0x10, 0x11);
    }
    let mut rng = Rng::new(0xC1_0256);
    for k in 0..N {
        let (a, b) = (words::<4>(&mut rng, k), words::<4>(&mut rng, k + 3));
        unsafe { run(a, b) };
    }
}

#[test]
fn avx512f() {
    if !has(is_x86_feature_detected!("avx512f"), "avx512f") {
        return;
    }
    #[target_feature(enable = "avx512f")]
    fn run(a: [u64; 8], b: [u64; 8], c: [u64; 8]) {
        let (va, vb, vc) = (m512(a), m512(b), m512(c));
        let lanes = |r: __m512i, f: &dyn Fn(usize) -> u64, name: &str| {
            let r = w512(r);
            for i in 0..8 {
                assert_eq!(r[i], f(i), "{name} lane {i}");
            }
        };
        lanes(_mm512_xor_si512(va, vb), &|i| a[i] ^ b[i], "xor");
        lanes(
            _mm512_unpacklo_epi64(va, vb),
            &|i| spec::model_unpacklo_lane(&a, &b, i),
            "unpacklo",
        );
        lanes(
            _mm512_unpackhi_epi64(va, vb),
            &|i| spec::model_unpackhi_lane(&a, &b, i),
            "unpackhi",
        );
        lanes(_mm512_set1_epi64(a[0] as i64), &|_| a[0], "set1");
        let (e0, e1, e2, e3) = (a[0] as i64, a[1] as i64, a[2] as i64, a[3] as i64);
        let (e4, e5, e6, e7) = (a[4] as i64, a[5] as i64, a[6] as i64, a[7] as i64);
        lanes(_mm512_set_epi64(e7, e6, e5, e4, e3, e2, e1, e0), &|i| a[i], "set");
        lanes(
            _mm512_permutex2var_epi64(va, vc, vb),
            &|i| spec::model_permutex2var_lane(&a, &c, &b, i),
            "permutex2var",
        );
        macro_rules! shifts {
            ($($imm:literal),*) => {$(
                lanes(_mm512_slli_epi64::<$imm>(va), &|i| spec::model_shl_imm(a[i], $imm), "slli");
                lanes(_mm512_srli_epi64::<$imm>(va), &|i| spec::model_shr_imm(a[i], $imm), "srli");
            )*};
        }
        shifts!(0, 1, 3, 4, 8, 32, 56, 60, 61, 63, 64, 200);
        macro_rules! shuffles {
            ($($imm:literal),*) => {$(
                lanes(_mm512_shuffle_i64x2::<$imm>(va, vb), &|i| spec::model_shuffle_i64x2_lane(&a, &b, $imm, i), "shuffle_i64x2");
            )*};
        }
        shuffles!(0x00, 0x44, 0xEE, 0x88, 0xDD, 0x4E, 0xE4, 0x1B, 0xFF);
        macro_rules! ternary {
            ($($imm:literal),*) => {$(
                lanes(_mm512_ternarylogic_epi64::<$imm>(va, vb, vc), &|i| spec::model_ternlog($imm, a[i], b[i], c[i]), "ternarylogic");
            )*};
        }
        ternary!(0x00, 0x96, 0x78, 0xE8, 0xCA, 0xF0, 0xCC, 0xAA, 0x3C, 0x6A, 0xFE, 0x80, 0x01, 0xFF);
        // The layout axioms of a 512-bit register.
        assert_eq!(
            unsafe { transmute::<__m512i, [[u64; 2]; 4]>(va) },
            [[a[0], a[1]], [a[2], a[3]], [a[4], a[5]], [a[6], a[7]]]
        );
        assert_eq!(w512(unsafe { transmute::<[u64; 8], __m512i>(a) }), a);
        for k in 0..64 {
            assert_eq!(
                unsafe { transmute::<__m512i, [u8; 64]>(va) }[k],
                (a[k / 8] >> (8 * (k % 8))) as u8
            );
        }
    }
    let mut rng = Rng::new(0xA_512);
    for k in 0..N {
        let (a, b) = (words::<8>(&mut rng, k), words::<8>(&mut rng, k + 7));
        // Index words: random low nibbles, the rest random too (the instruction reads bits 0 to 3 only).
        let c = if k % 2 == 0 {
            words::<8>(&mut rng, k + 2)
        } else {
            std::array::from_fn(|_| rng.next_u64() & 15)
        };
        unsafe { run(a, b, c) };
    }
}

#[test]
fn vpclmulqdq_avx512() {
    if !has(
        is_x86_feature_detected!("vpclmulqdq") && is_x86_feature_detected!("avx512f"),
        "vpclmulqdq with avx512f",
    ) {
        return;
    }
    #[target_feature(enable = "vpclmulqdq,avx512f")]
    fn run(a: [u64; 8], b: [u64; 8]) {
        check_clmul!(_mm512_clmulepi64_epi128, w512, m512, a, b, 0x00, 0x01, 0x10, 0x11);
    }
    let mut rng = Rng::new(0xC1_0512);
    for k in 0..N {
        let (a, b) = (words::<8>(&mut rng, k), words::<8>(&mut rng, k + 3));
        unsafe { run(a, b) };
    }
}
