//! The x86-64 intrinsic specifications of the bit transposes, and their byte loads and stores, against the hardware.
//!
//! Each test runs the real intrinsic on edge and random operands, reads its result through the same `transmute` the
//! specification's view is defined by, and compares every lane with the executable twin of the specification. A test
//! whose ISA extension this CPU lacks says so and passes.
use core::arch::x86_64::*;
use core::mem::transmute;
use leanvm_verus::intrinsics::x86_bits as spec;
use primitives::test_util::Rng;

const N: usize = 20_000;

/// Edge words: zero, all ones, the GFNI unit matrix, the identity matrix of the other bit order, one bit per byte,
/// alternating bits, the AES S-box's affine matrix, a single bit.
const EDGES: [u64; 8] = [
    0,
    u64::MAX,
    0x8040_2010_0804_0201,
    0x0102_0408_1020_4080,
    0x0101_0101_0101_0101,
    0x5555_5555_5555_5555,
    0xF1E3_C78F_1F3E_7CF8,
    1 << 37,
];

/// The edge words cycled, then random ones.
fn words<const W: usize>(rng: &mut Rng, k: usize) -> [u64; W] {
    if k < EDGES.len() * EDGES.len() {
        std::array::from_fn(|i| EDGES[(k / EDGES.len() * (i + 1) + k % EDGES.len() * i) % EDGES.len()])
    } else {
        std::array::from_fn(|_| rng.next_u64())
    }
}

fn bytes<const B: usize>(rng: &mut Rng) -> [u8; B] {
    std::array::from_fn(|_| rng.next_u8())
}

fn has(feature: bool, name: &str) -> bool {
    if !feature {
        eprintln!("this CPU has no {name}: its intrinsics are not tested here");
    }
    feature
}

fn m256(w: [u64; 4]) -> __m256i {
    unsafe { transmute(w) }
}
fn m512(w: [u64; 8]) -> __m512i {
    unsafe { transmute(w) }
}
fn b256(v: __m256i) -> [u8; 32] {
    unsafe { transmute(v) }
}
fn b512(v: __m512i) -> [u8; 64] {
    unsafe { transmute(v) }
}

/// GF2P8AFFINEQB from Intel's pseudocode, independently of the specification's closed form: bit `i` of the result is
/// the parity of `A.byte[7 - i] & x`, XOR bit `i` of the immediate.
fn affine_reference(a: u64, x: u8, imm8: u8) -> u8 {
    (0..8).fold(0u8, |r, i| {
        let row = (a >> (8 * (7 - i))) as u8;
        r | ((((row & x).count_ones() as u8) & 1) ^ ((imm8 >> i) & 1)) << i
    })
}

#[test]
fn affine_byte_matches_intel_pseudocode() {
    let mut rng = Rng::new(0xAFF_0);
    for k in 0..N {
        let a = words::<1>(&mut rng, k)[0];
        for x in [0u8, 1, 0x80, 0xFF, 0x55, rng.next_u8()] {
            for imm8 in [0u8, 1, 0x63, 0x80, 0xFF, rng.next_u8()] {
                assert_eq!(
                    spec::model_affine_byte(a, x, imm8),
                    affine_reference(a, x, imm8),
                    "a={a:#x} x={x:#x} imm8={imm8:#x}"
                );
            }
        }
    }
}

#[test]
fn avx2_byte_unpacks_and_memory() {
    if !has(is_x86_feature_detected!("avx2"), "avx2") {
        return;
    }
    #[target_feature(enable = "avx2")]
    fn run(a: [u64; 4], b: [u64; 4], block: [u8; 64], small: [u8; 16], fill: [u8; 64]) {
        let (ba, bb): ([u8; 32], [u8; 32]) = unsafe { (transmute(a), transmute(b)) };
        let (lo, hi) = (
            b256(_mm256_unpacklo_epi8(m256(a), m256(b))),
            b256(_mm256_unpackhi_epi8(m256(a), m256(b))),
        );
        for k in 0..32 {
            assert_eq!(
                lo[k],
                spec::model_unpacklo_epi8_lane(&ba, &bb, k),
                "unpacklo_epi8 byte {k}"
            );
            assert_eq!(
                hi[k],
                spec::model_unpackhi_epi8_lane(&ba, &bb, k),
                "unpackhi_epi8 byte {k}"
            );
        }
        unsafe {
            assert_eq!(
                transmute::<__m128i, [u8; 16]>(spec::load128_bytes(&small)),
                small,
                "load128_bytes"
            );
            for offset in [0, 1, 7, 16, 31, 32] {
                let v = spec::load256_bytes_at(&block, offset);
                assert_eq!(b256(v)[..], block[offset..offset + 32], "load256_bytes_at {offset}");
                let mut out = fill;
                spec::store256_bytes_at(&mut out, offset, m256(a));
                for k in 0..64 {
                    let want = if (offset..offset + 32).contains(&k) {
                        ba[k - offset]
                    } else {
                        fill[k]
                    };
                    assert_eq!(out[k], want, "store256_bytes_at {offset} byte {k}");
                }
            }
        }
    }
    let mut rng = Rng::new(0xB_256);
    for k in 0..N {
        let (a, b) = (words::<4>(&mut rng, k), words::<4>(&mut rng, k + 3));
        let (block, small, fill) = (bytes::<64>(&mut rng), bytes::<16>(&mut rng), bytes::<64>(&mut rng));
        unsafe { run(a, b, block, small, fill) };
    }
}

#[test]
fn avx512vbmi_byte_permute_and_memory() {
    if !has(
        is_x86_feature_detected!("avx512vbmi") && is_x86_feature_detected!("avx512f"),
        "avx512vbmi",
    ) {
        return;
    }
    #[target_feature(enable = "avx512f,avx512vbmi")]
    fn run(idx: [u8; 64], a: [u8; 64], fill: [u8; 64]) {
        let (vi, va): (__m512i, __m512i) = unsafe { (transmute(idx), transmute(a)) };
        let r = b512(_mm512_permutexvar_epi8(vi, va));
        for k in 0..64 {
            assert_eq!(
                r[k],
                spec::model_permutexvar_epi8_lane(&idx, &a, k),
                "permutexvar_epi8 byte {k}"
            );
        }
        unsafe {
            assert_eq!(b512(spec::load512_bytes(&a)), a, "load512_bytes");
            let mut out = fill;
            spec::store512_bytes(&mut out, va);
            assert_eq!(out, a, "store512_bytes");
        }
    }
    let mut rng = Rng::new(0xB_512);
    for k in 0..N {
        // Indices: the identity, the reversal, every byte the same, then random (the top two bits random too, which
        // the instruction ignores).
        let idx: [u8; 64] = match k {
            0 => std::array::from_fn(|i| i as u8),
            1 => std::array::from_fn(|i| 63 - i as u8),
            2 => [0xC5; 64],
            _ => bytes::<64>(&mut rng),
        };
        let (a, fill) = (bytes::<64>(&mut rng), bytes::<64>(&mut rng));
        unsafe { run(idx, a, fill) };
    }
}

macro_rules! check_affine {
    ($f:ident, $view:ident, $reg:ident, $x:expr, $a:expr, $($imm:literal),*) => {$(
        let r = $view($f::<$imm>($reg($x), $reg($a)));
        let xb: Vec<u8> = $x.iter().flat_map(|w: &u64| w.to_le_bytes()).collect();
        for k in 0..r.len() {
            assert_eq!(r[k], spec::model_gf2p8affine_lane(&xb, &$a, $imm, k), "{} imm {} byte {k}", stringify!($f), $imm);
        }
    )*};
}

#[test]
fn gfni_affine_avx2() {
    if !has(
        is_x86_feature_detected!("gfni") && is_x86_feature_detected!("avx2"),
        "gfni with avx2",
    ) {
        return;
    }
    #[target_feature(enable = "gfni,avx2")]
    fn run(x: [u64; 4], a: [u64; 4]) {
        check_affine!(
            _mm256_gf2p8affine_epi64_epi8,
            b256,
            m256,
            x,
            a,
            0,
            1,
            0x63,
            0x80,
            0xAA,
            0xFF
        );
    }
    let mut rng = Rng::new(0x6F_256);
    for k in 0..N {
        let (x, a) = (words::<4>(&mut rng, k + 5), words::<4>(&mut rng, k));
        unsafe { run(x, a) };
    }
}

#[test]
fn gfni_affine_avx512() {
    if !has(
        is_x86_feature_detected!("gfni") && is_x86_feature_detected!("avx512f"),
        "gfni with avx512f",
    ) {
        return;
    }
    #[target_feature(enable = "gfni,avx512f")]
    fn run(x: [u64; 8], a: [u64; 8]) {
        check_affine!(
            _mm512_gf2p8affine_epi64_epi8,
            b512,
            m512,
            x,
            a,
            0,
            1,
            0x63,
            0x80,
            0xAA,
            0xFF
        );
    }
    let mut rng = Rng::new(0x6F_512);
    for k in 0..N {
        let (x, a) = (words::<8>(&mut rng, k + 5), words::<8>(&mut rng, k));
        unsafe { run(x, a) };
    }
}
