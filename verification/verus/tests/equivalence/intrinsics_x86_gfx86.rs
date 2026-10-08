//! Hardware checks of every additional GF192 intrinsic assumption. Undefined upper
//! words of the widening cast are deliberately not inspected.
use core::arch::x86_64::*;
use core::mem::{transmute, zeroed};
use leanvm_verus::intrinsics::{x86 as base, x86_gfx86 as model};
use primitives::test_util::Rng;

fn words<const N: usize>(rng: &mut Rng, n: usize) -> [u64; N] {
    const E: [u64; 8] = [
        0,
        1,
        u64::MAX,
        1 << 63,
        0x1b,
        0x5555_5555_5555_5555,
        0xAAAA_AAAA_AAAA_AAAA,
        1 << 32,
    ];
    std::array::from_fn(|i| if n < 64 { E[(n + i * 3) % 8] } else { rng.next_u64() })
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

macro_rules! shuffle {
    ($f:ident,$view:ident,$a:expr,$($imm:literal),*) => {$(
        let actual = $view($f::<$imm>(transmute($a)));
        for i in 0..actual.len() { assert_eq!(actual[i],model::model_shuffle_epi32_lane(&$a,$imm,i)); }
    )*};
}
macro_rules! shifts {
    ($a:expr,$($imm:literal),*) => {$(
        let left = w128(_mm_slli_epi64::<$imm>(transmute($a)));
        let right = w128(_mm_srli_epi64::<$imm>(transmute($a)));
        for i in 0..2 {
            assert_eq!(left[i],base::model_shl_imm($a[i],$imm));
            assert_eq!(right[i],base::model_shr_imm($a[i],$imm));
        }
    )*};
}
#[test]
fn sse2_additional_assumptions() {
    let mut rng = Rng::new(0x192_128);
    for n in 0..2048 {
        let a = words::<2>(&mut rng, n);
        unsafe {
            assert_eq!(w128(_mm_setzero_si128()), [0; 2]);
            assert_eq!(w128(_mm_set1_epi64x(a[0] as i64)), [a[0]; 2]);
            shifts!(a, 0, 1, 3, 4, 31, 32, 60, 61, 63, 64, 65, 255);
            shuffle!(_mm_shuffle_epi32, w128, a, 0, 0x1b, 0x4e, 0x55, 0x88, 0xaa, 0xe4, 0xff);
        }
    }
}
macro_rules! pair_moves {
    ($a:expr,$b:expr,$($imm:literal),*) => {$(
        let blend = w256(_mm256_blend_epi32::<$imm>(transmute($a),transmute($b)));
        let perm = w256(_mm256_permute2x128_si256::<$imm>(transmute($a),transmute($b)));
        for i in 0..4 {
            assert_eq!(blend[i],model::model_blend_epi32_lane(&$a,&$b,$imm,i));
            assert_eq!(perm[i],model::model_permute2x128_lane(&$a,&$b,$imm,i));
        }
    )*};
}
#[test]
fn avx2_additional_assumptions() {
    if !is_x86_feature_detected!("avx2") {
        eprintln!("AVX2 not available; hardware test skipped");
        return;
    }
    #[target_feature(enable = "avx2")]
    unsafe fn run(a: [u64; 4], b: [u64; 4]) {
        shuffle!(
            _mm256_shuffle_epi32,
            w256,
            a,
            0,
            0x1b,
            0x4e,
            0x55,
            0x88,
            0xaa,
            0xe4,
            0xff
        );
        pair_moves!(a, b, 0, 1, 2, 3, 8, 0x20, 0x31, 0x44, 0x88, 0xc3, 0xff);
        let p = _mm256_permutevar_pd(transmute(a), transmute(b));
        let actual: [u64; 4] = transmute(p);
        for i in 0..4 {
            assert_eq!(actual[i], model::model_permutevar_pd_lane(&a, &b, i));
        }
        assert_eq!(w256(_mm256_castpd_si256(p)), actual);
        assert_eq!(w128(_mm256_castsi256_si128(transmute(a))), [a[0], a[1]]);
        assert_eq!(w128(_mm256_extracti128_si256::<0>(transmute(a))), [a[0], a[1]]);
        assert_eq!(w128(_mm256_extracti128_si256::<1>(transmute(a))), [a[2], a[3]]);
        let z: [[__m256i; 6]; 2] = zeroed();
        for half in z {
            for v in half {
                assert_eq!(w256(v), [0; 4]);
            }
        }
    }
    let mut rng = Rng::new(0x192_256);
    for n in 0..2048 {
        unsafe {
            run(words(&mut rng, n), words(&mut rng, n + 5));
        }
    }
}
#[test]
fn avx512_additional_assumptions() {
    if !is_x86_feature_detected!("avx512f") {
        eprintln!("AVX512F not available; hardware test skipped");
        return;
    }
    #[target_feature(enable = "avx512f")]
    unsafe fn run(a: [u64; 8]) {
        shuffle!(
            _mm512_shuffle_epi32,
            w512,
            a,
            0,
            0x1b,
            0x4e,
            0x55,
            0x88,
            0xaa,
            0xe4,
            0xff
        );
        assert_eq!(w512(_mm512_setzero_si512()), [0; 8]);
        assert_eq!(
            w512(_mm512_broadcast_i32x4(transmute([a[0], a[1]]))),
            [a[0], a[1], a[0], a[1], a[0], a[1], a[0], a[1]]
        );
        let low = [a[0], a[1], a[2], a[3]];
        assert_eq!(w256(_mm512_castsi512_si256(transmute(a))), low);
        let widened = _mm512_castsi256_si512(transmute(low));
        assert_eq!(w256(_mm512_castsi512_si256(widened)), low);
        assert_eq!(w256(_mm512_extracti64x4_epi64::<0>(transmute(a))), low);
        assert_eq!(
            w256(_mm512_extracti64x4_epi64::<1>(transmute(a))),
            [a[4], a[5], a[6], a[7]]
        );
        let z: [__m512i; 6] = zeroed();
        for v in z {
            assert_eq!(w512(v), [0; 8]);
        }
    }
    let mut rng = Rng::new(0x192_512);
    for n in 0..2048 {
        unsafe {
            run(words(&mut rng, n));
        }
    }
}
