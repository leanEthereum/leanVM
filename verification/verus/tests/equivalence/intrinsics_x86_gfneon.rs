//! The AVX2 byte intrinsic specifications of `src/intrinsics/x86_gfneon.rs` against the hardware.
//!
//! Each test runs the real intrinsic on edge and random operands, reads its result through `transmute`, and
//! compares every byte with the specification (its executable twin where there is one). A machine without AVX2
//! says so and passes.
use core::arch::x86_64::*;
use core::mem::transmute;
use leanvm_verus::intrinsics::x86_gfneon::model_cmpgt_epi8_lane;
use primitives::test_util::Rng;
use std::arch::is_x86_feature_detected;

const N: usize = 20_000;

/// 32 bytes: every byte value appears in the first eight vectors, in every lane position over the edge rounds.
fn bytes(rng: &mut Rng, k: usize) -> [u8; 32] {
    if k < 256 {
        std::array::from_fn(|i| (k + 37 * i) as u8)
    } else {
        std::array::from_fn(|_| rng.next_u64() as u8)
    }
}

#[target_feature(enable = "avx2")]
fn run(a: [u8; 32], b: [u8; 32]) {
    let r = |x: __m256i| unsafe { transmute::<__m256i, [u8; 32]>(x) };
    let (va, vb) = unsafe { (transmute::<[u8; 32], __m256i>(a), transmute::<[u8; 32], __m256i>(b)) };
    assert_eq!(
        unsafe { transmute::<__m256i, [u64; 4]>(_mm256_setzero_si256()) },
        [0; 4],
        "_mm256_setzero_si256"
    );
    assert_eq!(r(_mm256_set1_epi8(a[0] as i8)), [a[0]; 32], "_mm256_set1_epi8");
    assert_eq!(
        r(_mm256_add_epi8(va, vb)),
        std::array::from_fn(|i| a[i].wrapping_add(b[i])),
        "_mm256_add_epi8"
    );
    assert_eq!(
        r(_mm256_cmpgt_epi8(va, vb)),
        std::array::from_fn(|i| model_cmpgt_epi8_lane(a[i], b[i])),
        "_mm256_cmpgt_epi8"
    );
}

#[test]
fn avx2_byte_ops() {
    if !is_x86_feature_detected!("avx2") {
        eprintln!("this CPU has no avx2: its intrinsics are not tested here");
        return;
    }
    let mut rng = Rng::new(0x8B_0);
    for k in 0..N {
        let (a, b) = (
            bytes(&mut rng, k),
            bytes(&mut rng, (k * 7 + 3) % 256 + if k < 256 { 0 } else { 256 }),
        );
        unsafe { run(a, b) };
    }
    // The compare against zero, the use the kernel makes of it, for every byte.
    for x in 0..=u8::MAX {
        unsafe { run([0; 32], [x; 32]) };
    }
}
