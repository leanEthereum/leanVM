//! The AArch64 intrinsic specifications against the hardware (natively on an ARM64 runner, or under
//! `qemu-aarch64-static`).
//!
//! Each test runs the real intrinsic on edge and random operands, reads its result through the same `transmute` the
//! specification's view is defined by, and compares every lane with the specification. A test whose ISA extension
//! this CPU lacks says so and passes.
use core::arch::aarch64::*;
use core::mem::transmute;
use leanvm_verus::gf2_64::software::clmul;
use primitives::test_util::Rng;
use std::arch::is_aarch64_feature_detected;

const N: usize = 20_000;

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

fn v(w: [u64; 2]) -> uint64x2_t {
    unsafe { transmute(w) }
}
fn w(v: uint64x2_t) -> [u64; 2] {
    unsafe { transmute(v) }
}

#[test]
fn neon_moves_and_xor() {
    let mut rng = Rng::new(0x4E_0);
    for k in 0..N {
        let (a, b) = (words::<2>(&mut rng, k), words::<2>(&mut rng, k + 3));
        unsafe {
            assert_eq!(w(vdupq_n_u64(a[0])), [a[0], a[0]]);
            assert_eq!(w(veorq_u64(v(a), v(b))), [a[0] ^ b[0], a[1] ^ b[1]]);
            assert_eq!(w(vzip1q_u64(v(a), v(b))), [a[0], b[0]]);
            assert_eq!(vgetq_lane_u64::<0>(v(a)), a[0]);
            assert_eq!(vgetq_lane_u64::<1>(v(a)), a[1]);
            // The layout axioms.
            let x = u128::from(a[0]) | u128::from(a[1]) << 64;
            assert_eq!(w(transmute::<u128, uint64x2_t>(x)), a);
            assert_eq!(transmute::<uint64x2_t, u128>(v(a)), x);
            assert_eq!(
                transmute::<poly64x2_t, [u64; 2]>(transmute::<uint64x2_t, poly64x2_t>(v(a))),
                a
            );
        }
    }
}

#[test]
fn pmull() {
    if !has(is_aarch64_feature_detected!("aes"), "aes (PMULL)") {
        return;
    }
    #[target_feature(enable = "aes")]
    fn run(a: [u64; 2], b: [u64; 2]) {
        assert_eq!(vmull_p64(a[0], b[0]), clmul(a[0], b[0]), "vmull_p64");
        let (pa, pb) = unsafe {
            (
                transmute::<[u64; 2], poly64x2_t>(a),
                transmute::<[u64; 2], poly64x2_t>(b),
            )
        };
        assert_eq!(vmull_high_p64(pa, pb), clmul(a[1], b[1]), "vmull_high_p64");
    }
    let mut rng = Rng::new(0x9_0001);
    for k in 0..N {
        let (a, b) = (words::<2>(&mut rng, k), words::<2>(&mut rng, k + 5));
        unsafe { run(a, b) };
    }
}

#[test]
fn sha3_eor3() {
    if !has(is_aarch64_feature_detected!("sha3"), "sha3 (EOR3)") {
        return;
    }
    #[target_feature(enable = "sha3")]
    fn run(a: [u64; 2], b: [u64; 2], c: [u64; 2]) {
        assert_eq!(
            w(veor3q_u64(v(a), v(b), v(c))),
            [a[0] ^ b[0] ^ c[0], a[1] ^ b[1] ^ c[1]]
        );
    }
    let mut rng = Rng::new(0xE0_3);
    for k in 0..N {
        let (a, b, c) = (
            words::<2>(&mut rng, k),
            words::<2>(&mut rng, k + 5),
            words::<2>(&mut rng, k + 2),
        );
        unsafe { run(a, b, c) };
    }
}
