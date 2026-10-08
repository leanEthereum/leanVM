//! The AArch64 intrinsic specifications of `src/intrinsics/aarch64_gfneon.rs` (and the memory helpers of
//! `gf2_64x3::aarch64`) against the hardware, natively on an ARM64 runner or under `qemu-aarch64-static`.
//!
//! Each test runs the real intrinsic on edge and random operands, reads its result through the same `transmute`
//! the specification's view is defined by, and compares every lane with the specification's executable twin.
use core::arch::aarch64::*;
use core::mem::{transmute, MaybeUninit};
use leanvm_verus::gf2_64x3::aarch64::{load_f192, store_f192};
use leanvm_verus::gf2_64x3::F192;
use leanvm_verus::intrinsics::aarch64_gfneon::*;
use primitives::test_util::Rng;

const N: usize = 20_000;

const EDGES: [u64; 8] = [
    0,
    1,
    u64::MAX,
    1 << 63,
    0x1B,
    0x5555_5555_5555_5555,
    0xAAAA_AAAA_AAAA_AAAA,
    0x8080_8080_8080_8080,
];

fn words<const W: usize>(rng: &mut Rng, k: usize) -> [u64; W] {
    if k < EDGES.len() * EDGES.len() {
        std::array::from_fn(|i| EDGES[(k / EDGES.len() * (i + 1) + k % EDGES.len() * i) % EDGES.len()])
    } else {
        std::array::from_fn(|_| rng.next_u64())
    }
}

/// Sixteen bytes: the little-endian bytes of two words.
fn bytes16(rng: &mut Rng, k: usize) -> [u8; 16] {
    unsafe { transmute::<[u64; 2], [u8; 16]>(words::<2>(rng, k)) }
}

fn v(w: [u64; 2]) -> uint64x2_t {
    unsafe { transmute(w) }
}
fn w(v: uint64x2_t) -> [u64; 2] {
    unsafe { transmute(v) }
}
fn vb(b: [u8; 16]) -> uint8x16_t {
    unsafe { transmute(b) }
}
fn b16(v: uint8x16_t) -> [u8; 16] {
    unsafe { transmute(v) }
}
fn b8(v: uint8x8_t) -> [u8; 8] {
    unsafe { transmute(v) }
}
fn p8(v: poly8x8_t) -> [u8; 8] {
    unsafe { transmute(v) }
}
fn h8(v: uint16x8_t) -> [u16; 8] {
    unsafe { transmute(v) }
}
fn ph8(v: poly16x8_t) -> [u16; 8] {
    unsafe { transmute(v) }
}

#[test]
fn neon_u64_lane_moves() {
    let mut rng = Rng::new(0x6F_0);
    for k in 0..N {
        let (a, b) = (words::<2>(&mut rng, k), words::<2>(&mut rng, k + 3));
        unsafe {
            assert_eq!(
                transmute::<poly64x2_t, [u64; 2]>(vreinterpretq_p64_u64(v(a))),
                a,
                "vreinterpretq_p64_u64"
            );
            assert_eq!(
                transmute::<uint64x1_t, [u64; 1]>(vcreate_u64(a[0])),
                [a[0]],
                "vcreate_u64"
            );
            let (x, y) = (
                transmute::<[u64; 1], uint64x1_t>([a[1]]),
                transmute::<[u64; 1], uint64x1_t>([b[0]]),
            );
            assert_eq!(w(vcombine_u64(x, y)), [a[1], b[0]], "vcombine_u64");
            let ext0: [u64; 2] = std::array::from_fn(|i| model_ext_u64_lane(a, b, 0, i));
            let ext1: [u64; 2] = std::array::from_fn(|i| model_ext_u64_lane(a, b, 1, i));
            assert_eq!(w(vextq_u64::<0>(v(a), v(b))), ext0, "vextq_u64::<0>");
            assert_eq!(w(vextq_u64::<1>(v(a), v(b))), ext1, "vextq_u64::<1>");
            assert_eq!(w(vdupq_laneq_u64::<0>(v(a))), [a[0], a[0]], "vdupq_laneq_u64::<0>");
            assert_eq!(w(vdupq_laneq_u64::<1>(v(a))), [a[1], a[1]], "vdupq_laneq_u64::<1>");
            // The layout axiom: `[u64; 2]` read as a register has those lanes.
            assert_eq!(w(transmute::<[u64; 2], uint64x2_t>(a)), a);
        }
    }
}

#[test]
fn neon_byte_lanes() {
    let mut rng = Rng::new(0x6F_1);
    for k in 0..N {
        let (a, b) = (bytes16(&mut rng, k), bytes16(&mut rng, k + 5));
        unsafe {
            let uzp1: [u8; 16] = std::array::from_fn(|i| model_uzp_u8_lane(&a, &b, 0, i));
            let uzp2: [u8; 16] = std::array::from_fn(|i| model_uzp_u8_lane(&a, &b, 1, i));
            assert_eq!(b16(vuzp1q_u8(vb(a), vb(b))), uzp1, "vuzp1q_u8");
            assert_eq!(b16(vuzp2q_u8(vb(a), vb(b))), uzp2, "vuzp2q_u8");
            assert_eq!(
                b16(veorq_u8(vb(a), vb(b))),
                std::array::from_fn(|i| a[i] ^ b[i]),
                "veorq_u8"
            );
            assert_eq!(b8(vget_low_u8(vb(a))), std::array::from_fn(|i| a[i]), "vget_low_u8");
            assert_eq!(
                b8(vget_high_u8(vb(a))),
                std::array::from_fn(|i| a[i + 8]),
                "vget_high_u8"
            );
            assert_eq!(p8(vdup_n_p8(a[3])), [a[3]; 8], "vdup_n_p8");
            // The layout axioms: a `uint8x8_t` read as a `poly8x8_t`, and a `u64` read as a `poly8x8_t`.
            let lo = vget_low_u8(vb(a));
            assert_eq!(p8(transmute::<uint8x8_t, poly8x8_t>(lo)), b8(lo));
            let x = u64::from_le_bytes(std::array::from_fn(|i| b[i]));
            assert_eq!(
                p8(transmute::<u64, poly8x8_t>(x)),
                std::array::from_fn(|i| (x >> (8 * i)) as u8)
            );
        }
    }
    // The two constants the reduction reinterprets.
    for (x, c) in [(0x8d8d8d8d8d8d8d8d_u64, 0x8d_u8), (0x1b1b1b1b1b1b1b1b_u64, 0x1b_u8)] {
        assert_eq!(p8(unsafe { transmute::<u64, poly8x8_t>(x) }), [c; 8]);
    }
}

#[test]
fn neon_u16_lanes() {
    let mut rng = Rng::new(0x6F_2);
    for k in 0..N {
        let a = bytes16(&mut rng, k);
        let h: [u16; 8] = unsafe { transmute(a) };
        unsafe {
            let hv = transmute::<[u16; 8], uint16x8_t>(h);
            let ph = transmute::<[u16; 8], poly16x8_t>(h);
            assert_eq!(h8(vreinterpretq_u16_p16(ph)), ph8(ph), "vreinterpretq_u16_p16");
            let bytes: [u8; 16] = std::array::from_fn(|i| model_u16_byte(&h, i));
            assert_eq!(b16(vreinterpretq_u8_u16(hv)), bytes, "vreinterpretq_u8_u16");
            assert_eq!(h8(vshlq_n_u16::<1>(hv)), h.map(|x| x << 1), "vshlq_n_u16::<1>");
            assert_eq!(h8(vshlq_n_u16::<7>(hv)), h.map(|x| x << 7), "vshlq_n_u16::<7>");
            assert_eq!(vgetq_lane_u16::<0>(hv), h[0], "vgetq_lane_u16::<0>");
            assert_eq!(vgetq_lane_u16::<5>(hv), h[5], "vgetq_lane_u16::<5>");
        }
    }
}

/// PMULL on bytes, on every pair of bytes in every lane position.
#[test]
fn neon_vmull_p8() {
    for a in 0..=u8::MAX {
        for b0 in (0..=u8::MAX).step_by(8) {
            let x = [a; 8];
            let y: [u8; 8] = std::array::from_fn(|i| b0.wrapping_add(i as u8 * 37));
            let got = ph8(unsafe { vmull_p8(transmute::<[u8; 8], poly8x8_t>(x), transmute::<[u8; 8], poly8x8_t>(y)) });
            let want: [u16; 8] = std::array::from_fn(|i| model_vmull_p8_lane(x[i], y[i]));
            assert_eq!(got, want, "vmull_p8 {a:#x} {y:x?}");
        }
    }
}

/// The trusted memory helpers of `F192x1::load` and `F192x1::store`.
#[test]
fn f192_load_store_helpers() {
    let mut rng = Rng::new(0x6F_3);
    for k in 0..N {
        let [c0, c1, c2] = words::<3>(&mut rng, k);
        let e = F192::new(c0, c1, c2);
        let (r01, r22) = load_f192(&e);
        assert_eq!((w(r01), w(r22)), ([c0, c1], [c2, c2]), "load_f192");
        let (x, y) = (words::<2>(&mut rng, k + 7), words::<2>(&mut rng, k + 1));
        let mut out = MaybeUninit::<F192>::uninit();
        store_f192(&mut out, v(x), v(y));
        let got = unsafe { out.assume_init() };
        assert_eq!((got.c0, got.c1, got.c2), (x[0], x[1], y[0]), "store_f192");
    }
}
