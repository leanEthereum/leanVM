//! The AArch64 intrinsic specifications of the bit transposes, and their byte loads and stores, against the hardware
//! (natively on an ARM64 runner, or under `qemu-aarch64-static`).
//!
//! Each test runs the real intrinsic on edge and random operands, reads its result through the same `transmute` the
//! specification's view is defined by, and compares every lane with the executable twin of the specification.
use core::arch::aarch64::*;
use core::mem::transmute;
use leanvm_verus::intrinsics::aarch64_bits as spec;
use primitives::test_util::Rng;

const N: usize = 20_000;

const EDGES: [u64; 8] = [
    0,
    1,
    u64::MAX,
    1 << 63,
    0x00AA_00AA_00AA_00AA,
    0x5555_5555_5555_5555,
    0xF0F0_F0F0_0000_CCCC,
    1 << 32,
];

fn words(rng: &mut Rng, k: usize) -> [u64; 2] {
    if k < EDGES.len() * EDGES.len() {
        [EDGES[k / EDGES.len()], EDGES[k % EDGES.len()]]
    } else {
        [rng.next_u64(), rng.next_u64()]
    }
}

fn bytes<const B: usize>(rng: &mut Rng) -> [u8; B] {
    std::array::from_fn(|_| rng.next_u8())
}

fn v64(w: [u64; 2]) -> uint64x2_t {
    unsafe { transmute(w) }
}
fn w64(v: uint64x2_t) -> [u64; 2] {
    unsafe { transmute(v) }
}
fn v8(b: [u8; 16]) -> uint8x16_t {
    unsafe { transmute(b) }
}
fn b8(v: uint8x16_t) -> [u8; 16] {
    unsafe { transmute(v) }
}

#[test]
fn neon_table_lookup() {
    let mut rng = Rng::new(0x7B_4);
    for k in 0..N {
        let table = bytes::<64>(&mut rng);
        // Indices: the identity, past the table (64 and up return zero), the bit transpose's own, then random bytes,
        // about three quarters of which are past the table.
        let idx: [u8; 16] = match k {
            0 => std::array::from_fn(|i| i as u8),
            1 => std::array::from_fn(|i| 56 + i as u8),
            2 => [0, 8, 16, 24, 32, 40, 48, 56, 1, 9, 17, 25, 33, 41, 49, 57],
            3 => [63, 64, 65, 127, 128, 255, 0, 15, 16, 31, 32, 47, 48, 62, 200, 1],
            _ if k % 2 == 0 => std::array::from_fn(|_| rng.next_u8() & 63),
            _ => bytes::<16>(&mut rng),
        };
        let t = uint8x16x4_t(
            v8(table[0..16].try_into().unwrap()),
            v8(table[16..32].try_into().unwrap()),
            v8(table[32..48].try_into().unwrap()),
            v8(table[48..64].try_into().unwrap()),
        );
        let r = b8(unsafe { vqtbl4q_u8(t, v8(idx)) });
        for i in 0..16 {
            assert_eq!(
                r[i],
                spec::model_tbl4_byte(&table, idx[i]),
                "vqtbl4q_u8 byte {i}, index {}",
                idx[i]
            );
        }
    }
}

#[test]
fn neon_word_lanes() {
    let mut rng = Rng::new(0x5_4);
    for k in 0..N {
        let (a, b) = (words(&mut rng, k), words(&mut rng, k + 3));
        unsafe {
            assert_eq!(w64(vandq_u64(v64(a), v64(b))), [a[0] & b[0], a[1] & b[1]], "vandq_u64");
            macro_rules! shr {
                ($($n:literal),*) => {$(
                    assert_eq!(w64(vshrq_n_u64::<$n>(v64(a))), [spec::model_shr_n(a[0], $n), spec::model_shr_n(a[1], $n)], "vshrq_n_u64 {}", $n);
                )*};
            }
            shr!(1, 7, 14, 28, 32, 63, 64);
            macro_rules! shl {
                ($($n:literal),*) => {$(
                    assert_eq!(w64(vshlq_n_u64::<$n>(v64(a))), [spec::model_shl_n(a[0], $n), spec::model_shl_n(a[1], $n)], "vshlq_n_u64 {}", $n);
                )*};
            }
            shl!(0, 1, 7, 14, 28, 32, 63);
            // The reinterprets: bytes and words, little-endian.
            let ab: [u8; 16] = transmute(a);
            let r = b8(vreinterpretq_u8_u64(v64(a)));
            for i in 0..16 {
                assert_eq!(r[i], spec::model_u64x2_byte(&a, i), "vreinterpretq_u8_u64 byte {i}");
            }
            let back = w64(vreinterpretq_u64_u8(v8(ab)));
            for i in 0..16 {
                assert_eq!(spec::model_u64x2_byte(&back, i), ab[i], "vreinterpretq_u64_u8 byte {i}");
            }
        }
    }
}

#[test]
fn neon_byte_memory() {
    let mut rng = Rng::new(0x1D_4);
    for _ in 0..N {
        let (block, small, fill) = (bytes::<64>(&mut rng), bytes::<16>(&mut rng), bytes::<16>(&mut rng));
        assert_eq!(b8(spec::vld1q_u8_16(&small)), small, "vld1q_u8_16");
        for offset in [0, 1, 15, 16, 32, 47, 48] {
            assert_eq!(
                b8(spec::vld1q_u8_at(&block, offset))[..],
                block[offset..offset + 16],
                "vld1q_u8_at {offset}"
            );
            let mut out = block;
            spec::vst1q_u8_at(&mut out, offset, v8(fill));
            for k in 0..64 {
                let want = if (offset..offset + 16).contains(&k) {
                    fill[k - offset]
                } else {
                    block[k]
                };
                assert_eq!(out[k], want, "vst1q_u8_at {offset} byte {k}");
            }
        }
    }
}
