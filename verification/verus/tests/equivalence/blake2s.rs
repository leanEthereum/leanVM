use leanvm_verus::blake2s as verified;
use primitives::hash as production;
use primitives::test_util::Rng;

fn random_bytes(rng: &mut Rng, n: usize) -> Vec<u8> {
    (0..n).map(|_| rng.next_u8()).collect()
}

#[test]
fn constants_match() {
    assert_eq!(verified::IV, production::IV);
    assert_eq!(verified::PARAM_IV, production::PARAM_IV);
    assert_eq!(verified::SIGMA, production::SIGMA);
    assert_eq!(verified::G_LANES, production::G_LANES);
    assert_eq!(verified::OUT_LEN, production::OUT_LEN);
    assert_eq!(verified::BLOCK_LEN, production::BLOCK_LEN);
    assert_eq!(verified::ROUNDS, production::ROUNDS);
}

/// The trusted specification of `u32::rotate_right` (`0 < n < 32`): the RFC's `(x >> n) ^ (x << (32 - n))`.
#[test]
fn rotate_right_is_the_rfc_rotation() {
    let mut rng = Rng::new(0x2077_7777);
    let edges = [0u32, 1, u32::MAX, 1 << 31, 0x8000_0001, 0xDEAD_BEEF];
    for x in edges.into_iter().chain((0..10_000).map(|_| rng.next_u32())) {
        for n in 1..32u32 {
            assert_eq!(x.rotate_right(n), (x >> n) ^ (x << (32 - n)), "{x:#x} >>> {n}");
        }
    }
}

/// Counters at both halves' edges, both flags, then random states and blocks.
#[test]
fn compress_matches() {
    let mut rng = Rng::new(0xB2_7777);
    let counters = [
        0u64,
        1,
        64,
        u32::MAX as u64,
        1 << 32,
        (1 << 32) + 64,
        u64::MAX - 63,
        u64::MAX,
    ];
    for i in 0..20_000 {
        let h: [u32; 8] = if i == 0 {
            [0; 8]
        } else {
            std::array::from_fn(|_| rng.next_u32())
        };
        let m: [u32; 16] = match i {
            0 => [0; 16],
            1 => [u32::MAX; 16],
            _ => std::array::from_fn(|_| rng.next_u32()),
        };
        let t = if i < counters.len() * 4 {
            counters[i % counters.len()]
        } else {
            rng.next_u64()
        };
        let last = rng.bit();
        let (mut v, mut p) = (h, h);
        verified::compress(&mut v, &m, t, last);
        production::compress(&mut p, &m, t, last);
        assert_eq!(v, p, "h {h:x?} m {m:x?} t {t} last {last}");
    }
}

/// Production's `block_words` and `state_bytes` are private: the verified copies are checked against the
/// little-endian conversions they replace, and through `hash` below.
#[test]
fn byte_conversions_are_little_endian() {
    let mut rng = Rng::new(0x1E_7777);
    for _ in 0..10_000 {
        let block: [u8; 64] = std::array::from_fn(|_| rng.next_u8());
        let want: [u32; 16] = std::array::from_fn(|i| u32::from_le_bytes(block[4 * i..4 * i + 4].try_into().unwrap()));
        assert_eq!(verified::block_words(&block), want);
        let h: [u32; 8] = std::array::from_fn(|_| rng.next_u32());
        let want: Vec<u8> = h.iter().flat_map(|w| w.to_le_bytes()).collect();
        assert_eq!(verified::state_bytes(&h).to_vec(), want);
    }
}

/// Every length up to five blocks (both the whole-block fast path and the streaming path), then random lengths.
#[test]
fn hash_matches() {
    let mut rng = Rng::new(0x4A54_7777);
    let lengths: Vec<usize> = (0..=320)
        .chain((0..300).map(|_| (rng.next_u32() % 4096) as usize))
        .collect();
    for n in lengths {
        let data = random_bytes(&mut rng, n);
        assert_eq!(verified::hash(&data), production::hash(&data), "{n} bytes");
    }
    for (input, digest) in primitives::test_util::test_vectors() {
        assert_eq!(verified::hash(&input), digest, "official vector, {} bytes", input.len());
    }
}

/// RFC 7693, Appendix B: BLAKE2s-256("abc"). The verified `hash` is proven equal to the specification
/// `blake2s_spec`, so this checks the transcription of the RFC against the RFC's own example.
#[test]
fn rfc_7693_appendix_b() {
    let want = [
        0x50, 0x8C, 0x5E, 0x8C, 0x32, 0x7C, 0x14, 0xE2, 0xE1, 0xA7, 0x2B, 0xA3, 0x4E, 0xEB, 0x45, 0x2F, 0x37, 0x45,
        0x8B, 0x20, 0x9E, 0xD6, 0x3A, 0x29, 0x4D, 0x99, 0x9B, 0x4C, 0x86, 0x67, 0x59, 0x82,
    ];
    assert_eq!(verified::hash(b"abc"), want);
    assert_eq!(production::hash(b"abc"), want);
    let mut hasher = verified::Hasher::new();
    hasher.update(b"a").update(b"bc");
    assert_eq!(hasher.finalize(), want);
}

/// Random messages fed in random pieces, empty ones included, finalized at every step.
#[test]
fn hasher_matches() {
    let mut rng = Rng::new(0x5743_7777);
    for _ in 0..500 {
        let (mut v, mut p) = (verified::Hasher::new(), production::Hasher::new());
        assert_eq!(v.finalize(), p.finalize());
        for _ in 0..(rng.next_u32() % 12) {
            let piece = match rng.next_u32() % 4 {
                0 => 0,
                1 => 64,
                2 => (rng.next_u32() % 70) as usize,
                _ => (rng.next_u32() % 300) as usize,
            };
            let data = random_bytes(&mut rng, piece);
            v.update(&data);
            p.update(&data);
            assert_eq!(v.finalize(), p.finalize());
            assert_eq!(v.clone().finalize(), p.finalize());
        }
    }
}

#[test]
fn zero_prefix_and_continuation_match() {
    let mut rng = Rng::new(0x2E40_7777);
    for z in 0..12 {
        let state = verified::zero_prefix_state(z);
        assert_eq!(state, production::zero_prefix_state(z), "zero prefix {z}");
        for rest_blocks in 1..5 {
            let rest = random_bytes(&mut rng, rest_blocks * 64);
            let t = (z * 64) as u64;
            assert_eq!(
                verified::hash_from_state(&rest, &state, t),
                production::hash_from_state(&rest, &state, t)
            );
        }
    }
    // Arbitrary states and offsets, the counter's high word included.
    for _ in 0..2_000 {
        let state: [u32; 8] = std::array::from_fn(|_| rng.next_u32());
        let t = rng.next_u64() >> (rng.next_u32() % 64);
        let t = t.min(u64::MAX - 1024);
        let n = 64 * (1 + (rng.next_u32() % 8) as usize);
        let rest = random_bytes(&mut rng, n);
        assert_eq!(
            verified::hash_from_state(&rest, &state, t),
            production::hash_from_state(&rest, &state, t)
        );
    }
}
