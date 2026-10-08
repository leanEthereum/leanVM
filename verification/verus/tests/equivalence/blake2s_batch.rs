use leanvm_verus::blake2s as scalar;
use leanvm_verus::blake2s_batch::{self as verified, Lanes32, Scalar8};
use primitives::hash as production;
use primitives::test_util::Rng;

/// The production walk's layout, written plainly: input `g * 8 + l` of a set is lane `l` of group `g`, its block `b`
/// transposed word by word, every lane starting from `state`, digests written back lane by lane.
fn hash_set_with_verified_compression<const G: usize>(
    data: &[u8],
    len: usize,
    state: &[u32; 8],
    t_offset: u64,
) -> Vec<u8> {
    let n_blocks = len / 64;
    let mut h: [[Scalar8; 8]; G] = [verified::transpose_words(&[*state; 8]); G];
    for b in 0..n_blocks {
        let blocks: [[Scalar8; 16]; G] = std::array::from_fn(|g| {
            let rows: [[u32; 16]; 8] = std::array::from_fn(|l| {
                std::array::from_fn(|w| {
                    let at = (g * 8 + l) * len + b * 64 + 4 * w;
                    u32::from_le_bytes(data[at..at + 4].try_into().unwrap())
                })
            });
            verified::transpose_words(&rows)
        });
        let m: [&[Scalar8; 16]; G] = std::array::from_fn(|g| &blocks[g]);
        let t = t_offset + ((b + 1) * 64) as u64;
        verified::compress_groups::<Scalar8, G>(&mut h, m, t, b + 1 == n_blocks);
    }
    let mut out = vec![0u8; G * 8 * 32];
    for g in 0..G {
        let digests = verified::store_digests(&h[g]);
        for l in 0..8 {
            let at = (g * 8 + l) * 32;
            out[at..at + 32].copy_from_slice(&digests[l]);
        }
    }
    out
}

/// Production's batched path is private: the verified `compress_groups` (portable backend, 1, 2 and 4 groups), in a
/// plain transposing walk, is compared with production's public batched hash, whichever backend this target
/// dispatches to, on fresh and continued states.
#[test]
fn batched_hash_matches_production() {
    fn check<const G: usize>(rng: &mut Rng) {
        for len in [64usize, 128, 192, 640] {
            for continued in [false, true] {
                let (state, t_offset) = if continued {
                    let z = (rng.next_u32() % 4) as usize;
                    (production::zero_prefix_state(z), (z * 64) as u64)
                } else {
                    (production::PARAM_IV, 0)
                };
                let n = G * 8;
                let data: Vec<u8> = (0..n * len).map(|_| rng.next_u8()).collect();
                let mut want = vec![0u8; n * 32];
                production::hash_many_dyn_from_state(&data, len, &state, t_offset, &mut want);
                let got = hash_set_with_verified_compression::<G>(&data, len, &state, t_offset);
                assert_eq!(got, want, "G {G} len {len} continued {continued}");
            }
        }
    }
    let mut rng = Rng::new(0xBA7C_7777);
    for _ in 0..20 {
        check::<1>(&mut rng);
        check::<2>(&mut rng);
        check::<4>(&mut rng);
    }
}

/// Lane by lane, the batched compression is the verified scalar `compress` (itself checked against production), on
/// arbitrary transposed states and blocks, both counter halves and both flags.
#[test]
fn compress_groups_is_lanewise_compress() {
    let mut rng = Rng::new(0x1A2E_7777);
    for i in 0..2_000 {
        let states: [[[u32; 8]; 8]; 2] =
            std::array::from_fn(|_| std::array::from_fn(|_| std::array::from_fn(|_| rng.next_u32())));
        let messages: [[[u32; 16]; 8]; 2] =
            std::array::from_fn(|_| std::array::from_fn(|_| std::array::from_fn(|_| rng.next_u32())));
        let h = states.map(|rows| verified::transpose_words(&rows));
        let blocks = messages.map(|rows| verified::transpose_words(&rows));
        let counters = [0, 64, u32::MAX as u64, 1 << 32, (1 << 32) + 64, u64::MAX];
        let t = if i < counters.len() * 2 {
            counters[i / 2]
        } else {
            rng.next_u64()
        };
        let last = i % 2 == 0;
        let mut got = h;
        verified::compress_groups::<Scalar8, 2>(&mut got, [&blocks[0], &blocks[1]], t, last);
        let mut one = [h[1]];
        verified::compress_groups::<Scalar8, 1>(&mut one, [&blocks[1]], t, last);
        let row_digests = verified::compress_rows(&states[1], &messages[1], t, last);
        for g in 0..2 {
            let digests = verified::store_digests(&got[g]);
            for l in 0..8 {
                let mut want = states[g][l];
                let m = messages[g][l];
                scalar::compress(&mut want, &m, t, last);
                assert_eq!(
                    std::array::from_fn::<u32, 8, _>(|w| got[g][w].0[l]),
                    want,
                    "group {g} lane {l}"
                );
                assert_eq!(digests[l], scalar::state_bytes(&want), "scatter group {g} lane {l}");
                if g == 1 {
                    assert_eq!(row_digests[l], digests[l], "composed layout lane {l}");
                }
            }
        }
        for w in 0..8 {
            assert_eq!(one[0][w].0, got[1][w].0, "one group against two, word {w}");
        }
    }
}

/// The portable lane arithmetic, against the scalar operations it maps.
#[test]
fn scalar8_lanes_match() {
    let mut rng = Rng::new(0x5CA8_7777);
    for _ in 0..10_000 {
        let a = Scalar8(std::array::from_fn(|_| rng.next_u32()));
        let b = Scalar8(std::array::from_fn(|_| rng.next_u32()));
        let x = rng.next_u32();
        for l in 0..8 {
            assert_eq!(a.add(b).0[l], a.0[l].wrapping_add(b.0[l]));
            assert_eq!(a.xor(b).0[l], a.0[l] ^ b.0[l]);
            assert_eq!(a.rotr::<16>().0[l], a.0[l].rotate_right(16));
            assert_eq!(a.rotr::<12>().0[l], a.0[l].rotate_right(12));
            assert_eq!(a.rotr::<8>().0[l], a.0[l].rotate_right(8));
            assert_eq!(a.rotr::<7>().0[l], a.0[l].rotate_right(7));
            assert_eq!(Scalar8::splat(x).0[l], x);
        }
    }
}
