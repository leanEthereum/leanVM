//! The verified NTT pieces against `pcs::ntt::AdditiveNttF64`.
//!
//! The table, `span_get`, `twiddle`, `twiddles_radix8`, the butterflies and the fused row groups are
//! private in production, so they are checked through the public encoder: the verified scalar reference,
//! and a small driver built from the verified radix-8/radix-4 groups, must both reproduce
//! `encode_interleaved_in_place` word for word.
use leanvm_verus::gf2_64::F64 as VF64;
use leanvm_verus::ntt as verified;
use pcs::ntt::AdditiveNttF64 as Production;
use primitives::field::F64;
use primitives::test_util::Rng;

fn random(rng: &mut Rng, n: usize) -> Vec<F64> {
    (0..n).map(|_| F64(rng.next_u64())).collect()
}

fn to_verified(v: &[F64]) -> Vec<VF64> {
    v.iter().map(|x| VF64(x.0)).collect()
}

fn from_verified(v: &[VF64]) -> Vec<F64> {
    v.iter().map(|x| F64(x.0)).collect()
}

#[test]
fn forward_reference_matches_encoder() {
    // Every lane count encodes `lanes` independent transforms; the domain size is the table's.
    let mut rng = Rng::new(0x4E77);
    for log_d in 1..=12usize {
        for lanes in [1usize, 2, 3, 5, 8] {
            let msg = random(&mut rng, lanes << log_d);
            let mut want = to_verified(&msg);
            verified::forward_scalar_from_layer(&verified::AdditiveNttF64::standard(log_d), &mut want, lanes, 0);
            let mut got = msg;
            Production::standard(log_d).encode_interleaved_in_place(&mut got, lanes, 0);
            assert_eq!(got, from_verified(&want), "log_d={log_d}, lanes={lanes}");
        }
    }
}

#[test]
fn forward_reference_matches_encoder_at_a_rate() {
    // The encoder reads the message from the first replica; the reference replicates it, then runs the
    // layers from the rate layer on.
    let mut rng = Rng::new(0x4A7E);
    for (log_d, lanes, log_inv_rate) in [(3usize, 1usize, 1usize), (6, 3, 2), (9, 8, 1), (10, 2, 3), (12, 4, 2), (4, 8, 4)] {
        let msg_len = (lanes << log_d) >> log_inv_rate;
        let msg = random(&mut rng, msg_len);
        let mut want: Vec<VF64> = to_verified(&msg).repeat(1 << log_inv_rate);
        verified::forward_scalar_from_layer(&verified::AdditiveNttF64::standard(log_d), &mut want, lanes, log_inv_rate);
        let mut got = vec![F64::ZERO; msg_len << log_inv_rate];
        got[..msg_len].copy_from_slice(&msg);
        Production::standard(log_d).encode_interleaved_in_place(&mut got, lanes, log_inv_rate);
        assert_eq!(got, from_verified(&want), "log_d={log_d}, lanes={lanes}, rate={log_inv_rate}");
    }
}

#[test]
fn inverse_matches_production_and_undoes_the_forward_reference() {
    let mut rng = Rng::new(0x1A7F);
    for dim in [1usize, 4, 9, 12] {
        let (ours, theirs) = (verified::AdditiveNttF64::standard(dim), Production::standard(dim));
        for log_d in 0..=dim {
            for _ in 0..4 {
                let orig = random(&mut rng, 1 << log_d);
                let mut want = to_verified(&orig);
                ours.inverse_transform(&mut want);
                let mut got = orig.clone();
                theirs.inverse_transform(&mut got);
                assert_eq!(got, from_verified(&want), "dim={dim}, log_d={log_d}");

                if log_d == dim {
                    let mut back = to_verified(&orig);
                    verified::forward_scalar_from_layer(&ours, &mut back, 1, 0);
                    ours.inverse_transform(&mut back);
                    assert_eq!(from_verified(&back), orig, "roundtrip dim={dim}");
                }
            }
        }
    }
}

/// One single-lane transform built from the verified fused groups, planned as `run_layers` plans a
/// single sweep: three layers at a time while blocks span at least 8 rows, then two, then one.
fn fused_forward(ntt: &verified::AdditiveNttF64, data: &mut [VF64]) {
    let log_d = verified::log2_strict_usize(data.len());
    let mut layer = 0;
    while layer < log_d {
        let num_blocks = 1usize << layer;
        let block_size = 1usize << (log_d - layer);
        if layer + 2 < log_d && block_size >= 8 {
            let eighth = block_size >> 3;
            for block in 0..num_blocks {
                let t = ntt.twiddles_radix8(layer, block);
                for r in 0..eighth {
                    let at = |k: usize| block * block_size + r + k * eighth;
                    let mut rows = [0, 1, 2, 3, 4, 5, 6, 7].map(|k| data[at(k)]);
                    verified::radix8_butterflies(&mut rows, &t);
                    for (k, v) in rows.into_iter().enumerate() {
                        data[at(k)] = v;
                    }
                }
            }
            layer += 3;
        } else if layer + 1 < log_d && block_size >= 4 {
            let quarter = block_size >> 2;
            for block in 0..num_blocks {
                let (t_outer, t_inner_a, t_inner_b) =
                    (ntt.twiddle(layer, block), ntt.twiddle(layer + 1, 2 * block), ntt.twiddle(layer + 1, 2 * block + 1));
                for r in 0..quarter {
                    let at = |k: usize| block * block_size + r + k * quarter;
                    let mut rows = [0, 1, 2, 3].map(|k| data[at(k)]);
                    verified::radix4_butterflies(&mut rows, t_outer, t_inner_a, t_inner_b);
                    for (k, v) in rows.into_iter().enumerate() {
                        data[at(k)] = v;
                    }
                }
            }
            layer += 2;
        } else {
            let half = block_size >> 1;
            for block in 0..num_blocks {
                let twiddle = ntt.twiddle(layer, block);
                let (top, bot) = data[block * block_size..(block + 1) * block_size].split_at_mut(half);
                verified::butterfly_lanes(top, bot, twiddle);
            }
            layer += 1;
        }
    }
}

#[test]
fn fused_groups_match_encoder() {
    let mut rng = Rng::new(0xF05E);
    for log_d in 1..=13usize {
        for _ in 0..4 {
            let msg = random(&mut rng, 1 << log_d);
            let ntt = verified::AdditiveNttF64::standard(log_d);
            let mut fused = to_verified(&msg);
            fused_forward(&ntt, &mut fused);
            let mut scalar = to_verified(&msg);
            verified::forward_scalar_from_layer(&ntt, &mut scalar, 1, 0);
            let mut got = msg;
            Production::standard(log_d).encode_interleaved_in_place(&mut got, 1, 0);
            assert_eq!(got, from_verified(&fused), "fused, log_d={log_d}");
            assert_eq!(got, from_verified(&scalar), "scalar, log_d={log_d}");
        }
    }
}

#[test]
fn transposed_butterfly_matches_its_formula() {
    // Production's transposed lane butterfly is crate-private and reached only through the WHIR prover,
    // so the verified one is checked against its documented formula in the production field:
    // s = u + v; new_u = s; new_v = v + s*t.
    let mut rng = Rng::new(0x7A5);
    for _ in 0..10_000 {
        let (u, v, t) = (F64(rng.next_u64()), F64(rng.next_u64()), F64(rng.next_u64()));
        let s = u + v;
        let (mut top, mut bot) = ([VF64(u.0)], [VF64(v.0)]);
        verified::transposed_butterfly_lanes(&mut top, &mut bot, VF64(t.0));
        assert_eq!((top[0].0, bot[0].0), (s.0, (v + s * t).0));
    }
}

#[test]
fn log2_matches_production() {
    for k in 0..usize::BITS as usize {
        assert_eq!(verified::log2_strict_usize(1 << k), primitives::log2_strict_usize(1 << k));
    }
}
