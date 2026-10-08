//! The verified GF(2^8) NTT and LDE table against flock's `zerocheck/ntt.rs` and `zerocheck/ntt/inv_table.rs`.
//!
//! Everything there is `pub(crate)` and flock exports no path to it, so the two production source files are
//! compiled into this test binary as a module of their own (the `#[path]` module below) and called directly:
//! the code under test is production's, byte for byte. Their own `#[cfg(test)]` tests come along and run here
//! too.
//!
//! The twiddle table is private to its struct, so it is checked through `forward` and `inverse`, which read
//! every entry; the LDE table is private too, so it is checked through `apply_scalar` on every single-byte row
//! (which reads one table row) and on random rows, and the dispatched `apply` (the SIMD arms on this machine)
//! against the verified `apply_scalar`.
use leanvm_verus::flock_ntt as verified;
use leanvm_verus::gf2_8::F8 as VF8;
use primitives::field::F8;
use primitives::test_util::Rng;

#[allow(dead_code, clippy::all)]
#[path = "../../../../crates/flock/src/zerocheck"]
mod production {
    pub mod ntt;
}

use production::ntt::{AdditiveNttGf8 as Production, InvNttTableByteSingleGf8 as ProductionTable};

fn random(rng: &mut Rng, n: usize) -> Vec<F8> {
    (0..n).map(|_| F8(rng.next_u8())).collect()
}

fn to_verified(v: &[F8]) -> Vec<VF8> {
    v.iter().map(|x| VF8(x.0)).collect()
}

fn from_verified(v: &[VF8]) -> Vec<F8> {
    v.iter().map(|x| F8(x.0)).collect()
}

#[test]
fn forward_and_inverse_match_production() {
    // Every domain size up to the whole field, every offset, a few vectors each, and the unit vectors.
    let mut rng = Rng::new(0xF8_0717);
    for k in 0..=8usize {
        for beta in 0..=255u8 {
            let (ours, theirs) = (
                verified::AdditiveNttGf8::new(k, VF8(beta)),
                Production::new(k, F8(beta)),
            );
            assert_eq!(ours.k(), theirs.k());
            let mut inputs: Vec<Vec<F8>> = (0..2).map(|_| random(&mut rng, 1 << k)).collect();
            if beta % 51 == 0 {
                for t in 0..1usize << k {
                    let mut e = vec![F8::ZERO; 1 << k];
                    e[t] = F8::ONE;
                    inputs.push(e);
                }
            }
            for v in inputs {
                let mut want = to_verified(&v);
                ours.forward(&mut want);
                let mut got = v.clone();
                theirs.forward(&mut got);
                assert_eq!(got, from_verified(&want), "forward k={k}, beta={beta:#04x}");

                let mut want = to_verified(&v);
                ours.inverse(&mut want);
                let mut got = v.clone();
                theirs.inverse(&mut got);
                assert_eq!(got, from_verified(&want), "inverse k={k}, beta={beta:#04x}");
            }
        }
    }
}

#[test]
fn lde_table_matches_production() {
    // The protocol's pair (S at 0, Λ at 2^k), and random offsets, at every size the table accepts.
    let mut rng = Rng::new(0x1DE7);
    for k in 3..=7usize {
        let ell = 1usize << k;
        let mut pairs = vec![(0u8, 1u8 << k)];
        pairs.extend((0..6).map(|_| (rng.next_u8(), rng.next_u8())));
        for (beta_s, beta_l) in pairs {
            let ours = verified::InvNttTableByteSingleGf8::new(
                &verified::AdditiveNttGf8::new(k, VF8(beta_s)),
                &verified::AdditiveNttGf8::new(k, VF8(beta_l)),
            );
            let theirs = ProductionTable::new(&Production::new(k, F8(beta_s)), &Production::new(k, F8(beta_l)));
            assert_eq!(
                (ours.k, ours.ell, ours.n_chunks),
                (theirs.k, theirs.ell, theirs.n_chunks)
            );

            let mut rows: Vec<Vec<u8>> = Vec::new();
            // Single-byte rows: byte `w` at chunk `b`, every `w` and `b`, so every table row at every shift.
            for b in 0..ell / 8 {
                for w in 0..=255u8 {
                    let mut bytes = vec![0u8; ell / 8];
                    bytes[b] = w;
                    rows.push(bytes);
                }
            }
            rows.extend((0..256).map(|_| (0..ell / 8).map(|_| rng.next_u8()).collect()));
            rows.push(vec![0xFF; ell / 8]);

            for bytes in rows {
                let mut want = vec![VF8(0); ell];
                ours.apply_scalar(&bytes, &mut want);
                let want = from_verified(&want);
                let mut got = vec![F8::ZERO; ell];
                theirs.apply_scalar(&bytes, &mut got);
                assert_eq!(
                    got, want,
                    "apply_scalar k={k}, betas=({beta_s:#04x}, {beta_l:#04x}), bytes={bytes:02x?}"
                );
                let mut got = vec![F8::ZERO; ell];
                theirs.apply(&bytes, &mut got);
                assert_eq!(
                    got, want,
                    "apply k={k}, betas=({beta_s:#04x}, {beta_l:#04x}), bytes={bytes:02x?}"
                );
            }
        }
    }
}
