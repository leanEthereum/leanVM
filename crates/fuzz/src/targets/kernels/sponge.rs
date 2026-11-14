//! `kernel-sponge`: the Fiat-Shamir duplex (`FiatShamirState`, `ProverState`, grinding), `compress`, and the
//! verifier's DA challenge, against a duplex written here from the reference permutation and the module docs.

use super::check;
use super::reference as r;
use crate::{Ctx, Outcome, Source};
use fiat_shamir::transcript::ProverState;
use fiat_shamir::{FiatShamirState, compress, digest_words, merkle::hash_to_scalars};
use primitives::field::{F64, F128};

/// The duplex as `fiat_shamir`'s module docs state it.
#[derive(Clone)]
struct RefSponge {
    state: [u64; 25],
    pending: usize,
}

const OBSERVE: u64 = 1;
const NONCE: u64 = 4;

impl RefSponge {
    fn new(iv: [u64; 4], pi: [u64; 4]) -> Self {
        let mut s = Self {
            state: [0; 25],
            pending: 0,
        };
        s.state[..4].copy_from_slice(&iv);
        s.state[4..8].copy_from_slice(&pi);
        s.duplex();
        s
    }

    /// The permutation's first two lanes as a challenge, its third as the grind's proof of work.
    fn duplex(&mut self) -> (F128, u64) {
        r::keccak_f(&mut self.state);
        let out = (F128::new(self.state[0], self.state[1]), self.state[2]);
        self.state[..16].fill(0);
        self.pending = 0;
        out
    }

    fn sample(&mut self) -> F128 {
        self.duplex().0
    }

    fn absorb(&mut self, x: F128, tag: u64) {
        if self.pending == 4 {
            self.duplex();
        }
        let i = 4 * self.pending;
        self.state[i..i + 4].copy_from_slice(&[x.c0, x.c1, 0, tag]);
        self.pending += 1;
    }

    /// The nonce's permutation clears `bits` low bits of its proof-of-work lane.
    fn grind_ok(&self, nonce: u64, bits: u32) -> bool {
        let mut probe = self.clone();
        probe.absorb(F128::new(nonce, 0), NONCE);
        probe.duplex().1 & ((1u64 << bits) - 1) == 0
    }
}

fn words(digest: &[u8; 32]) -> [u64; 4] {
    std::array::from_fn(|i| u64::from_le_bytes(digest[8 * i..8 * i + 8].try_into().unwrap()))
}

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    match src.below(4) {
        0 => duplex(src, ctx),
        1 => grinding(src, ctx),
        2 => compression(src, ctx),
        _ => da_challenge(src, ctx),
    }
}

fn duplex(src: &mut Source, ctx: &Ctx) -> Outcome {
    let (iv, pi): ([u64; 4], [u64; 4]) = (src.bulk_u64(4).try_into().unwrap(), src.bulk_u64(4).try_into().unwrap());
    let (mut want, mut fs, mut ps);
    if src.chance(1, 4) {
        let n = src.below(300);
        let label = src.bulk(n);
        want = RefSponge::new(words(&r::keccak256(&label)), [0; 4]);
        fs = FiatShamirState::from_label(&label);
        ps = ProverState::from_label(&label);
        ctx.note("from_label");
    } else {
        ctx.note("duplex");
        want = RefSponge::new(iv, pi);
        fs = FiatShamirState::new(iv.map(F64), pi.map(F64));
        ps = ProverState::new(iv.map(F64), pi.map(F64));
    }
    let mut stream = Vec::new();
    for step in 0..src.below(40) {
        match src.below(6) {
            0..=2 => {
                let x = src.f128();
                want.absorb(x, OBSERVE);
                fs.observe(x);
                ps.add_scalar(x);
                stream.push(x);
            }
            3 => {
                let n = src.below(4);
                let got = fs.sample_vec(n);
                let got_ps = ps.sample_vec(n);
                for (i, (&a, &b)) in got.iter().zip(&got_ps).enumerate() {
                    let w = want.sample();
                    check!(
                        a == w,
                        "FiatShamirState sample_vec",
                        "step {step}, challenge {i}: got {a:?}, want {w:?}"
                    );
                    check!(b == w, "ProverState sample_vec", "step {step}, challenge {i}");
                }
            }
            4 => {
                let root: [u8; 32] = src.bulk(32).try_into().unwrap();
                let halves = hash_to_scalars(&root);
                let w = words(&root);
                check!(
                    halves == [F128::new(w[0], w[1]), F128::new(w[2], w[3])],
                    "hash_to_scalars",
                    "{root:02x?}"
                );
                check!(digest_words(&root) == w.map(F64), "digest_words", "{root:02x?}");
                ps.add_root(&root);
                for h in halves {
                    want.absorb(h, OBSERVE);
                    fs.observe(h);
                    stream.push(h);
                }
            }
            _ => {
                let n = src.range(2, 6);
                let coeffs: Vec<F128> = (0..n).map(|_| src.f128()).collect();
                let eq = src.bool();
                ps.add_round_poly(&coeffs, eq);
                for (i, &c) in coeffs.iter().enumerate() {
                    if i != usize::from(!eq) {
                        want.absorb(c, OBSERVE);
                        fs.observe(c);
                        stream.push(c);
                    }
                }
            }
        }
        if want.pending == 0 {
            let cells = fs.capacity_cells();
            let s = want.state;
            let expect = [
                F128::new(s[16], 0),
                F128::new(s[17], s[18]),
                F128::new(s[19], s[20]),
                F128::new(s[21], s[22]),
                F128::new(s[23], s[24]),
            ];
            check!(cells == expect, "capacity_cells", "step {step}");
        }
    }
    let (a, b, w) = (fs.sample(), ps.sample(), want.sample());
    check!(a == w, "FiatShamirState", "final challenge: got {a:?}, want {w:?}");
    check!(b == w, "ProverState", "final challenge: got {b:?}, want {w:?}");
    check!(
        ps.into_proof().stream == stream,
        "ProverState stream",
        "the stream is not what was sent"
    );
    Ok(())
}

/// `grind`: the smallest nonce whose challenge clears `bits` low bits, bound and sent.
fn grinding(src: &mut Source, ctx: &Ctx) -> Outcome {
    let bits = match src.below(8) {
        0 => 0,
        1..=4 => src.range(1, 10) as u32,
        5 | 6 => src.range(11, 14) as u32,
        _ => src.range(15, 17) as u32,
    };
    ctx.note(format!("grind {}", if bits >= 13 { "parallel" } else { "serial" }));
    let iv: [u64; 4] = src.bulk_u64(4).try_into().unwrap();
    let mut want = RefSponge::new(iv, [0; 4]);
    let mut ps = ProverState::new(iv.map(F64), [F64::ZERO; 4]);
    let before = src.below(6);
    for _ in 0..before {
        let x = src.f128();
        want.absorb(x, OBSERVE);
        ps.add_scalar(x);
    }
    ps.grind(bits);
    let proof = ps.into_proof();
    if bits == 0 {
        check!(
            proof.stream.len() == before,
            "ProverState grind",
            "bits 0 must send nothing"
        );
        return Ok(());
    }
    let Some(&nonce) = proof.stream.last() else {
        return Err(super::mismatch("ProverState grind", "no nonce on the stream"));
    };
    check!(
        nonce.c1 == 0,
        "ProverState grind",
        "nonce {nonce:?} is not a u64"
    );
    let n = nonce.c0;
    check!(
        want.grind_ok(n, bits),
        "ProverState grind",
        "nonce {n} does not clear {bits} bits"
    );
    // Minimality: the reference permutation is slow, so look only below a bound.
    let below = n.min(1 << 12);
    if let Some(smaller) = (0..below).find(|&m| want.grind_ok(m, bits)) {
        return Err(super::mismatch(
            "ProverState grind",
            format!("nonce {n} for {bits} bits, but {smaller} also clears them: grinding must pick the smallest"),
        ));
    }
    // After the grind the state has absorbed the nonce; the permutation it forces is what
    // `ground` hands to the next sample, so the ref duplexes once, on the check itself.
    want.absorb(F128::new(n, 0), NONCE);
    let mut after = ProverState::new(iv.map(F64), [F64::ZERO; 4]);
    for &x in &proof.stream[..proof.stream.len() - 1] {
        after.add_scalar(x);
    }
    after.grind(bits);
    check!(
        after.sample() == want.sample(),
        "ProverState grind",
        "the challenge after the grind"
    );
    Ok(())
}

fn compression(src: &mut Source, ctx: &Ctx) -> Outcome {
    ctx.note("compress");
    let (a, b): ([u64; 4], [u64; 4]) = (src.bulk_u64(4).try_into().unwrap(), src.bulk_u64(4).try_into().unwrap());
    let a = if src.chance(1, 8) { [u64::MAX; 4] } else { a };
    let got = compress(a.map(F64), b.map(F64));
    let got_vm = leanvm_core::vmhash::compress(a.map(F64), b.map(F64));
    let bytes = r::words_le(&[a, b].concat());
    let want = words(&r::keccak256(&bytes)).map(F64);
    check!(got == want, "fiat_shamir::compress", "{a:x?} {b:x?}");
    check!(got_vm == want, "vmhash::compress", "{a:x?} {b:x?}");
    // One VM KECCAK from the zero state: the 64 bytes, the padding, one permutation.
    let mut state = [0u64; 25];
    state[..8].copy_from_slice(&[a, b].concat());
    state[8] ^= 1;
    state[16] ^= 0x80 << 56;
    r::keccak_f(&mut state);
    check!(
        got.map(|w| w.0) == state[..4],
        "fiat_shamir::compress",
        "not one permutation of the padded halves"
    );
    Ok(())
}

/// `verifier::da`: `z` is the duplex seeded with the label's hash and the root, squeezed once; the digest is
/// `H(root || z || 0)`.
fn da_challenge(src: &mut Source, ctx: &Ctx) -> Outcome {
    ctx.note("da challenge");
    let root: [u8; 32] = if src.chance(1, 8) {
        [0; 32]
    } else {
        src.bulk(32).try_into().unwrap()
    };
    let mut want = RefSponge::new(words(&r::keccak256(b"leanDA/rs-membership/v1")), words(&root));
    // The challenge's derivation grinds: the smallest nonce whose permutation clears `bits` low bits of the
    // proof-of-work lane, `bits = grinding_bits(2^14 - 1)` for a blob's `k - 1` bad values of `z`.
    let bits = 11u32;
    let n = (0..).find(|&n| want.grind_ok(n, bits)).expect("a nonce exists");
    want.absorb(F128::new(n, 0), NONCE);
    let z = want.sample();
    let got = verifier::da::membership_challenge(&root);
    check!(
        (got.c0, got.c1) == (z.c0, z.c1),
        "verifier::da::membership_challenge",
        "root {root:02x?}"
    );
    let mut fs = FiatShamirState::new(
        digest_words(&r::keccak256(b"leanDA/rs-membership/v1")),
        digest_words(&root),
    );
    check!(
        fs.grind(bits) == Some(n) && fs.sample() == z,
        "FiatShamirState",
        "the prover's grind does not give the DA challenge of the verifier's sponge"
    );
    let tail: Vec<u8> = [z.c0, z.c1, 0, 0].iter().flat_map(|w| w.to_le_bytes()).collect();
    let digest = r::hash_pair(&root, &tail.try_into().unwrap());
    check!(
        verifier::da::digest(Some(root)) == digest,
        "verifier::da::digest",
        "root {root:02x?}"
    );
    check!(
        verifier::da::digest(None) == [0; 32],
        "verifier::da::digest",
        "no root must give zeros"
    );
    Ok(())
}
