//! The guest against NIST's ACVP sigVer vectors and, on random keys, messages and corruptions, against RustCrypto's
//! `ml-dsa`; and one claim proven and verified end to end.

use ml_dsa::{EncodedSignature, EncodedVerifyingKey, Keypair, MlDsa44, MlDsa65, MlDsa87, MlDsaParams, Signature};
use ml_dsa::{SigningKey, VerifyingKey};
use ml_dsa_guest::{Claim, ML_DSA_44, ML_DSA_65, ML_DSA_87, Params, fips};
use stable_lean_vm_core::cpu::{execute, from_scalar};

const SETS: [Params; 3] = [ML_DSA_44, ML_DSA_65, ML_DSA_87];

/// Whether the guest accepts the claims: they have a witness, and the run on it succeeds.
fn guest_accepts(program: &isa::Program, p: &Params, claims: &[Claim]) -> bool {
    let Ok(witness) = ml_dsa_guest::witness(p, claims) else {
        return false;
    };
    let witness: Vec<_> = witness
        .into_iter()
        .map(|(name, entries)| {
            let entries = entries.into_iter().map(|e| e.into_iter().map(from_scalar).collect());
            (name, entries.collect())
        })
        .collect();
    let pi = ml_dsa_guest::public_input(claims).map(from_scalar);
    execute(program, &witness, pi).is_ok()
}

/// RustCrypto's verdict on a claim.
fn reference_accepts<P: MlDsaParams>(claim: &Claim) -> bool {
    let (Ok(pk), Ok(sig)) = (
        EncodedVerifyingKey::<P>::try_from(&claim.pk[..]),
        EncodedSignature::<P>::try_from(&claim.sig[..]),
    ) else {
        return false;
    };
    let Some(sig) = Signature::<P>::decode(&sig) else {
        return false;
    };
    VerifyingKey::<P>::decode(&pk).verify_mu(&claim.mu.into(), &sig)
}

fn reference(p: &Params, claim: &Claim) -> bool {
    match p.k {
        4 => reference_accepts::<MlDsa44>(claim),
        6 => reference_accepts::<MlDsa65>(claim),
        _ => reference_accepts::<MlDsa87>(claim),
    }
}

fn sign<P: MlDsaParams>(seed: [u8; 32], msg: &[u8], ctx: &[u8]) -> Claim {
    let sk = SigningKey::<P>::from_seed(&seed.into());
    let pk = sk.verifying_key().encode().to_vec();
    let sig = sk
        .expanded_key()
        .sign_deterministic(msg, ctx)
        .unwrap()
        .encode()
        .to_vec();
    Claim {
        mu: fips::mu(&pk, msg, ctx),
        pk,
        sig,
    }
}

fn signed(p: &Params, seed: [u8; 32], msg: &[u8], ctx: &[u8]) -> Claim {
    match p.k {
        4 => sign::<MlDsa44>(seed, msg, ctx),
        6 => sign::<MlDsa65>(seed, msg, ctx),
        _ => sign::<MlDsa87>(seed, msg, ctx),
    }
}

fn hex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

#[test]
fn acvp_sigver() {
    let vectors = include_str!("acvp/sigver.txt");
    for p in SETS {
        let program = ml_dsa_guest::program(&p, 1);
        let set = p.name.trim_start_matches("ML-DSA-");
        let mut n = 0;
        for line in vectors.lines().filter(|l| l.split(' ').next() == Some(set)) {
            let f: Vec<&str> = line.split(' ').collect();
            let passed = f[2] == "1";
            let claim = Claim {
                pk: hex(f[3]),
                mu: hex(f[4]).try_into().unwrap(),
                sig: hex(f[5]),
            };
            assert_eq!(reference(&p, &claim), passed, "{} tcId {}: the reference", p.name, f[1]);
            assert_eq!(
                guest_accepts(&program, &p, &[claim]),
                passed,
                "{} tcId {}",
                p.name,
                f[1]
            );
            n += 1;
        }
        assert_eq!(n, 20, "{}: vectors", p.name);
    }
}

/// A splitmix64 stream, so the cases are the same on every run.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    fn bytes<const N: usize>(&mut self) -> [u8; N] {
        std::array::from_fn(|_| self.next() as u8)
    }
}

/// Random keys and messages, each signature as signed and with one bit flipped in its key, `mu` or signature (in
/// its `c~`, its `z` or its hint), the guest agreeing with the reference on every one.
#[test]
fn differential() {
    let mut rng = Rng(0x6d6c_2d64_7361);
    for p in SETS {
        let program = ml_dsa_guest::program(&p, 1);
        let (ct, z_end) = (p.ctilde_bytes(), p.sig_bytes() - p.omega - p.k);
        let (mut accepted, mut rejected) = (0, 0);
        for _ in 0..3 {
            let msg: Vec<u8> = (0..rng.below(200)).map(|_| rng.next() as u8).collect();
            let ctx: Vec<u8> = (0..rng.below(8)).map(|_| rng.next() as u8).collect();
            let valid = signed(&p, rng.bytes(), &msg, &ctx);
            let mut cases = vec![valid.clone()];
            for target in 0..5 {
                let mut c = valid.clone();
                let bit = 1 << rng.below(8);
                match target {
                    0 => c.pk[rng.below(p.pk_bytes())] ^= bit,
                    1 => c.mu[rng.below(64)] ^= bit,
                    2 => c.sig[rng.below(ct)] ^= bit,
                    3 => c.sig[ct + rng.below(z_end - ct)] ^= bit,
                    _ => c.sig[z_end + rng.below(p.omega + p.k)] ^= bit,
                }
                cases.push(c);
            }
            for c in cases {
                let want = reference(&p, &c);
                assert_eq!(
                    guest_accepts(&program, &p, std::slice::from_ref(&c)),
                    want,
                    "{}",
                    p.name
                );
                if want { accepted += 1 } else { rejected += 1 }
            }
        }
        assert!(
            accepted >= 3 && rejected >= 9,
            "{}: {accepted} accepted, {rejected} rejected",
            p.name
        );
    }
}

/// Every stream of advice is pinned: one value nudged anywhere in it, the run on a valid claim fails. A g-power
/// moves one step along the exponent, a lane or a flag flips its low bit.
#[test]
fn every_hint_is_checked() {
    let p = ML_DSA_44;
    let program = ml_dsa_guest::program(&p, 1);
    let claim = signed(&p, [3; 32], b"pinned", b"");
    let honest = ml_dsa_guest::witness(&p, std::slice::from_ref(&claim)).unwrap();
    let pi = ml_dsa_guest::public_input(std::slice::from_ref(&claim)).map(from_scalar);
    let run = |w: &[(String, Vec<Vec<verifier::E>>)]| {
        let w: Vec<_> = w
            .iter()
            .map(|(n, es)| {
                (
                    n.clone(),
                    es.iter()
                        .map(|e| e.iter().copied().map(from_scalar).collect())
                        .collect(),
                )
            })
            .collect();
        execute(&program, &w, pi).is_ok()
    };
    assert!(run(&honest));
    let mut rng = Rng(5);
    for (s, (name, entries)) in honest.iter().enumerate() {
        for _ in 0..3 {
            let mut w = honest.clone();
            let (e, v) = (rng.below(entries.len()), rng.below(entries[0].len()));
            let x = &mut w[s].1[e][v];
            *x = match name.as_str() {
                "rho" | "mu" | "ct" | "exr" | "sibf" => *x + verifier::E::new(1, 0),
                _ => *x * verifier::E::new(2, 0),
            };
            assert!(!run(&w), "stream {name}, entry {e}, value {v} is unchecked");
        }
    }
}
