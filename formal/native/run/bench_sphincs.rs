//! Microbenchmark comparing `lean_sphincs::verify` against the proved assembly `sphincs_verify`.
//!
//! Invoked by `formal/native/run/bench-sphincs.sh`. Runs only accepted (valid) signatures across
//! multiple distinct keys and messages so the verifier never bails early on WOTS+C codeword checks.

use std::hint::black_box;
use std::time::Instant;

#[cfg(not(feature = "proved_asm"))]
use lean_sphincs::{LeanSphincsPublicKey, LeanSphincsSignature};
use lean_sphincs::{PUB_KEY_SIZE, SIG_SIZE};

#[cfg(feature = "proved_asm")]
unsafe extern "C" {
    fn sphincs_verify(pk: *const [u8; PUB_KEY_SIZE], msg: *const [u8; 32], sig: *const [u8; SIG_SIZE]) -> u64;
}

const CASES: usize = 8;
const WARMUP: usize = 100;
const ITERS: usize = 2000;

struct Case {
    pk_bytes: [u8; PUB_KEY_SIZE],
    msg: [u8; 32],
    sig_bytes: [u8; SIG_SIZE],
    #[cfg(not(feature = "proved_asm"))]
    pk: LeanSphincsPublicKey,
    #[cfg(not(feature = "proved_asm"))]
    sig: LeanSphincsSignature,
}

fn make_cases() -> Vec<Case> {
    (0..CASES)
        .map(|i| {
            let mut seed = [0u8; 32];
            seed[0] = (i as u8).wrapping_mul(17).wrapping_add(1);
            seed[31] = i as u8;
            let mut msg = [0u8; 32];
            msg[0] = (i as u8).wrapping_mul(31).wrapping_add(7);
            msg[15] = (i as u8) ^ 0x5a;
            let pk = lean_sphincs::key_gen(&seed);
            let sig = lean_sphincs::sign(&seed, &msg);
            let pk_bytes = pk.to_bytes();
            let sig_bytes = sig.to_bytes();
            assert!(lean_sphincs::verify(&pk, &msg, &sig), "case {i} must be valid");
            #[cfg(feature = "proved_asm")]
            {
                let ok = unsafe { sphincs_verify(&pk_bytes, &msg, &sig_bytes) };
                assert_eq!(ok, 1, "proved sphincs_verify rejected valid case {i}");
            }
            Case {
                pk_bytes,
                msg,
                sig_bytes,
                #[cfg(not(feature = "proved_asm"))]
                pk,
                #[cfg(not(feature = "proved_asm"))]
                sig,
            }
        })
        .collect()
}

fn measure(label: &str, mut f: impl FnMut(usize) -> bool) {
    for i in 0..WARMUP {
        assert!(f(i % CASES), "{label}: warmup case rejected");
    }
    let t0 = Instant::now();
    let mut accepted = 0usize;
    for i in 0..ITERS {
        if black_box(f(i % CASES)) {
            accepted += 1;
        }
    }
    let dt = t0.elapsed();
    assert_eq!(accepted, ITERS, "{label}: expected every measured signature to verify");
    let us = dt.as_secs_f64() * 1e6 / ITERS as f64;
    println!("  {label:<32} {:7.2} us/op  ({:6.0} verif/s)", us, 1e6 / us);
}

fn main() {
    let cases = make_cases();

    #[cfg(not(feature = "proved_asm"))]
    {
        measure("rust verify (with from_bytes)", |i| {
            let c = &cases[i];
            let p = LeanSphincsPublicKey::from_bytes(black_box(&c.pk_bytes));
            let s = LeanSphincsSignature::from_bytes(black_box(&c.sig_bytes));
            lean_sphincs::verify(&p, black_box(&c.msg), &s)
        });
        measure("rust verify (pre-parsed)", |i| {
            let c = &cases[i];
            lean_sphincs::verify(black_box(&c.pk), black_box(&c.msg), black_box(&c.sig))
        });
    }

    #[cfg(feature = "proved_asm")]
    {
        measure("proved asm (raw byte pointers)", |i| {
            let c = &cases[i];
            unsafe { sphincs_verify(black_box(&c.pk_bytes), black_box(&c.msg), black_box(&c.sig_bytes)) == 1 }
        });
    }
}
