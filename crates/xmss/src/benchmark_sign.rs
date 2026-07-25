use std::hint::black_box;
use std::time::Instant;

use backend::PrimeCharacteristicRing;

use crate::wots::wots_encode;
use crate::{
    CHAIN_LENGTH, F, MESSAGE_LEN_BYTES, Randomness, TARGET_SUM, V, hash_message, xmss_key_gen_from_seed, xmss_sign,
    xmss_verify,
};

const SEED: [u8; 32] = [7u8; 32];
const ACTIVATION_SLOT: u64 = 1 << 20;
const NUM_ACTIVE_SLOTS: u64 = 1 << 10;

/// Signing and verification throughput.
///
/// cargo test --release --package xmss --lib -- benchmark_sign::bench_sign --exact --nocapture --ignored
#[test]
#[ignore]
fn bench_sign() {
    const WARMUP: u32 = 64;
    const SAMPLES: u32 = 512;

    let (pk, sk) = xmss_key_gen_from_seed(SEED, ACTIVATION_SLOT, NUM_ACTIVE_SLOTS).unwrap();
    let message: [u8; MESSAGE_LEN_BYTES] = std::array::from_fn(|i| i as u8);

    for i in 0..WARMUP {
        let slot = (ACTIVATION_SLOT + u64::from(i)) as u32;
        let _ = black_box(xmss_sign(&sk, slot, &message).unwrap());
    }

    let time = Instant::now();
    for i in 0..SAMPLES {
        let slot = (ACTIVATION_SLOT + u64::from(WARMUP + i)) as u32;
        let _ = black_box(xmss_sign(&sk, slot, &message).unwrap());
    }
    let sign_elapsed = time.elapsed();

    let slot = (ACTIVATION_SLOT + u64::from(WARMUP)) as u32;
    let signature = xmss_sign(&sk, slot, &message).unwrap();
    assert!(xmss_verify(&pk, slot, &message, &signature).is_ok());

    let time = Instant::now();
    for _ in 0..SAMPLES {
        let _ = black_box(xmss_verify(&pk, slot, &message, &signature));
    }
    let verify_elapsed = time.elapsed();

    println!(
        "xmss_sign  : {:>9.1} us/op ({:.0} sig/s)",
        sign_elapsed.as_secs_f64() * 1e6 / f64::from(SAMPLES),
        f64::from(SAMPLES) / sign_elapsed.as_secs_f64()
    );
    println!(
        "xmss_verify: {:>9.1} us/op",
        verify_elapsed.as_secs_f64() * 1e6 / f64::from(SAMPLES)
    );
    println!(
        "chain hashes: {TARGET_SUM} walked per signature, {} in a full WOTS public key",
        V * (CHAIN_LENGTH - 1)
    );
}

/// Per-attempt cost of the loop that grinds randomness until the codeword hits `TARGET_SUM`.
/// The accepted-codeword count doubles as a check that the encoding itself did not change.
///
/// cargo test --release --package xmss --lib -- benchmark_sign::bench_wots_encode --exact --nocapture --ignored
#[test]
#[ignore]
fn bench_wots_encode() {
    const WARMUP: u64 = 20_000;
    const ATTEMPTS: u64 = 400_000;

    let (pk, _) = xmss_key_gen_from_seed(SEED, ACTIVATION_SLOT, NUM_ACTIVE_SLOTS).unwrap();
    let message: [u8; MESSAGE_LEN_BYTES] = std::array::from_fn(|i| i as u8);
    let message_fe = hash_message(&message);
    let slot = ACTIVATION_SLOT as u32;
    // Stand-in for the per-attempt PRF output: only its spread matters here.
    let randomness = |n: u64| -> Randomness {
        std::array::from_fn(|i| F::from_usize((n.wrapping_mul(0x9e37_79b9) as usize).wrapping_add(i)))
    };

    let mut accepted = 0u64;
    for n in 0..WARMUP {
        accepted += u64::from(black_box(wots_encode(&message_fe, slot, &pk, &randomness(n))).is_some());
    }

    let time = Instant::now();
    for n in WARMUP..WARMUP + ATTEMPTS {
        accepted += u64::from(black_box(wots_encode(&message_fe, slot, &pk, &randomness(n))).is_some());
    }
    let elapsed = time.elapsed();

    println!(
        "wots_encode: {:>8.1} ns/attempt ({accepted} accepted of {})",
        elapsed.as_secs_f64() * 1e9 / ATTEMPTS as f64,
        WARMUP + ATTEMPTS
    );
}

/// Signature digests for fixed (seed, slot, message) triples. An optimization that is meant to
/// leave the signature untouched must print the same digests before and after.
///
/// cargo test --release --package xmss --lib -- benchmark_sign::signature_digests --exact --nocapture --ignored
#[test]
#[ignore]
fn signature_digests() {
    let (pk, sk) = xmss_key_gen_from_seed(SEED, ACTIVATION_SLOT, NUM_ACTIVE_SLOTS).unwrap();
    for slot_offset in [0u64, 1, 7, 511, 1023] {
        let slot = (ACTIVATION_SLOT + slot_offset) as u32;
        let message: [u8; MESSAGE_LEN_BYTES] = std::array::from_fn(|i| (i as u8).wrapping_mul(slot as u8));
        let signature = xmss_sign(&sk, slot, &message).unwrap();
        assert!(xmss_verify(&pk, slot, &message, &signature).is_ok());

        let mut digest = 0xcbf2_9ce4_8422_2325u64;
        for byte in ssz::Encode::as_ssz_bytes(&signature) {
            digest = (digest ^ u64::from(byte)).wrapping_mul(0x0100_0000_01b3);
        }
        println!("slot {slot}: signature fnv1a = {digest:016x}");
    }
}
