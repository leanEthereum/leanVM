use backend::*;
use rand::SeedableRng;
use rand::rngs::StdRng;
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::PathBuf;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

use crate::*;

static SIGNERS_CACHE: OnceLock<Vec<(XmssPublicKey, XmssSignature)>> = OnceLock::new();

pub fn get_benchmark_signatures() -> &'static Vec<(XmssPublicKey, XmssSignature)> {
    SIGNERS_CACHE.get_or_init(gen_benchmark_signers_cache)
}

pub const BENCHMARK_SLOT: u32 = 111;
pub const NUM_BENCHMARK_SIGNERS: usize = 10_000;

pub fn message_for_benchmark() -> [u8; MESSAGE_LEN_BYTES] {
    std::array::from_fn(|i| i as u8)
}

const CACHE_SCHEMA_VERSION: u32 = 6;

#[derive(Serialize, Deserialize)]
struct SignersCacheFile {
    schema_version: u32,
    signatures: Vec<(XmssPublicKey, XmssSignature)>,
}

fn cache_footprint(first_pubkey: &XmssPublicKey) -> u128 {
    let mut input = [F::ZERO; 16];
    input[0] = F::from_usize(NUM_BENCHMARK_SIGNERS);
    input[1] = F::from_u32(BENCHMARK_SLOT);
    input[2..2 + MESSAGE_LEN_FE].copy_from_slice(&hash_message(&message_for_benchmark()));
    input[2 + MESSAGE_LEN_FE..][..XMSS_DIGEST_LEN].copy_from_slice(&first_pubkey.merkle_root);
    let digest = poseidon16_compress(input);
    digest[..4]
        .iter()
        .fold(0u128, |acc, f| (acc << 32) | u128::from(f.as_canonical_u32()))
}

fn cache_dir() -> PathBuf {
    // In CI, set SIGNERS_CACHE_DIR to a path outside target/
    if let Ok(dir) = std::env::var("SIGNERS_CACHE_DIR") {
        PathBuf::from(dir)
    } else {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../target/signers-cache")
    }
}

fn cache_path(first_pubkey: &XmssPublicKey) -> PathBuf {
    let footprint = cache_footprint(first_pubkey);
    let file = format!("benchmark_signers_cache_{footprint:032x}.bin");
    cache_dir().join(file)
}

fn compute_signer(index: usize) -> (XmssPublicKey, XmssSignature) {
    let mut rng = StdRng::seed_from_u64(index as u64);
    let (pk, sk) = xmss_key_gen(&mut rng, BENCHMARK_SLOT as u64, 2).unwrap();
    let sig = xmss_sign(&sk, BENCHMARK_SLOT, &message_for_benchmark()).unwrap();
    (pk, sig)
}

fn try_load_cache(path: &PathBuf) -> Option<Vec<(XmssPublicKey, XmssSignature)>> {
    let data = fs::read(path).ok()?;
    let cached: SignersCacheFile = postcard::from_bytes(&data).ok()?;
    let valid = cached.schema_version == CACHE_SCHEMA_VERSION && cached.signatures.len() == NUM_BENCHMARK_SIGNERS;
    valid.then_some(cached.signatures)
}

fn gen_benchmark_signers_cache() -> Vec<(XmssPublicKey, XmssSignature)> {
    // Compute first signer; its pubkey feeds into the cache footprint
    let first_signer = compute_signer(0);
    let path = cache_path(&first_signer.0);

    if let Some(signers) = try_load_cache(&path) {
        return signers;
    }

    let completed = AtomicUsize::new(1);
    let time = Instant::now();
    let n_rest = NUM_BENCHMARK_SIGNERS - 1;
    let rest = parallel::par_map_collect(n_rest, |i| {
        let signer = compute_signer(1 + i);
        let done = completed.fetch_add(1, Ordering::Relaxed) + 1;
        print!(
            "\rPrecomputing benchmark signatures (cached after first run): {:.0}%",
            100.0 * done as f64 / NUM_BENCHMARK_SIGNERS as f64
        );
        signer
    });

    println!(
        "\rGenerating signatures for benchmark (one-time operation): 100% - done ({:.2}s)",
        time.elapsed().as_secs_f32()
    );

    let mut signers = Vec::with_capacity(NUM_BENCHMARK_SIGNERS);
    signers.push(first_signer);
    signers.extend(rest);

    let cache_file = SignersCacheFile {
        schema_version: CACHE_SCHEMA_VERSION,
        signatures: signers.clone(),
    };
    let encoded = postcard::to_allocvec(&cache_file).expect("serialization failed");
    if let Some(parent) = path.parent() {
        let _ = fs::create_dir_all(parent);
    }
    fs::write(&path, &encoded).expect("Failed to save benchmark cache");

    signers
}

#[test]
fn test_signature_cache() {
    let signatures = get_benchmark_signatures();
    parallel::for_each_index(signatures.len(), |i| {
        let (pk, sig) = &signatures[i];
        xmss_verify(pk, BENCHMARK_SLOT, &message_for_benchmark(), sig)
            .unwrap_or_else(|_| panic!("Signature {} failed to verify", i));
    });
}
