//! Persistent cache for deterministic benchmark signatures, one file per
//! scheme.
//!
//! The cache grows as needed and is memoized in-process. Its filename binds the
//! parameters, hash construction, encoding predicate, and key derivation. Loaded
//! signatures are also verified, so stale entries are regenerated from the first
//! invalid one.

use std::collections::BTreeMap;
use std::collections::hash_map::DefaultHasher;
use std::fs;
use std::hash::{Hash, Hasher};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::time::Instant;

use primitives::{pretty_f64, pretty_integer};
use rand::SeedableRng;
use rand::rngs::StdRng;
use signatures::lean_xmss::*;
use signatures::{lean_sphincs, lean_xmss};

type CachedSignature = (LeanXmssPublicKey, LeanXmssSignature);

const SCHEMA_VERSION: u32 = 7;

/// The leaf indices every cached key signs at: mock keys (`lean_xmss::mock`), real
/// only over this range, which a full key's top tree would make far slower to
/// generate.
const KEY_START: LeafIndex = 3_000_000_000;
const KEY_END: LeafIndex = 3_000_000_015;

/// The message [`get_signers`] signs. leanSPHINCS signers carry their own.
pub fn message() -> Message {
    std::array::from_fn(|i| (i * 5 + 1) as u8)
}

/// The message of cache `message_id`: distinct per id, and exactly [`message`] at 0.
pub fn message_for(message_id: u32) -> Message {
    let mut msg = message();
    for (byte, delta) in msg.iter_mut().zip(message_id.to_le_bytes()) {
        *byte ^= delta;
    }
    msg
}

/// The leaf index signer `index` signs [`message_for`]`(message_id)` at, shifted per
/// message so one key signs messages fewer than 16 ids apart at distinct leaf indices.
fn leaf_index_of(index: usize, message_id: u32) -> LeafIndex {
    let span = (KEY_END - KEY_START + 1) as usize;
    KEY_START + ((index + message_id as usize) % span) as LeafIndex
}

fn compute_signer(index: usize, message_id: u32) -> CachedSignature {
    // The index over its full width: a one-byte seed repeats every 256 signers,
    // and a repeated signer is invisible until something deduplicates the set,
    // at which point a batch of 900 quietly becomes one of 256.
    // One seed per signer, always over the one range KEY_START..=KEY_END: a seed
    // must back one key only (`lean_xmss::mock`).
    let mut seed = [10u8; 32];
    seed[..8].copy_from_slice(&(index as u64).to_le_bytes());
    let (sk, pk) = mock::key_gen_from_seed(seed, KEY_START, KEY_END);
    let sig = mock::sign(&sk, &message_for(message_id), leaf_index_of(index, message_id)).expect("sign");
    (pk, sig)
}

fn cache_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../target/signers-cache")
}

/// The cache file of `message_id`, named after signer 0's key and signature, which
/// any change to the scheme, its parameters, key derivation or grinding changes.
fn cache_path(message_id: u32) -> PathBuf {
    let mut hasher = DefaultHasher::new();
    (SCHEMA_VERSION, message_id, compute_signer(0, message_id)).hash(&mut hasher);
    cache_dir().join(format!("lean_xmss_signers_{:016x}.bin", hasher.finish()))
}

fn try_load_cache(path: &Path, message_id: u32) -> Option<Vec<CachedSignature>> {
    let bytes = fs::read(path).ok()?;
    let (version, mut signers): (u32, Vec<CachedSignature>) = bincode::deserialize(&bytes).ok()?;
    if version != SCHEMA_VERSION {
        return None;
    }
    let msg = message_for(message_id);
    let valid = signers
        .iter()
        .enumerate()
        .take_while(|(i, (pk, sig))| {
            sig.leaf_index == leaf_index_of(*i, message_id) && lean_xmss::verify(pk, &msg, sig).is_ok()
        })
        .count();
    if valid < signers.len() {
        eprintln!(
            "warning: signers cache {} is stale (signer {valid} of {} no longer verifies); regenerating from there",
            path.display(),
            signers.len()
        );
        signers.truncate(valid);
    }
    Some(signers)
}

fn save_cache(path: &Path, signers: &[CachedSignature]) {
    if let Some(parent) = path.parent() {
        let _ = fs::create_dir_all(parent);
    }
    let bytes = bincode::serialize(&(SCHEMA_VERSION, signers)).expect("serialize signers cache");
    if let Err(error) = fs::write(path, &bytes) {
        eprintln!("warning: could not write signers cache to {}: {error}", path.display());
    }
}

fn generate_range(start: usize, end: usize, message_id: u32) -> Vec<CachedSignature> {
    let total = end - start;
    let started = Instant::now();
    let mut signers = Vec::with_capacity(total);
    for (done, index) in (start..end).enumerate() {
        signers.push(compute_signer(index, message_id));
        print!(
            "\r  generating leanXMSS signers (one-time, then cached): {}/{}",
            pretty_integer(done + 1),
            pretty_integer(total)
        );
        let _ = std::io::stdout().flush();
    }
    println!(
        "\r  generated {} leanXMSS in {} s (cached to disk)                ",
        pretty_integer(total),
        pretty_f64(started.elapsed().as_secs_f64())
    );
    signers
}

static POOLS: Mutex<BTreeMap<u32, Vec<CachedSignature>>> = Mutex::new(BTreeMap::new());

/// The first `n` cached signers of [`message`].
pub fn get_signers(n: usize) -> Vec<CachedSignature> {
    get_signers_for(n, 0)
}

/// The first `n` cached signers, signing [`message_for`]`(message_id)`, signer `i` at
/// `leaf_index_of(i, message_id)`: one cache file per message, the keys shared
/// across them.
pub fn get_signers_for(n: usize, message_id: u32) -> Vec<CachedSignature> {
    let mut pools = POOLS.lock().unwrap();
    let pool = pools.entry(message_id).or_default();
    if pool.len() < n {
        let path = cache_path(message_id);
        if let Some(disk) = try_load_cache(&path, message_id)
            && disk.len() > pool.len()
        {
            *pool = disk;
        }
        if pool.len() < n {
            let mut fresh = generate_range(pool.len(), n, message_id);
            pool.append(&mut fresh);
            save_cache(&path, pool);
        }
    }
    pool[..n].to_vec()
}

/// The height of the subtree a cached leanSPHINCS key keeps. Verification does not
/// depend on it, and a full key takes `2^26` one-time keys to generate.
pub const LEAN_LEAN_SPHINCS_KEPT_HEIGHT: usize = 12;

/// A leanSPHINCS signer, generated the same way, with the message it signed.
/// Signing is stateless, so unlike leanXMSS there is no leaf index and no key range:
/// one key answers for every index.
type CachedSphincsSignature = (
    lean_sphincs::LeanSphincsPublicKey,
    lean_sphincs::Message,
    lean_sphincs::LeanSphincsSignature,
);

/// Signer `index`'s own message, distinct from every other's and from the
/// leanXMSS ones, so a test that mixed them up would fail rather than pass.
pub fn lean_sphincs_message(index: usize) -> lean_sphincs::Message {
    let mut msg = [0u8; lean_sphincs::MESSAGE_LEN];
    msg[..8].copy_from_slice(&(index as u64).to_le_bytes());
    msg[8..].copy_from_slice(&[0xC5; lean_sphincs::MESSAGE_LEN - 8]);
    msg
}

/// One cached leanSPHINCS signer, as fixed-size bytes: the scheme's own
/// serializations, so nothing here has to agree with a derived one.
const LEAN_LEAN_SPHINCS_RECORD: usize = lean_sphincs::PUB_KEY_SIZE + lean_sphincs::MESSAGE_LEN + lean_sphincs::SIG_SIZE;

fn compute_lean_sphincs_signer(index: usize) -> CachedSphincsSignature {
    let mut rng = StdRng::seed_from_u64(0x5F1A_C500 ^ index as u64);
    let (secret_key, public_key) = lean_sphincs::key_gen(&mut rng, LEAN_LEAN_SPHINCS_KEPT_HEIGHT);
    let message = lean_sphincs_message(index);
    let signature = lean_sphincs::sign(&secret_key, &message).expect("sign");
    (public_key, message, signature)
}

fn lean_sphincs_footprint() -> u64 {
    let mut hasher = DefaultHasher::new();
    SCHEMA_VERSION.hash(&mut hasher);
    // The record layout and the per-signer messages, so a change to either
    // invalidates the file rather than being read back as another scheme's.
    LEAN_LEAN_SPHINCS_RECORD.hash(&mut hasher);
    lean_sphincs_message(0).hash(&mut hasher);
    lean_sphincs_message(1).hash(&mut hasher);
    (
        lean_sphincs::MASTER_SECRET_LEN,
        lean_sphincs::V,
        lean_sphincs::W,
        lean_sphincs::TARGET_SUM,
        lean_sphincs::H,
        lean_sphincs::FOREST_TREES,
        lean_sphincs::TREE_HEIGHT,
        lean_sphincs::SUBTREE_HEIGHT,
        lean_sphincs::FOREST_CHAINS,
        LEAN_LEAN_SPHINCS_KEPT_HEIGHT,
    )
        .hash(&mut hasher);
    // The key derivation, the tweakable hash and the codeword table, so a change
    // to any of them invalidates the file.
    lean_sphincs::scheme_seed(&[0x11; lean_sphincs::MASTER_SECRET_LEN]).hash(&mut hasher);
    lean_sphincs::th(
        &[0xA5; lean_sphincs::PUBLIC_PARAM_LEN],
        &lean_sphincs::tweak(1, 2, 3).step(4),
        &[0x3C; 16],
    )
    .hash(&mut hasher);
    for t in 0..1 << lean_sphincs::CODEWORD_BITS {
        lean_sphincs::codeword(t).hash(&mut hasher);
    }
    hasher.finish()
}

fn lean_sphincs_cache_path() -> PathBuf {
    cache_dir().join(format!("lean_sphincs_signers_{:016x}.bin", lean_sphincs_footprint()))
}

fn try_load_lean_sphincs_cache() -> Option<Vec<CachedSphincsSignature>> {
    let bytes = fs::read(lean_sphincs_cache_path()).ok()?;
    let mut signers = Vec::with_capacity(bytes.len() / LEAN_LEAN_SPHINCS_RECORD);
    for record in bytes.as_chunks::<LEAN_LEAN_SPHINCS_RECORD>().0 {
        let (key_bytes, rest) = record.split_at(lean_sphincs::PUB_KEY_SIZE);
        let (message_bytes, signature_bytes) = rest.split_at(lean_sphincs::MESSAGE_LEN);
        let public_key = lean_sphincs::LeanSphincsPublicKey::from_bytes(key_bytes.try_into().unwrap());
        let message: lean_sphincs::Message = message_bytes.try_into().unwrap();
        let signature = lean_sphincs::LeanSphincsSignature::from_bytes(signature_bytes.try_into().unwrap());
        if lean_sphincs::verify(&public_key, &message, &signature).is_err() {
            eprintln!(
                "warning: signers cache {} is stale (signer {} no longer verifies); regenerating from there",
                lean_sphincs_cache_path().display(),
                signers.len()
            );
            break;
        }
        signers.push((public_key, message, signature));
    }
    Some(signers)
}

fn save_lean_sphincs_cache(signers: &[CachedSphincsSignature]) {
    let path = lean_sphincs_cache_path();
    if let Some(parent) = path.parent() {
        let _ = fs::create_dir_all(parent);
    }
    let mut bytes = Vec::with_capacity(signers.len() * LEAN_LEAN_SPHINCS_RECORD);
    for (public_key, message, signature) in signers {
        bytes.extend_from_slice(&public_key.flatten());
        bytes.extend_from_slice(message);
        bytes.extend_from_slice(&signature.to_bytes());
    }
    if let Err(error) = fs::write(&path, &bytes) {
        eprintln!("warning: could not write signers cache to {}: {error}", path.display());
    }
}

static LEAN_LEAN_SPHINCS_POOL: Mutex<Vec<CachedSphincsSignature>> = Mutex::new(Vec::new());

pub fn get_lean_sphincs_signers(n: usize) -> Vec<CachedSphincsSignature> {
    let mut pool = LEAN_LEAN_SPHINCS_POOL.lock().unwrap();
    if pool.len() < n {
        if let Some(disk) = try_load_lean_sphincs_cache()
            && disk.len() > pool.len()
        {
            *pool = disk;
        }
        // Key generation is one whole 2^12-leaf tree, which is the expensive
        // part; it fans out internally, so this loop stays sequential.
        let started = Instant::now();
        let missing = n.saturating_sub(pool.len());
        for index in pool.len()..n {
            pool.push(compute_lean_sphincs_signer(index));
            print!(
                "\r  generating leanSPHINCS signers (one-time, then cached): {}/{}",
                pretty_integer(index + 1 - (n - missing)),
                pretty_integer(missing)
            );
            let _ = std::io::stdout().flush();
        }
        if missing > 0 {
            println!(
                "\r  generated {} leanSPHINCS in {} s (cached to disk)              ",
                pretty_integer(missing),
                pretty_f64(started.elapsed().as_secs_f64())
            );
            save_lean_sphincs_cache(&pool);
        }
    }
    pool[..n].to_vec()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn signer_seed_uses_more_than_one_byte() {
        assert_ne!(compute_signer(0, 0).0, compute_signer(256, 0).0);
    }
}
