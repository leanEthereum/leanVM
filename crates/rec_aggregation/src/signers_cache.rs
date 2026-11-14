//! Persistent cache for deterministic benchmark signatures, one file per scheme
//! and message.
//!
//! The cache grows as needed and is memoized in-process. Loaded signatures are
//! verified, so a change to the scheme regenerates them from the first that no
//! longer verifies; a change that leaves them valid bumps `SCHEMA_VERSION`.

use std::collections::BTreeMap;
use std::collections::hash_map::DefaultHasher;
use std::fs;
use std::hash::{Hash, Hasher};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::Instant;

use lean_xmss::*;
use primitives::{pretty_f64, pretty_integer};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

/// A cached leanXMSS signer, as the aggregation API takes it: the key, the message
/// it signed, the signature.
pub type LeanXmssSigner = (LeanXmssPublicKey, Message, LeanXmssSignature);

const SCHEMA_VERSION: u32 = 8;

/// One cached leanXMSS signer, as fixed-size bytes: the public key, then the signature.
const LEAN_XMSS_RECORD: usize = PUB_KEY_SIZE + SIG_SIZE;

/// The keys the cached leanXMSS signers share, a full key being slow to generate:
/// signer `i` is key `i % NUM_KEYS` in round `i / NUM_KEYS`, each round signing a
/// message of its own, so no two signers make the same claim.
const NUM_KEYS: usize = 32;

/// Message ids are below this, so that a key signs each message id and round at a
/// leaf index of its own.
const MESSAGE_IDS: u32 = 16;

/// The message [`get_signers`] signs in round 0.
pub fn message() -> Message {
    std::array::from_fn(|i| (i * 5 + 1) as u8)
}

/// The message of cache `message_id` in round 0: distinct per id, and exactly
/// [`message`] at 0.
#[cfg(test)]
pub(crate) fn message_for(message_id: u32) -> Message {
    signer_message(0, message_id)
}

/// The message signer `index` of cache `message_id` signs: distinct per id and round.
fn signer_message(index: usize, message_id: u32) -> Message {
    let round = (index / NUM_KEYS) as u32;
    let mut msg = message();
    for (byte, delta) in msg
        .iter_mut()
        .zip([message_id.to_le_bytes(), round.to_le_bytes()].as_flattened())
    {
        *byte ^= delta;
    }
    msg
}

/// The bottom tree the cached signers sign in: far from the first, so that the top
/// layer's index and path are not all zeros.
const BOTTOM_TREE: LeafIndex = 3_000_000_000 >> LAYER_HEIGHT;

/// The leaf index signer `index` of cache `message_id` signs at: its key's own for
/// each message, in [`BOTTOM_TREE`] for the first `2^16 / MESSAGE_IDS` rounds.
fn leaf_index_of(index: usize, message_id: u32) -> LeafIndex {
    assert!(
        message_id < MESSAGE_IDS,
        "message id {message_id} is not below {MESSAGE_IDS}"
    );
    (BOTTOM_TREE << LAYER_HEIGHT) + (index / NUM_KEYS) as LeafIndex * MESSAGE_IDS + message_id
}

fn key_seed(k: usize) -> Seed {
    let mut seed = [10; SEED_LEN];
    seed[..8].copy_from_slice(&(k as u64).to_le_bytes());
    seed
}

/// The [`NUM_KEYS`] keys, each generated, with [`BOTTOM_TREE`] prepared, when first used.
type Keys = [OnceLock<(LeanXmssSecretKey, LeanXmssPublicKey)>; NUM_KEYS];

fn key(keys: &Keys, k: usize) -> &(LeanXmssSecretKey, LeanXmssPublicKey) {
    keys[k].get_or_init(|| {
        let (sk, pk) = key_gen(key_seed(k));
        sk.prepare(BOTTOM_TREE << LAYER_HEIGHT).expect("prepare");
        (sk, pk)
    })
}

fn compute_signer(keys: &Keys, index: usize, message_id: u32) -> LeanXmssSigner {
    let (sk, pk) = key(keys, index % NUM_KEYS);
    let message = signer_message(index, message_id);
    let sig = sign(sk, &message, leaf_index_of(index, message_id)).expect("sign");
    (*pk, message, sig)
}

fn cache_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../target/signers-cache")
}

fn cache_path(message_id: u32) -> PathBuf {
    let mut hasher = DefaultHasher::new();
    // Key 0's public parameter, so that a new key derivation starts a new file.
    let public_param = public_param(&scheme_seed(&key_seed(0)));
    (
        SCHEMA_VERSION,
        LEAN_XMSS_RECORD,
        NUM_KEYS,
        MESSAGE_IDS,
        BOTTOM_TREE,
        public_param,
        message_id,
    )
        .hash(&mut hasher);
    cache_dir().join(format!("lean_xmss_signers_{:016x}.bin", hasher.finish()))
}

fn try_load_cache(path: &Path, message_id: u32) -> Option<Vec<LeanXmssSigner>> {
    let bytes = fs::read(path).ok()?;
    let mut signers: Vec<LeanXmssSigner> = Vec::with_capacity(bytes.len() / LEAN_XMSS_RECORD);
    for record in bytes.as_chunks::<LEAN_XMSS_RECORD>().0 {
        let index = signers.len();
        let (pk, sig) = record.split_at(PUB_KEY_SIZE);
        let pk = LeanXmssPublicKey::from_bytes(pk.try_into().unwrap());
        let sig = LeanXmssSignature::from_bytes(sig.try_into().unwrap());
        let message = signer_message(index, message_id);
        if index >= NUM_KEYS && pk != signers[index % NUM_KEYS].0
            || sig.leaf_index() != leaf_index_of(index, message_id)
            || lean_xmss::verify(&pk, &message, &sig).is_err()
        {
            eprintln!(
                "warning: signers cache {} is stale at signer {index}; regenerating from there",
                path.display(),
            );
            break;
        }
        signers.push((pk, message, sig));
    }
    Some(signers)
}

fn save_cache(path: &Path, signers: &[LeanXmssSigner]) {
    let mut bytes = Vec::with_capacity(signers.len() * LEAN_XMSS_RECORD);
    for (pk, _, sig) in signers {
        bytes.extend_from_slice(&pk.to_bytes());
        bytes.extend_from_slice(&sig.to_bytes());
    }
    write_cache(path, &bytes);
}

fn write_cache(path: &Path, bytes: &[u8]) {
    if let Some(parent) = path.parent() {
        let _ = fs::create_dir_all(parent);
    }
    if let Err(error) = fs::write(path, bytes) {
        eprintln!("warning: could not write signers cache to {}: {error}", path.display());
    }
}

/// `f` over `start..end` on `parallel`, with a progress line naming `what`.
fn generate<T: Send>(start: usize, end: usize, what: &str, f: impl Fn(usize) -> T + Sync) -> Vec<T> {
    let total = end - start;
    let started = Instant::now();
    let done = AtomicUsize::new(0);
    let generated = parallel::map_collect(total, |k| {
        let generated = f(start + k);
        let done = done.fetch_add(1, Ordering::Relaxed) + 1;
        print!(
            "\r  generating {what}: {}/{}",
            pretty_integer(done),
            pretty_integer(total)
        );
        let _ = std::io::stdout().flush();
        generated
    });
    println!(
        "\r  generated {} {what} in {} s                              ",
        pretty_integer(total),
        pretty_f64(started.elapsed().as_secs_f64())
    );
    generated
}

static POOLS: Mutex<BTreeMap<u32, Vec<LeanXmssSigner>>> = Mutex::new(BTreeMap::new());

/// The first `n` cached signers of [`message`] and the rounds after it.
pub fn get_signers(n: usize) -> Vec<LeanXmssSigner> {
    get_signers_for(n, 0)
}

/// The first `n` cached signers of cache `message_id`, signer `i` at
/// `leaf_index_of(i, message_id)`: one cache file per message id, the keys shared
/// across them.
pub(crate) fn get_signers_for(n: usize, message_id: u32) -> Vec<LeanXmssSigner> {
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
            // The keys first, one task each: a worker claims a run of signers, whose
            // keys it would otherwise generate one after another.
            let keys: Keys = [const { OnceLock::new() }; NUM_KEYS];
            let start = pool.len();
            generate(start, n.min(start + NUM_KEYS), "leanXMSS keys", |index| {
                key(&keys, index % NUM_KEYS);
            });
            let mut fresh = generate(pool.len(), n, "leanXMSS signatures", |index| {
                compute_signer(&keys, index, message_id)
            });
            pool.append(&mut fresh);
            save_cache(&path, pool);
        }
    }
    pool[..n].to_vec()
}

/// A leanSPHINCS signer, one key each, with the message it signed.
type CachedSphincsSignature = (
    lean_sphincs::LeanSphincsPublicKey,
    lean_sphincs::Message,
    lean_sphincs::LeanSphincsSignature,
);

/// Signer `index`'s own message, distinct from every other's and from the
/// leanXMSS ones, so a test that mixed them up would fail rather than pass.
pub(crate) fn lean_sphincs_message(index: usize) -> lean_sphincs::Message {
    let mut msg = [0u8; lean_sphincs::MESSAGE_LEN];
    msg[..8].copy_from_slice(&(index as u64).to_le_bytes());
    msg[8..].copy_from_slice(&[0xC5; lean_sphincs::MESSAGE_LEN - 8]);
    msg
}

/// One cached leanSPHINCS signer, as fixed-size bytes: the scheme's own
/// serializations, so nothing here has to agree with a derived one.
const LEAN_SPHINCS_RECORD: usize = lean_sphincs::PUB_KEY_SIZE + lean_sphincs::MESSAGE_LEN + lean_sphincs::SIG_SIZE;

fn compute_lean_sphincs_signer(index: usize) -> CachedSphincsSignature {
    let mut rng = StdRng::seed_from_u64(0x5F1A_C500 ^ index as u64);
    let (secret_key, public_key) = lean_sphincs::key_gen(rng.random());
    let message = lean_sphincs_message(index);
    let signature = lean_sphincs::sign(&secret_key, &message);
    (public_key, message, signature)
}

/// Keyed by signer 0's key, message and signature, so any change to the scheme
/// invalidates the file. Computed once.
fn lean_sphincs_cache_path() -> PathBuf {
    static PATH: std::sync::OnceLock<PathBuf> = std::sync::OnceLock::new();
    PATH.get_or_init(|| {
        let (public_key, message, signature) = compute_lean_sphincs_signer(0);
        let mut hasher = DefaultHasher::new();
        (
            SCHEMA_VERSION,
            LEAN_SPHINCS_RECORD,
            public_key,
            message,
            signature.to_bytes(),
            // Signer 0's message has a zero index; signer 1's binds how it is encoded.
            lean_sphincs_message(1),
        )
            .hash(&mut hasher);
        cache_dir().join(format!("lean_sphincs_signers_{:016x}.bin", hasher.finish()))
    })
    .clone()
}

fn try_load_lean_sphincs_cache() -> Option<Vec<CachedSphincsSignature>> {
    let bytes = fs::read(lean_sphincs_cache_path()).ok()?;
    let mut signers = Vec::with_capacity(bytes.len() / LEAN_SPHINCS_RECORD);
    for record in bytes.as_chunks::<LEAN_SPHINCS_RECORD>().0 {
        let (key_bytes, rest) = record.split_at(lean_sphincs::PUB_KEY_SIZE);
        let (message_bytes, signature_bytes) = rest.split_at(lean_sphincs::MESSAGE_LEN);
        let public_key = lean_sphincs::LeanSphincsPublicKey::from_bytes(key_bytes.try_into().unwrap());
        let message: lean_sphincs::Message = message_bytes.try_into().unwrap();
        let signature = lean_sphincs::LeanSphincsSignature::from_bytes(signature_bytes.try_into().unwrap());
        if !lean_sphincs::verify(&public_key, &message, &signature) {
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
    let mut bytes = Vec::with_capacity(signers.len() * LEAN_SPHINCS_RECORD);
    for (public_key, message, signature) in signers {
        bytes.extend_from_slice(&public_key.to_bytes());
        bytes.extend_from_slice(message);
        bytes.extend_from_slice(&signature.to_bytes());
    }
    write_cache(&lean_sphincs_cache_path(), &bytes);
}

static LEAN_SPHINCS_POOL: Mutex<Vec<CachedSphincsSignature>> = Mutex::new(Vec::new());

pub fn get_lean_sphincs_signers(n: usize) -> Vec<CachedSphincsSignature> {
    let mut pool = LEAN_SPHINCS_POOL.lock().unwrap();
    if pool.len() < n {
        if let Some(disk) = try_load_lean_sphincs_cache()
            && disk.len() > pool.len()
        {
            *pool = disk;
        }
        if pool.len() < n {
            let mut fresh = generate(pool.len(), n, "leanSPHINCS signatures", compute_lean_sphincs_signer);
            pool.append(&mut fresh);
            save_lean_sphincs_cache(&pool);
        }
    }
    pool[..n].to_vec()
}
