//! Deterministic benchmark and test signers, generated on the given prover's pool and cached in memory and on disk,
//! one file per scheme and message id, each signer stored as its public key then its signature.
//!
//! Loaded signers are verified, so a change to the scheme regenerates them from the first that no longer verifies; a
//! change that leaves them valid bumps `VERSION`.

use std::collections::BTreeMap;
use std::collections::hash_map::DefaultHasher;
use std::fs;
use std::hash::{Hash, Hasher};
use std::io::Write;
use std::ops::Range;
use std::path::PathBuf;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

use isa::{Prover, pretty_f64, pretty_integer};
use lean_sphincs::{LeanSphincsPublicKey, LeanSphincsSignature};
use lean_xmss::internals::*;
use lean_xmss::*;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

/// A cached leanXMSS signer, as the aggregation API takes it: the key, the message it signed, the signature.
pub type LeanXmssSigner = (LeanXmssPublicKey, Message, LeanXmssSignature);

/// A cached leanSPHINCS signer, one key each, with the message it signed.
pub type LeanSphincsSigner = (LeanSphincsPublicKey, lean_sphincs::Message, LeanSphincsSignature);

/// Bumped by a change to the signers that leaves the cached ones valid.
pub const VERSION: u32 = 9;

/// The keys the cached leanXMSS signers share, a full key being slow to generate: signer `i` is key `i % NUM_KEYS`
/// in round `i / NUM_KEYS`, each round signing a message of its own, so no two signers make the same claim.
const NUM_KEYS: usize = 32;

/// Message ids are below this, so that a key signs each message id and round at a leaf index of its own.
const MESSAGE_IDS: u32 = 16;

/// The bottom tree the cached leanXMSS signers sign in: far from the first, so that the top layer's index and path
/// are not all zeros.
const BOTTOM_TREE: LeafIndex = 3_000_000_000 >> LAYER_HEIGHT;

/// The message [`get_signers`] signs in round 0.
pub fn message() -> Message {
    std::array::from_fn(|i| (i * 5 + 1) as u8)
}

/// The message of cache `message_id` in round 0: distinct per id, and exactly [`message`] at 0.
#[cfg(test)]
pub(crate) fn message_for(message_id: u32) -> Message {
    signer_message(0, message_id)
}

/// The message leanXMSS signer `index` of cache `message_id` signs: distinct per id and round.
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

/// The leaf index leanXMSS signer `index` of cache `message_id` signs at: its key's own for each message, in
/// [`BOTTOM_TREE`] for the first `2^16 / MESSAGE_IDS` rounds.
fn leaf_index_of(index: usize, message_id: u32) -> LeafIndex {
    (BOTTOM_TREE << LAYER_HEIGHT) + (index / NUM_KEYS) as LeafIndex * MESSAGE_IDS + message_id
}

fn key_seed(k: usize) -> SecretKey {
    let mut seed = [10; SECRET_KEY_LEN];
    seed[..8].copy_from_slice(&(k as u64).to_le_bytes());
    seed
}

/// The first `n` cached signers of [`message`] and the rounds after it, generated if not cached.
pub fn get_signers<P: Prover>(n: usize) -> Vec<LeanXmssSigner> {
    get_signers_for::<P>(n, 0)
}

/// The first `n` cached signers of cache `message_id`, signer `i` at `leaf_index_of(i, message_id)`: one cache file
/// per message id, the keys shared across them.
pub(crate) fn get_signers_for<P: Prover>(n: usize, message_id: u32) -> Vec<LeanXmssSigner> {
    static POOLS: Mutex<BTreeMap<u32, Vec<LeanXmssSigner>>> = Mutex::new(BTreeMap::new());
    assert!(
        message_id < MESSAGE_IDS,
        "message id {message_id} is not below {MESSAGE_IDS}"
    );
    cached(
        POOLS.lock().unwrap().entry(message_id).or_default(),
        n,
        // Key 0's public parameter, so that a new key derivation starts a new file.
        || {
            cache_path(
                "lean_xmss",
                (
                    NUM_KEYS,
                    BOTTOM_TREE,
                    public_param(&scheme_seed(&key_seed(0))),
                    message_id,
                ),
            )
        },
        PUB_KEY_SIZE + SIG_SIZE,
        |earlier, record| {
            let index = earlier.len();
            let (pk, sig) = record.split_at(PUB_KEY_SIZE);
            let pk = LeanXmssPublicKey::from_bytes(pk.try_into().unwrap());
            let sig = LeanXmssSignature::from_bytes(sig.try_into().unwrap());
            let message = signer_message(index, message_id);
            let valid = (index < NUM_KEYS || pk == earlier[index % NUM_KEYS].0)
                && sig.leaf_index() == leaf_index_of(index, message_id)
                && verify(&pk, &message, &sig);
            valid.then_some((pk, message, sig))
        },
        |(pk, _, sig)| [&pk.to_bytes()[..], &sig.to_bytes()].concat(),
        |range| {
            // The keys first, one task each: a worker claims a run of signers, whose keys it would otherwise generate
            // one after another. `keys[j]` is the key of signer `range.start + j`.
            let keys = progress::<P, _>("leanXMSS keys", 0..NUM_KEYS.min(range.len()), |j| {
                let (sk, pk) = key_gen(&key_seed((range.start + j) % NUM_KEYS));
                sk.prepare(BOTTOM_TREE << LAYER_HEIGHT);
                (sk, pk)
            });
            progress::<P, _>("leanXMSS signatures", range.clone(), |index| {
                let (sk, pk) = &keys[(index - range.start) % NUM_KEYS];
                let message = signer_message(index, message_id);
                (*pk, message, sign(sk, &message, leaf_index_of(index, message_id)))
            })
        },
    )
}

/// Signer `index`'s own message, distinct from every other's and from the leanXMSS ones, so a test that mixed them
/// up would fail rather than pass.
fn lean_sphincs_message(index: usize) -> lean_sphincs::Message {
    let mut msg = [0xC5; lean_sphincs::MESSAGE_LEN];
    msg[..8].copy_from_slice(&(index as u64).to_le_bytes());
    msg
}

fn lean_sphincs_signer(index: usize) -> LeanSphincsSigner {
    let secret_key: lean_sphincs::SecretKey = StdRng::seed_from_u64(0x5F1A_C500 ^ index as u64).random();
    let message = lean_sphincs_message(index);
    (
        lean_sphincs::key_gen(&secret_key),
        message,
        lean_sphincs::sign(&secret_key, &message),
    )
}

/// The first `n` cached leanSPHINCS signers, generated if not cached.
pub fn get_lean_sphincs_signers<P: Prover>(n: usize) -> Vec<LeanSphincsSigner> {
    static POOL: Mutex<Vec<LeanSphincsSigner>> = Mutex::new(Vec::new());
    cached(
        &mut POOL.lock().unwrap(),
        n,
        // Signer 0, so that a change to the scheme starts a new file.
        || {
            let (pk, _, sig) = lean_sphincs_signer(0);
            cache_path("lean_sphincs", (pk.to_bytes(), sig.to_bytes()))
        },
        lean_sphincs::PUB_KEY_SIZE + lean_sphincs::SIG_SIZE,
        |earlier, record| {
            let (pk, sig) = record.split_at(lean_sphincs::PUB_KEY_SIZE);
            let pk = LeanSphincsPublicKey::from_bytes(pk.try_into().unwrap());
            let sig = LeanSphincsSignature::from_bytes(sig.try_into().unwrap());
            let message = lean_sphincs_message(earlier.len());
            lean_sphincs::verify(&pk, &message, &sig).then_some((pk, message, sig))
        },
        |(pk, _, sig)| [&pk.to_bytes()[..], &sig.to_bytes()].concat(),
        |range| progress::<P, _>("leanSPHINCS signatures", range, lean_sphincs_signer),
    )
}

/// `f` over `range` on `P`'s pool, with a progress line naming `what`.
fn progress<P: Prover, T: Send>(what: &str, range: Range<usize>, f: impl Fn(usize) -> T + Sync) -> Vec<T> {
    let (total, started, done) = (range.len(), Instant::now(), AtomicUsize::new(0));
    let generated = P::map_collect(total, |k| {
        let generated = f(range.start + k);
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

fn cache_path(scheme: &str, fingerprint: impl Hash) -> PathBuf {
    let mut hasher = DefaultHasher::new();
    (VERSION, fingerprint).hash(&mut hasher);
    let name = format!(
        "../../target/signers-cache/{scheme}_signers_{:016x}.bin",
        hasher.finish()
    );
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(name)
}

/// The first `n` signers of `pool`, extended first from the file at `path`, records of `record` bytes that `load`
/// reads (given the signers before it, rejecting a stale one and all after it), then by `generate` on the indices
/// still missing, the file then written anew with `save`.
fn cached<S: Clone>(
    pool: &mut Vec<S>,
    n: usize,
    path: impl FnOnce() -> PathBuf,
    record: usize,
    load: impl Fn(&[S], &[u8]) -> Option<S>,
    save: impl Fn(&S) -> Vec<u8>,
    generate: impl FnOnce(Range<usize>) -> Vec<S>,
) -> Vec<S> {
    if pool.len() < n {
        let path = path();
        let mut disk = Vec::new();
        for bytes in fs::read(&path).unwrap_or_default().chunks_exact(record) {
            let Some(signer) = load(&disk, bytes) else {
                eprintln!(
                    "warning: signers cache {} is stale at signer {}; regenerating from there",
                    path.display(),
                    disk.len()
                );
                break;
            };
            disk.push(signer);
        }
        if disk.len() > pool.len() {
            *pool = disk;
        }
        if pool.len() < n {
            pool.extend(generate(pool.len()..n));
            let bytes: Vec<u8> = pool.iter().flat_map(save).collect();
            if let Err(error) = fs::create_dir_all(path.parent().unwrap()).and_then(|()| fs::write(&path, bytes)) {
                eprintln!("warning: could not write signers cache {}: {error}", path.display());
            }
        }
    }
    pool[..n].to_vec()
}
