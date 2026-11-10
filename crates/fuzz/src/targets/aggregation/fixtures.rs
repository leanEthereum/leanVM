//! What every aggregation target builds on: cached signers, two keys that sign twice, three blob rows, and a small
//! set of real aggregates, proven once per campaign and shared on disk by every worker, behind a lock.

use crate::{Ctx, Finding, Rng};
use rec_aggregation::{EthereumClaims, EthereumProof, LeanSphincsClaim, LeanXmssClaim, aggregate};
use signatures::lean_sphincs::{self, LeanSphincsPublicKey, LeanSphincsSignature};
use signatures::lean_xmss::{self, LeanXmssPublicKey, LeanXmssSignature};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::time::{Duration, SystemTime};

pub type RawXmss = (LeanXmssPublicKey, lean_xmss::Message, LeanXmssSignature);
pub type RawSphincs = (LeanSphincsPublicKey, lean_sphincs::Message, LeanSphincsSignature);

/// Cached leanXMSS signers, all on [`message_a`].
pub const N_XMSS: usize = 8;
/// Cached leanSPHINCS signers, each on its own message.
pub const N_SPHINCS: usize = 4;

/// The fixtures, by index into [`Fixtures::children`].
pub const X3: usize = 0;
pub const S2: usize = 1;
pub const DA: usize = 2;
pub const MIXED: usize = 3;
pub const NODE: usize = 4;
pub const X3R2: usize = 5;
pub const TWO_MSG: usize = 6;
pub const NARROW: usize = 7;
pub const NAMES: [&str; 8] = ["x3", "s2", "da", "mixed", "node", "x3r2", "two-msg", "narrow"];

/// Bump to rebuild every campaign's fixtures.
const VERSION: u32 = 1;

pub struct Signers {
    pub xmss: Vec<RawXmss>,
    pub sphincs: Vec<RawSphincs>,
    /// One leanXMSS key: [`message_a`] at the first leaf of its range, [`message_b`] at the second, [`message_a`]
    /// again at the third.
    pub xmss_two: [RawXmss; 3],
    /// One leanSPHINCS key on two messages.
    pub sphincs_two: [RawSphincs; 2],
}

pub struct Fixture {
    pub name: &'static str,
    pub rate: usize,
    pub proof: EthereumProof,
}

pub struct Fixtures {
    pub signers: Signers,
    /// One row each: the `da` fixture's, the `mixed` fixture's, and one no fixture holds.
    pub blobs: [Vec<u64>; 3],
    pub children: Vec<Fixture>,
}

impl Fixtures {
    pub fn proof(&self, i: usize) -> &EthereumProof {
        &self.children[i].proof
    }

    pub fn claims(&self, i: usize) -> &EthereumClaims {
        self.children[i].proof.claims()
    }
}

pub fn message_a() -> lean_xmss::Message {
    rec_aggregation::signers_cache::message()
}

pub fn message_b() -> lean_xmss::Message {
    std::array::from_fn(|i| 0xB0 ^ i as u8)
}

/// A row of blob symbols from a seed.
pub fn blob_row(seed: u64) -> Vec<u64> {
    let mut rng = Rng::new(seed);
    (0..lean_da::BLOB_SYMBOLS).map(|_| rng.next_u64()).collect()
}

pub fn root_of(blobs: &[u64]) -> [u8; 32] {
    lean_da::commit(blobs).expect("a whole row").0
}

fn signers() -> Signers {
    let xmss = rec_aggregation::signers_cache::get_signers(N_XMSS)
        .into_iter()
        .map(|(pk, sig)| (pk, message_a(), sig))
        .collect();
    let sphincs = rec_aggregation::signers_cache::get_lean_sphincs_signers(N_SPHINCS);
    // A seed backs one key: this one, over this range, nowhere else.
    const FIRST: lean_xmss::LeafIndex = 3_000_000_100;
    let (sk, pk) = lean_xmss::mock::key_gen_from_seed([0xA7; 32], FIRST, FIRST + 3);
    let sign = |message: lean_xmss::Message, leaf| {
        let sig = lean_xmss::mock::sign(&sk, &message, leaf).expect("mock signs in range");
        (pk, message, sig)
    };
    let xmss_two = [
        sign(message_a(), FIRST),
        sign(message_b(), FIRST + 1),
        sign(message_a(), FIRST + 2),
    ];
    let (sk, pk) = lean_sphincs::key_gen_from_seed([0x5B; lean_sphincs::SEED_LEN]);
    let sphincs_two = [message_a(), message_b()].map(|message| {
        let sig = lean_sphincs::sign(&sk, &message).expect("signs");
        (pk, message, sig)
    });
    Signers {
        xmss,
        sphincs,
        xmss_two,
        sphincs_two,
    }
}

/// The process's fixtures, built by the first worker of the campaign to get here and loaded by every other.
pub fn fixtures(ctx: &Ctx) -> Result<&'static Fixtures, Finding> {
    static FIXTURES: OnceLock<Fixtures> = OnceLock::new();
    if let Some(f) = FIXTURES.get() {
        return Ok(f);
    }
    leanvm_core::init_prover();
    rec_aggregation::warm_up();
    let signers = signers();
    let blobs = [blob_row(0xDA_0001), blob_row(0xDA_0002), blob_row(0xDA_0003)];
    let dir = ctx.path(&format!("aggregation/fixtures-{:016x}/x", version_hash()));
    let dir = dir.parent().expect("a parent").to_path_buf();
    let children = load_or_build(&dir, &signers, &blobs)?;
    Ok(FIXTURES.get_or_init(|| Fixtures {
        signers,
        blobs,
        children,
    }))
}

/// The guest and the format: a change to either is a new set of fixtures.
fn version_hash() -> u64 {
    use std::hash::{Hash, Hasher};
    let (source, placeholders) = rec_aggregation::fuzzing::guest_source();
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    (VERSION, source, placeholders).hash(&mut hasher);
    hasher.finish()
}

struct Lock(PathBuf);

impl Drop for Lock {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir(&self.0);
    }
}

/// A lock older than this belongs to a worker that was killed: the heavy timeout.
const STALE: Duration = Duration::from_secs(3600);

fn load_or_build(dir: &Path, signers: &Signers, blobs: &[Vec<u64>; 3]) -> Result<Vec<Fixture>, Finding> {
    let done = dir.join("done");
    let lock = dir.join("lock");
    loop {
        if done.exists() {
            return load(dir);
        }
        match std::fs::create_dir(&lock) {
            Ok(()) => {
                let _held = Lock(lock.clone());
                if done.exists() {
                    return load(dir);
                }
                build(dir, signers, blobs)?;
                std::fs::write(&done, b"").expect("write the fixtures' marker");
                return load(dir);
            }
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {
                let age = std::fs::metadata(&lock)
                    .and_then(|m| m.modified())
                    .ok()
                    .and_then(|t| SystemTime::now().duration_since(t).ok());
                if age.is_some_and(|age| age > STALE) {
                    let _ = std::fs::remove_dir(&lock);
                }
                std::thread::sleep(Duration::from_secs(2));
            }
            Err(e) => panic!("cannot create the fixtures lock {}: {e}", lock.display()),
        }
    }
}

fn prove(
    name: &str,
    children: &[EthereumProof],
    xmss: &[RawXmss],
    sphincs: &[RawSphincs],
    blobs: &[u64],
    declare: Option<&EthereumClaims>,
    rate: usize,
) -> Result<EthereumProof, Finding> {
    let proof = aggregate(children, xmss.to_vec(), sphincs.to_vec(), blobs, declare, rate).map_err(|e| {
        Finding::high(
            format!("aggregation fixtures: honest aggregate `{name}` refused"),
            format!("{e:?}"),
        )
    })?;
    proof.verify().map_err(|e| {
        Finding::high(
            format!("aggregation fixtures: honest aggregate `{name}` does not verify"),
            format!("{e:?}"),
        )
    })?;
    Ok(proof)
}

fn build(dir: &Path, s: &Signers, blobs: &[Vec<u64>; 3]) -> Result<(), Finding> {
    eprintln!("building the aggregation fixtures in {}", dir.display());
    let x3 = prove("x3", &[], &s.xmss[..3], &[], &[], None, 1)?;
    let s2 = prove("s2", &[], &[], &s.sphincs[..2], &[], None, 2)?;
    let da = prove("da", &[], &[], &[], &blobs[0], None, 1)?;
    let mixed = prove("mixed", &[], &s.xmss[2..5], &s.sphincs[1..3], &blobs[1], None, 1)?;
    let node = prove("node", &[x3.clone(), s2.clone()], &[], &[], &[], None, 1)?;
    let x3r2 = prove("x3r2", &[], &s.xmss[..3], &[], &[], None, 2)?;
    let two_msg = prove("two-msg", &[], &s.xmss_two[..2], &[], &[], None, 1)?;
    // Drops leanXMSS signer 2's claim and one leanSPHINCS claim, keeping the root.
    let mut narrowed = mixed.claims().clone();
    narrowed.xmss.remove(0);
    narrowed.lean_sphincs.remove(0);
    let narrow = prove(
        "narrow",
        std::slice::from_ref(&mixed),
        &[],
        &[],
        &[],
        Some(&narrowed),
        1,
    )?;
    let rates = [1, 2, 1, 1, 1, 2, 1, 1];
    for (i, proof) in [x3, s2, da, mixed, node, x3r2, two_msg, narrow].iter().enumerate() {
        let path = dir.join(format!("{}.bin", NAMES[i]));
        let tmp = dir.join(format!("{}.tmp", NAMES[i]));
        std::fs::write(&tmp, encode(rates[i], proof)).expect("write a fixture");
        std::fs::rename(&tmp, &path).expect("move a fixture in place");
    }
    Ok(())
}

fn load(dir: &Path) -> Result<Vec<Fixture>, Finding> {
    let mut out = Vec::new();
    for name in NAMES {
        let bytes = std::fs::read(dir.join(format!("{name}.bin"))).expect("read a fixture");
        let (rate, claims, proof_bytes) = decode(&bytes).expect("a fixture we wrote");
        let proof = EthereumProof::from_proof_bytes(proof_bytes, claims).map_err(|e| {
            Finding::high(
                format!("aggregation fixtures: `{name}` does not decode"),
                format!("{e:?}"),
            )
        })?;
        proof.verify().map_err(|e| {
            Finding::high(
                format!("aggregation fixtures: `{name}` no longer verifies once decoded"),
                format!("{e:?}"),
            )
        })?;
        out.push(Fixture { name, rate, proof });
    }
    Ok(out)
}

fn encode(rate: usize, proof: &EthereumProof) -> Vec<u8> {
    let claims = proof.claims();
    let mut out = (rate as u64).to_le_bytes().to_vec();
    out.extend((claims.xmss.len() as u32).to_le_bytes());
    for (pk, message) in &claims.xmss {
        out.extend(pk.to_bytes());
        out.extend(message);
    }
    out.extend((claims.lean_sphincs.len() as u32).to_le_bytes());
    for (pk, message) in &claims.lean_sphincs {
        out.extend(pk.to_bytes());
        out.extend(message);
    }
    match claims.da_commitment {
        Some(root) => {
            out.push(1);
            out.extend(root);
        }
        None => out.extend([0; 33]),
    }
    out.extend(proof.proof_bytes());
    out
}

fn decode(bytes: &[u8]) -> Option<(usize, EthereumClaims, &[u8])> {
    let mut at = 0;
    let mut take = |n: usize| {
        let s = bytes.get(at..at + n)?;
        at += n;
        Some(s)
    };
    let rate = u64::from_le_bytes(take(8)?.try_into().ok()?) as usize;
    let nx = u32::from_le_bytes(take(4)?.try_into().ok()?) as usize;
    let mut xmss: Vec<LeanXmssClaim> = Vec::new();
    for _ in 0..nx {
        let pk = LeanXmssPublicKey::from_bytes(take(lean_xmss::PUB_KEY_SIZE)?.try_into().ok()?);
        xmss.push((pk, take(32)?.try_into().ok()?));
    }
    let ns = u32::from_le_bytes(take(4)?.try_into().ok()?) as usize;
    let mut lean_sphincs: Vec<LeanSphincsClaim> = Vec::new();
    for _ in 0..ns {
        let pk = LeanSphincsPublicKey::from_bytes(take(lean_sphincs::PUB_KEY_SIZE)?.try_into().ok()?);
        lean_sphincs.push((pk, take(32)?.try_into().ok()?));
    }
    let flag = take(1)?[0];
    let root: [u8; 32] = take(32)?.try_into().ok()?;
    let da_commitment = (flag == 1).then_some(root);
    Some((
        rate,
        EthereumClaims {
            xmss,
            lean_sphincs,
            da_commitment,
        },
        &bytes[at..],
    ))
}

/// The claims a set of raw signatures would publish, sorted and deduplicated, with `da`.
pub fn claims_of(xmss: &[RawXmss], sphincs: &[RawSphincs], da: Option<[u8; 32]>) -> EthereumClaims {
    let mut c = EthereumClaims {
        xmss: xmss.iter().map(|(pk, m, _)| (*pk, *m)).collect(),
        lean_sphincs: sphincs.iter().map(|(pk, m, _)| (*pk, *m)).collect(),
        da_commitment: da,
    };
    normalize(&mut c);
    c
}

/// Sort and deduplicate both lists, as a node publishes them.
pub fn normalize(c: &mut EthereumClaims) {
    c.xmss.sort();
    c.xmss.dedup();
    c.lean_sphincs.sort();
    c.lean_sphincs.dedup();
}

/// `a` with `b`'s claims merged in; `a`'s DA root.
pub fn union(a: &EthereumClaims, b: &EthereumClaims) -> EthereumClaims {
    let mut c = a.clone();
    c.xmss.extend(b.xmss.iter().copied());
    c.lean_sphincs.extend(b.lean_sphincs.iter().copied());
    normalize(&mut c);
    c
}
