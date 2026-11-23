//! Recursive aggregation of leanXMSS and leanSPHINCS signatures into one leanVM proof.
//!
//! It is the argument-based multi-signature of Drake, Khovratovich, Kudinov and Wagner.
//!
//! - Paper: "Hash-Based Multi-Signatures for Post-Quantum Ethereum", IACR Communications in Cryptology 2(1), 2025.
//! - Construction 4: an aggregate is a succinct argument of knowledge of every signature.
//! - Theorem 2: it is as unforgeable as the signatures, given adaptive knowledge soundness.
//!
//! An encoded aggregate is the proof alone: the claims travel separately, and a receiver checks
//! the proof against the claims it expects.

use std::fmt;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::OnceLock;

use lean_vm::{AggregateClaims, AggregateProof, OutputClaims, MAX_RECURSIONS};

use crate::{sphincs, xmss, Error, Message};

/// The most children one aggregation recurses over.
pub const MAX_CHILDREN: usize = MAX_RECURSIONS;

/// Exponent of the proof's Reed-Solomon code rate, `rho = 2^-2 = 1/4`: a larger one gives a smaller
/// proof but slower proving.
const LOG_INV_RATE: usize = 2;

/// The pool's thread count, once it runs.
static POOL: OnceLock<usize> = OnceLock::new();

/// The process that started the pool, and the one building the guest (`BUILT` once built), each
/// set before it starts: a child forked since inherits their state but not the threads running them.
static POOL_OWNER: AtomicU32 = AtomicU32::new(0);
static GUEST_OWNER: AtomicU32 = AtomicU32::new(0);
const BUILT: u32 = u32::MAX;

/// Starts the prover pool with `threads` threads (0: one per core) and builds the aggregation
/// guest, once per process.
///
/// # Errors
///
/// - Fails when `threads` exceeds the machine's parallelism.
/// - Fails when the pool already runs with another thread count.
/// - Fails in a process forked while or after its parent started the pool.
pub fn setup(threads: usize) -> Result<(), Error> {
    let max = std::thread::available_parallelism().map_or(1, usize::from);
    if threads > max {
        return Err(Error::TooManyThreads { threads, max });
    }
    let running = start(threads)?;
    if running != threads {
        return Err(Error::SetupThreads { running, threads });
    }
    Ok(())
}

fn start(threads: usize) -> Result<usize, Error> {
    claim(&POOL_OWNER)?;
    build_guest()?;
    Ok(*POOL.get_or_init(|| {
        lean_vm::setup(threads);
        threads
    }))
}

/// Builds the aggregation guest, which decoding, verifying and proving read, unless another process is building it.
fn build_guest() -> Result<(), Error> {
    claim(&GUEST_OWNER)?;
    aggregation::unified_guest();
    GUEST_OWNER.store(BUILT, Ordering::Release);
    Ok(())
}

/// Fails in a process forked from the one that claimed `owner`.
fn unclaimed_or_ours(owner: &AtomicU32) -> Result<(), Error> {
    match owner.load(Ordering::Acquire) {
        0 | BUILT => Ok(()),
        pid if pid == std::process::id() => Ok(()),
        _ => Err(Error::ForkedAfterSetup),
    }
}

fn claim(owner: &AtomicU32) -> Result<(), Error> {
    let pid = std::process::id();
    match owner.compare_exchange(0, pid, Ordering::AcqRel, Ordering::Acquire) {
        Err(other) if other != pid && other != BUILT => Err(Error::ForkedAfterSetup),
        _ => Ok(()),
    }
}

/// Proves raw signatures and child aggregates together as one aggregate.
///
/// ```text
///     claims(result) = claims(children) + claims(raw inputs)
///                      sorted, one entry per (public key, message)
/// ```
///
/// - Raw signatures are verified first, so a bad one is named by its index.
/// - The proof re-verifies each child.
/// - Proofs run one at a time per process.
///
/// # Errors
///
/// - Fails when more than 16 children are given.
/// - Fails when a raw signature does not verify, naming its list and index.
/// - Fails when the prover rejects the input, for example when it is empty.
/// - Fails in a process forked while or after its parent started the pool.
pub fn aggregate(
    children: &[&Aggregate],
    xmss: &[(xmss::PublicKey, Message, xmss::Signature)],
    sphincs: &[(sphincs::PublicKey, Message, sphincs::Signature)],
) -> Result<Aggregate, Error> {
    prove(children, xmss, sphincs, None)
}

/// [`aggregate`], but the result proves exactly these claims, in any order, a repeat counting once. Raw signatures
/// whose claims it drops are still verified and proven.
///
/// # Errors
///
/// As [`aggregate`]'s, and the prover rejects no claims, or a claim the inputs do not cover.
pub fn aggregate_only(
    children: &[&Aggregate],
    xmss: &[(xmss::PublicKey, Message, xmss::Signature)],
    sphincs: &[(sphincs::PublicKey, Message, sphincs::Signature)],
    xmss_claims: &[(xmss::PublicKey, Message)],
    sphincs_claims: &[(sphincs::PublicKey, Message)],
) -> Result<Aggregate, Error> {
    prove(
        children,
        xmss,
        sphincs,
        Some(&statement(xmss_claims, sphincs_claims)),
    )
}

fn prove(
    children: &[&Aggregate],
    xmss: &[(xmss::PublicKey, Message, xmss::Signature)],
    sphincs: &[(sphincs::PublicKey, Message, sphincs::Signature)],
    only: Option<&AggregateClaims>,
) -> Result<Aggregate, Error> {
    if children.len() > MAX_CHILDREN {
        return Err(Error::TooManyChildren {
            count: children.len(),
            max: MAX_CHILDREN,
        });
    }
    // A forked child fails before verifying anything; `start` claims the pool once the inputs pass.
    unclaimed_or_ours(&POOL_OWNER)?;
    // An invalid signature would otherwise surface as a failed proof; checking first names it.
    for (index, (public_key, message, signature)) in xmss.iter().enumerate() {
        public_key
            .verify(message, signature)
            .map_err(|_| Error::InvalidXmssInput {
                index,
                leaf_index: signature.leaf_index(),
            })?;
    }
    for (index, (public_key, message, signature)) in sphincs.iter().enumerate() {
        public_key
            .verify(message, signature)
            .map_err(|_| Error::InvalidSphincsInput { index })?;
    }
    let children: Vec<_> = children
        .iter()
        .map(|child| (child.claims.clone(), child.proof.clone()))
        .collect();
    let xmss: Vec<_> = xmss
        .iter()
        .map(|(public_key, message, signature)| (public_key.0, *message, signature.0.clone()))
        .collect();
    let sphincs: Vec<_> = sphincs
        .iter()
        .map(|(public_key, message, signature)| (public_key.0, *message, signature.0.clone()))
        .collect();
    start(0)?;
    let output = only.map_or(OutputClaims::All, OutputClaims::Only);
    // No DA blobs.
    let (claims, proof) = lean_vm::aggregate(&children, xmss, sphincs, None, output, LOG_INV_RATE)
        .map_err(|reason| Error::Aggregation {
            reason: reason.to_string(),
        })?;
    Ok(Aggregate { claims, proof })
}

/// A verified recursive proof that each listed public key signed its message.
///
/// - Every value was either proven here or decoded and verified against the claims it lists.
/// - A claim names a public key and a message, never the leaf index used.
/// - Its encoding is the proof alone: send the claims alongside, or let the receiver rebuild them.
#[derive(Clone)]
pub struct Aggregate {
    claims: AggregateClaims,
    proof: AggregateProof,
}

impl Aggregate {
    /// Verifies that a proof proves exactly these claims, and returns it as an aggregate.
    ///
    /// The claims may come in any order, and a repeated claim counts once.
    ///
    /// # Errors
    ///
    /// - Fails when the bytes are not a proof of exactly these claims.
    /// - Fails in a process forked while its parent was building the aggregation guest.
    pub fn from_bytes(
        bytes: &[u8],
        xmss_claims: &[(xmss::PublicKey, Message)],
        sphincs_claims: &[(sphincs::PublicKey, Message)],
    ) -> Result<Self, Error> {
        build_guest()?;
        let proof = AggregateProof::from_bytes(bytes).ok_or(Error::MalformedAggregate)?;
        let claims = statement(xmss_claims, sphincs_claims);
        if !proof.verify(&claims) {
            return Err(Error::AggregateRejected);
        }
        Ok(Self { claims, proof })
    }

    /// Encodes the proof, without its claims.
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        self.proof.to_bytes()
    }

    /// Returns the proven leanXMSS claims, strictly sorted by public key then message.
    #[must_use]
    pub fn xmss_claims(&self) -> Vec<(xmss::PublicKey, Message)> {
        self.claims
            .lean_xmss
            .iter()
            .map(|&(key, message)| (xmss::PublicKey(key), message))
            .collect()
    }

    /// Returns the proven leanSPHINCS claims, strictly sorted by public key then message.
    #[must_use]
    pub fn sphincs_claims(&self) -> Vec<(sphincs::PublicKey, Message)> {
        self.claims
            .lean_sphincs
            .iter()
            .map(|&(key, message)| (sphincs::PublicKey(key), message))
            .collect()
    }
}

impl fmt::Debug for Aggregate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Claim counts identify an aggregate in a log.
        // The proof bytes would drown it.
        f.debug_struct("Aggregate")
            .field("xmss_claims", &self.claims.lean_xmss.len())
            .field("sphincs_claims", &self.claims.lean_sphincs.len())
            .finish_non_exhaustive()
    }
}

/// The statement proving exactly these claims: each list strictly sorted, as a proof lists them.
fn statement(
    xmss_claims: &[(xmss::PublicKey, Message)],
    sphincs_claims: &[(sphincs::PublicKey, Message)],
) -> AggregateClaims {
    AggregateClaims {
        lean_xmss: sorted_claims(xmss_claims.iter().map(|(key, message)| (key.0, *message))),
        lean_sphincs: sorted_claims(
            sphincs_claims
                .iter()
                .map(|(key, message)| (key.0, *message)),
        ),
        // These bindings neither make nor accept leanDA blob commitments.
        da_commitment: None,
    }
}

fn sorted_claims<K: Ord>(claims: impl Iterator<Item = (K, Message)>) -> Vec<(K, Message)> {
    let mut claims: Vec<_> = claims.collect();
    claims.sort_unstable();
    claims.dedup();
    claims
}
