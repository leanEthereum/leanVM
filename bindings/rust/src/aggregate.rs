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
use std::sync::OnceLock;

use lean_vm::{
    aggregate as prove, setup as setup_lean_vm, AggregateClaims, AggregateProof, OutputClaims,
    MAX_LOG_INV_RATE, MAX_RECURSIONS, MIN_LOG_INV_RATE,
};

use crate::{sphincs, xmss, Error, Message};

/// The most children one aggregation recurses over.
pub const MAX_CHILDREN: usize = 16;

// Invariant: the limit above is the guest's, checked at compile time.
const _: () = assert!(MAX_CHILDREN == MAX_RECURSIONS);

/// Exponent of the proof's Reed-Solomon code rate, `rho = 2^-2 = 1/4`.
///
/// - leanVM accepts exponents 1 to 4.
/// - A larger exponent gives a smaller proof but slower proving.
const LOG_INV_RATE: usize = 2;

const _: () = assert!(MIN_LOG_INV_RATE <= LOG_INV_RATE && LOG_INV_RATE <= MAX_LOG_INV_RATE);

/// The process that started the prover pool and built the guest, once.
///
/// A child forked after the start inherits it but not the pool's threads.
static SETUP: OnceLock<u32> = OnceLock::new();

/// Starts leanVM's prover pool, one thread per core, and builds the aggregation guest, once per
/// process.
///
/// Aggregating and decoding call it themselves, so calling it only moves that cost earlier. A
/// process forked after the start cannot aggregate: start it before, or without forking.
pub fn setup() {
    setup_process();
}

fn setup_process() -> u32 {
    *SETUP.get_or_init(|| {
        setup_lean_vm(0);
        std::process::id()
    })
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
    /// Decodes a proof and verifies that it proves exactly these claims.
    ///
    /// The claims may come in any order, and a repeated claim counts once.
    ///
    /// # Errors
    ///
    /// - Fails when the bytes are not an encoded aggregate proof.
    /// - Fails when the proof does not prove exactly these claims.
    pub fn from_bytes(
        bytes: &[u8],
        xmss_claims: &[(xmss::PublicKey, Message)],
        sphincs_claims: &[(sphincs::PublicKey, Message)],
    ) -> Result<Self, Error> {
        // Verification needs the guest's tables.
        setup();
        let proof = AggregateProof::from_bytes(bytes).ok_or(Error::MalformedAggregate)?;
        let claims = AggregateClaims {
            lean_xmss: sorted_claims(xmss_claims.iter().map(|(key, message)| (key.0, *message))),
            lean_sphincs: sorted_claims(
                sphincs_claims
                    .iter()
                    .map(|(key, message)| (key.0, *message)),
            ),
            // These bindings neither make nor accept leanDA blob commitments.
            da_commitment: None,
        };
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

/// Claims strictly sorted, the order a proof's statement lists them in.
fn sorted_claims<K: Ord>(claims: impl Iterator<Item = (K, Message)>) -> Vec<(K, Message)> {
    let mut claims: Vec<_> = claims.collect();
    claims.sort_unstable();
    claims.dedup();
    claims
}

/// Proves raw signatures and child aggregates together as one aggregate.
///
/// ```text
///     claims(result) = claims(children) + claims(raw inputs)
///                      sorted, one entry per (public key, message)
/// ```
///
/// - Raw signatures are verified first, so a bad one is named by its index.
/// - Children are borrowed, and the guest re-verifies each one inside the new proof.
/// - One proof runs at a time per process, and concurrent calls wait.
///
/// # Errors
///
/// - Fails when more than 16 children are given.
/// - Fails when a raw signature does not verify, naming its list and index.
/// - Fails when the prover rejects the input, for example when it is empty.
/// - Fails in a process forked after the prover pool started, which has the pool but not its
///   threads.
pub fn aggregate(
    children: &[&Aggregate],
    xmss: &[(xmss::PublicKey, Message, xmss::Signature)],
    sphincs: &[(sphincs::PublicKey, Message, sphincs::Signature)],
) -> Result<Aggregate, Error> {
    // Reject an oversized fan-in before cloning any proof.
    if children.len() > MAX_CHILDREN {
        return Err(Error::TooManyChildren {
            count: children.len(),
            max: MAX_CHILDREN,
        });
    }

    // Why: the prover catches only some invalid signatures, and the rest make proving fail.
    //
    // Checking here turns every one into an error that names the culprit.
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

    // The prover takes owned inputs: copy the proofs and unwrap the signature types.
    let children: Vec<(AggregateClaims, AggregateProof)> = children
        .iter()
        .map(|child| (child.claims.clone(), child.proof.clone()))
        .collect();
    let xmss = xmss
        .iter()
        .map(|(public_key, message, signature)| (public_key.0, *message, signature.0.clone()))
        .collect();
    let sphincs = sphincs
        .iter()
        .map(|(public_key, message, signature)| (public_key.0, *message, signature.0.clone()))
        .collect();

    if setup_process() != std::process::id() {
        return Err(Error::ForkedAfterSetup);
    }
    // No DA blobs, and keep every claim the inputs cover.
    prove(
        &children,
        xmss,
        sphincs,
        None,
        OutputClaims::All,
        LOG_INV_RATE,
    )
    .map(|(claims, proof)| Aggregate { claims, proof })
    .map_err(|reason| Error::Aggregation { reason })
}
