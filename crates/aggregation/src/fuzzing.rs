//! The fuzzer's way into a node: a malicious host's edits to the guest's witness and to its children, and a run
//! of the guest without the proof, which is where a node's soundness is decided at a fraction of a proof's cost.
//!
//! A guest run that succeeds is a witness the prover would prove: the proof then verifies, since
//! `Prover::prove` only refuses unconstrained reads, which [`run_guest`] refuses too.

use super::deferred::{DeferredBytecodeClaim, bytecode_vars as deferred_vars};
use super::error::AggregateError;
use super::guest::{fs_seed, unified_guest};

#[cfg(any(test, feature = "fuzzing"))]
use super::hints::FORGE;
use super::hints::Forgery;
pub use super::hints::Hints;
pub use super::node::build_node;
pub use super::error::AggregateError as AggregationError;
pub use crate::{AggregateClaims as EthereumClaims, LeanSphincsClaim, LeanXmssClaim, MAX_RECURSIONS};
pub use crate::proof::OutputClaims;
use super::placeholders::placeholder_map;
use super::proof::{AggregateClaims, AggregateProof};
use super::statement::statement_digest;
use isa::{Program, Prover};
use lean_vm_core::cpu::{self, ProveError};
use lean_xmss::{LeanXmssPublicKey, LeanXmssSignature};
use lean_sphincs::{LeanSphincsPublicKey, LeanSphincsSignature};
use primitives::field::F128;
use verifier::E;

/// The next node this thread builds, [`super::aggregate`](crate::aggregate) or [`execute_node`], hands its guest
/// the witness `forgery` makes of the honest one.
pub fn arm_forgery(forgery: Forgery) {
    FORGE.with(|forge| *forge.borrow_mut() = Some(forgery));
}

/// Drop a forgery no node took.
pub fn disarm_forgery() {
    FORGE.with(|forge| forge.borrow_mut().take());
}

/// A node's guest, run and not proven.
pub struct NodeRun {
    /// The statement the run had to reach.
    pub public_input: [F128; 2],
    /// What the aggregate would claim.
    pub claims: AggregateClaims,
    /// The guest's witness streams, in the order the guest pops them, as the prover's words.
    pub witness: Vec<(String, Vec<Vec<F128>>)>,
    /// The guest's witness streams as the prover's `Prover::prove` takes them.
    pub scalar_witness: Vec<(String, Vec<Vec<E>>)>,
    /// The guest, to prove with.
    pub program: &'static Program,
    /// The run's cycles, or why `prove` would refuse it.
    pub run: Result<usize, ProveError>,
    /// The deferred claim the aggregate would carry: its point and value.
    pub defer_point: Vec<F128>,
    pub defer_value: F128,
}

/// Build a node as [`super::aggregate`](crate::aggregate) does, applying an armed forgery, and run its guest
/// instead of proving it. `Err` is what `aggregate` returns before proving; a refused run is in [`NodeRun::run`].
pub fn execute_node<P: Prover>(
    children: &[(AggregateClaims, AggregateProof)],
    raw_lean_xmss: Vec<(LeanXmssPublicKey, lean_xmss::Message, LeanXmssSignature)>,
    raw_lean_sphincs: Vec<(LeanSphincsPublicKey, lean_sphincs::Message, LeanSphincsSignature)>,
    blobs: Option<&lean_da::BlobMatrix>,
    output: OutputClaims,
) -> Result<NodeRun, AggregateError> {
    let node = build_node::<P>(children, raw_lean_xmss, raw_lean_sphincs, blobs, output)?;
    let scalar_witness = node.hints.witness();
    let witness: Vec<(String, Vec<Vec<F128>>)> = scalar_witness
        .iter()
        .map(|(name, entries)| {
            let scalars = |entry: &Vec<E>| -> Vec<F128> { entry.iter().map(|x| cpu::from_scalar(*x)).collect() };
            (name.clone(), entries.iter().map(scalars).collect())
        })
        .collect();
    let run = run_guest(&witness, node.public_input);
    let program = unified_guest();
    Ok(NodeRun {
        public_input: node.public_input,
        claims: node.claims,
        witness,
        scalar_witness,
        program,
        run,
        defer_point: node.defer.bytecode_point,
        defer_value: node.defer.bytecode_value,
    })
}

/// [`execute_node`] without the run, its [`NodeRun::run`] an `Ok(0)` placeholder: for a caller that runs the
/// guest against a statement of its own ([`run_guest`]).
pub fn prepare_node<P: Prover>(
    children: &[(AggregateClaims, AggregateProof)],
    raw_lean_xmss: Vec<(LeanXmssPublicKey, lean_xmss::Message, LeanXmssSignature)>,
    raw_lean_sphincs: Vec<(LeanSphincsPublicKey, lean_sphincs::Message, LeanSphincsSignature)>,
    blobs: Option<&lean_da::BlobMatrix>,
    output: OutputClaims,
) -> Result<NodeRun, AggregateError> {
    let node = build_node::<P>(children, raw_lean_xmss, raw_lean_sphincs, blobs, output)?;
    let scalar_witness = node.hints.witness();
    let witness: Vec<(String, Vec<Vec<F128>>)> = scalar_witness
        .iter()
        .map(|(name, entries)| {
            let scalars = |entry: &Vec<E>| -> Vec<F128> { entry.iter().map(|x| cpu::from_scalar(*x)).collect() };
            (name.clone(), entries.iter().map(scalars).collect())
        })
        .collect();
    Ok(NodeRun {
        public_input: node.public_input,
        claims: node.claims,
        witness,
        scalar_witness,
        program: unified_guest(),
        run: Ok(0),
        defer_point: node.defer.bytecode_point,
        defer_value: node.defer.bytecode_value,
    })
}

/// Run a node's guest against `public_input`: its cycles, or why `prove` would refuse the run.
pub fn run_guest(witness: &[(String, Vec<Vec<F128>>)], public_input: [F128; 2]) -> Result<usize, ProveError> {
    let witness: Vec<(String, Vec<Vec<F128>>)> = witness
        .iter()
        .map(|(name, entries)| {
            let scalars = |entry: &Vec<F128>| -> Vec<F128> { entry.clone() };
            (name.clone(), entries.iter().map(scalars).collect())
        })
        .collect();
    let program = unified_guest();
    match cpu::execute(program, &witness, [public_input[0], public_input[1]]) {
        Err(e) => Err(ProveError::Execution(e)),
        Ok(exec) if !exec.unconstrained_reads.is_empty() => {
            Err(ProveError::UnconstrainedReads(exec.unconstrained_reads))
        }
        Ok(exec) => Ok(exec.cycles),
    }
}

/// The VM statement of an aggregate of `claims` deferring `value` at `point`, nothing checked: what a forged
/// witness has to reach when it claims something else.
pub fn statement_of(claims: &AggregateClaims, point: &[F128], value: F128) -> [F128; 2] {
    let defer = DeferredBytecodeClaim { bytecode_point: point.to_vec(), bytecode_value: value };
    statement_digest(claims, &defer)
}

/// The stacked bytecode's true value at `point`, as [`AggregateProof::verify`] recomputes it.
pub fn true_deferred_value(point: &[F128]) -> Option<F128> {
    (point.len() == deferred_vars()).then(|| DeferredBytecodeClaim::recompute(point.to_vec()).bytecode_value)
}

/// What a leaf defers: the all-zeros point and the value there.
pub fn leaf_deferred() -> (Vec<F128>, F128) {
    let leaf = DeferredBytecodeClaim::leaf();
    (leaf.bytecode_point, leaf.bytecode_value)
}

/// The stacked bytecode prepared for the verifier, what [`AggregateProof::verify`] checks proofs against.
pub fn scalar_bytecode() -> &'static verifier::Bytecode {
    unified_guest().bytecode()
}

/// The guest's source and the placeholders the unified guest fills it with, for a fuzzer that mutates the guest.
pub fn guest_source() -> (&'static str, std::collections::BTreeMap<String, String>) {
    let kbc = unified_guest().prog.len().trailing_zeros() as usize;
    (include_str!("../../../guests/lean_ethereum.py"), placeholder_map(kbc))
}

/// The seed of the guest's own Fiat-Shamir IV, as two cells.
pub fn seed() -> [F128; 2] {
    fs_seed()
}


// ---- the pre-restructure surface the fuzz targets are written against ----
// `EthereumProof` (a proof carrying its claims) and the compat `aggregate`, on the new API, generic over
// the prover so a campaign exercises both trees.

use lean_da::BlobMatrix;

/// Why a compat [`EthereumProof`] was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AggregateVerifyError {
    MalformedEncoding,
    MalformedSignerSet,
    MalformedClaim,
    Snark(String),
}

impl std::fmt::Display for AggregateVerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedEncoding => write!(f, "malformed encoding"),
            Self::MalformedSignerSet => write!(f, "malformed signer set"),
            Self::MalformedClaim => write!(f, "malformed claim"),
            Self::Snark(error) => write!(f, "snark: {error}"),
        }
    }
}

/// An [`AggregateProof`] carrying the claims it attests: the fuzz targets' shape.
#[derive(Clone, Debug)]
pub struct EthereumProof {
    pub claims: AggregateClaims,
    /// The deferred bytecode claim the aggregate carries: its point and value.
    pub defer: DeferredBytecodeClaim,
    proof: AggregateProof,
}

impl EthereumProof {
    /// The aggregate `bytes` encode, attesting `claims`.
    pub fn from_proof_bytes(bytes: &[u8], claims: AggregateClaims) -> Result<Self, AggregateVerifyError> {
        if !crate::proof::is_sorted(&claims) {
            return Err(AggregateVerifyError::MalformedSignerSet);
        }
        let proof = AggregateProof::from_bytes(bytes).ok_or(AggregateVerifyError::MalformedEncoding)?;
        let defer = DeferredBytecodeClaim::recompute(proof.bytecode_point.clone());
        Ok(Self { claims, defer, proof })
    }

    /// The deferred point and the proof, on the wire.
    pub fn proof_bytes(&self) -> Vec<u8> {
        self.proof.to_bytes()
    }

    /// Whether this proves its claims: the lists are sorted, the deferred claim holds, and the proof verifies.
    pub fn verify(&self) -> Result<(), AggregateVerifyError> {
        let defer = DeferredBytecodeClaim::recompute(self.proof.bytecode_point.clone());
        if defer.bytecode_value != self.defer.bytecode_value {
            return Err(AggregateVerifyError::MalformedClaim);
        }
        if self.proof.verify(&self.claims) {
            Ok(())
        } else {
            let error = format!("{:?}", self.proof);
            Err(AggregateVerifyError::Snark(error))
        }
    }

    pub fn claims(&self) -> &AggregateClaims {
        &self.claims
    }

    pub fn vm_proof(&self) -> &verifier::Proof {
        &self.proof.proof
    }

    /// The deferred claim's point and value.
    pub fn deferred(&self) -> (&[F128], F128) {
        (&self.proof.bytecode_point, self.defer.bytecode_value)
    }

    /// The proof half of the aggregate, claims dropped.
    pub fn into_inner(self) -> AggregateProof {
        self.proof
    }

    /// The aggregate's parts: claims, the deferred claim's point and value, and the proof.
    pub fn into_parts(self) -> Parts {
        let defer_point = self.proof.bytecode_point.clone();
        Parts {
            claims: self.claims,
            defer_point,
            defer_value: self.defer.bytecode_value,
            proof: self.proof,
        }
    }

    /// An aggregate from its parts, nothing checked or recomputed: a malicious child's shape.
    pub fn from_parts(parts: Parts) -> Self {
        Self {
            claims: parts.claims,
            defer: DeferredBytecodeClaim {
                bytecode_point: parts.defer_point,
                bytecode_value: parts.defer_value,
            },
            proof: parts.proof,
        }
    }
}

/// An aggregate's parts: its claims, the deferred claim's point and value, and the proof.
pub struct Parts {
    pub claims: AggregateClaims,
    pub defer_point: Vec<F128>,
    pub defer_value: F128,
    pub proof: AggregateProof,
}

/// A child as [`aggregate_compat`] takes it: the claims the parent's coverage adopts, and the proof.
pub fn child_of(proof: &EthereumProof) -> (AggregateClaims, AggregateProof) {
    (proof.claims.clone(), proof.into_inner_cloned())
}

impl EthereumProof {
    fn into_inner_cloned(&self) -> AggregateProof {
        AggregateProof { bytecode_point: self.proof.bytecode_point.clone(), proof: self.proof.proof.clone() }
    }
}

/// The compat aggregate: children as [`EthereumProof`]s, blobs as raw symbols, [`OutputClaims::All`] without a
/// declaration, on the prover `P`.
pub fn aggregate_compat<P: Prover>(
    children: &[EthereumProof],
    raw_lean_xmss: Vec<(LeanXmssPublicKey, lean_xmss::Message, LeanXmssSignature)>,
    raw_lean_sphincs: Vec<(LeanSphincsPublicKey, lean_sphincs::Message, LeanSphincsSignature)>,
    blobs: &[u64],
    declare: Option<&AggregateClaims>,
    log_inv_rate: usize,
) -> Result<EthereumProof, AggregateError> {
    let children: Vec<(AggregateClaims, AggregateProof)> =
        children.iter().map(child_of).collect();
    let blobs = (!blobs.is_empty())
        .then(|| {
            let rows: Vec<lean_da::Blob> = blobs
                .chunks(lean_da::BLOB_SYMBOLS)
                .map(|chunk| {
                    let mut blob = [0; lean_da::BLOB_SYMBOLS];
                    for (word, symbol) in blob.iter_mut().zip(chunk) {
                        *word = *symbol as u128;
                    }
                    blob
                })
                .collect();
            BlobMatrix::build(&rows)
        })
        .transpose()
        .map_err(|_| AggregateError::InvalidInput("blob symbols"))?;
    let output = match declare {
        None => OutputClaims::All,
        Some(claims) => OutputClaims::Only(claims),
    };
    let (claims, proof, _) = super::aggregate::<P>(&children, raw_lean_xmss, raw_lean_sphincs, blobs.as_ref(), output, log_inv_rate)?;
    let defer = DeferredBytecodeClaim::recompute(proof.bytecode_point.clone());
    Ok(EthereumProof { claims, defer, proof })
}
