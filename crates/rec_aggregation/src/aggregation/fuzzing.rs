//! The fuzzer's way into a node: a malicious host's edits to the guest's witness and to its children, and a run
//! of the guest without the proof, which is where a node's soundness is decided at a fraction of a proof's cost.
//!
//! A guest run that succeeds is a witness the prover would prove: the proof then verifies, since
//! [`leanvm_core::cpu::prove`] only refuses unconstrained reads, which [`execute_node`] refuses too.

use super::EthereumClaims;
use super::deferred::DeferredClaim;
use super::error::{AggregationError, SnarkProveError};
use super::guest::unified_guest;
use super::hints::FORGE;
pub use super::hints::{Forgery, Hints};
use super::node::build_node;
use super::placeholders::placeholder_map;
use super::proof::EthereumProof;
use leanvm_core::cpu::{Program, ProveError};
use primitives::field::F192;
use signatures::lean_sphincs::{LeanSphincsPublicKey, LeanSphincsSignature};
use signatures::lean_xmss::{LeanXmssPublicKey, LeanXmssSignature};
use signatures::{lean_sphincs, lean_xmss};

/// The next node this thread builds, [`super::aggregate`] or [`execute_node`], hands its guest the witness
/// `forgery` makes of the honest one.
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
    pub public_input: [F192; 2],
    /// What the aggregate would claim.
    pub claims: EthereumClaims,
    /// The guest with its witness, for a caller to run again or prove.
    pub program: Program,
    /// The run's cycles, or why `prove` would refuse it.
    pub run: Result<usize, ProveError>,
    /// The deferred claim the aggregate would carry: its point and value.
    pub defer_point: Vec<F192>,
    pub defer_value: F192,
}

/// Build a node as [`super::aggregate`] does, applying an armed forgery, and run its guest instead of proving it.
/// `Err` is what `aggregate` returns before proving; a refused run is in [`NodeRun::run`].
pub fn execute_node(
    children: &[EthereumProof],
    raw_lean_xmss: Vec<(LeanXmssPublicKey, lean_xmss::Message, LeanXmssSignature)>,
    raw_lean_sphincs: Vec<(LeanSphincsPublicKey, lean_sphincs::Message, LeanSphincsSignature)>,
    blobs: &[u64],
    declare: Option<&EthereumClaims>,
) -> Result<NodeRun, AggregationError> {
    let mut node = prepare_node(children, raw_lean_xmss, raw_lean_sphincs, blobs, declare)?;
    node.run = run_guest(&node.program, node.public_input);
    Ok(node)
}

/// [`execute_node`] without the run, its [`NodeRun::run`] an `Ok(0)` placeholder: for a caller that runs the
/// guest against a statement of its own ([`run_guest`]).
pub fn prepare_node(
    children: &[EthereumProof],
    raw_lean_xmss: Vec<(LeanXmssPublicKey, lean_xmss::Message, LeanXmssSignature)>,
    raw_lean_sphincs: Vec<(LeanSphincsPublicKey, lean_sphincs::Message, LeanSphincsSignature)>,
    blobs: &[u64],
    declare: Option<&EthereumClaims>,
) -> Result<NodeRun, AggregationError> {
    let node = build_node(children, raw_lean_xmss, raw_lean_sphincs, blobs, declare)?;
    Ok(NodeRun {
        public_input: node.public_input,
        claims: node.claims,
        program: node.program,
        run: Ok(0),
        defer_point: node.defer.bytecode_point,
        defer_value: node.defer.bytecode_value,
    })
}

/// Run a node's guest against `public_input`: its cycles, or why `prove` would refuse the run.
pub fn run_guest(program: &Program, public_input: [F192; 2]) -> Result<usize, ProveError> {
    match program.execute(public_input) {
        Err(e) => Err(ProveError::Execution(e)),
        Ok(exec) if !exec.unconstrained_reads.is_empty() => {
            Err(ProveError::UnconstrainedReads(exec.unconstrained_reads))
        }
        Ok(exec) => Ok(exec.cycles),
    }
}

/// The VM statement of an aggregate of `claims` deferring `value` at `point`, nothing checked: what a forged
/// witness has to reach when it claims something else.
pub fn statement_of(claims: &EthereumClaims, point: &[F192], value: F192) -> [F192; 2] {
    let defer = DeferredClaim {
        bytecode_point: point.to_vec(),
        bytecode_value: value,
    };
    let da = verifier::da::digest(claims.da_commitment);
    super::statement::statement_digest(&claims.xmss, &claims.lean_sphincs, da, &defer)
}

/// The stacked bytecode's true value at `point`, as [`EthereumProof::verify`] recomputes it; `None` for a point
/// of the wrong length.
pub fn true_deferred_value(point: &[F192]) -> Option<F192> {
    DeferredClaim::recompute_scalar(point.to_vec())
        .ok()
        .map(|claim| claim.bytecode_value)
}

/// What a leaf defers: the all-zeros point and the value there.
pub fn leaf_deferred() -> (Vec<F192>, F192) {
    let leaf = DeferredClaim::leaf();
    (leaf.bytecode_point, leaf.bytecode_value)
}

/// Map a refused run to what [`super::aggregate`] would have returned.
pub fn as_aggregation_error(e: ProveError) -> AggregationError {
    AggregationError::ProofError(SnarkProveError(e))
}

/// An aggregate's parts: its claims, the deferred claim's point and value, and the VM proof.
pub struct Parts {
    pub claims: EthereumClaims,
    pub defer_point: Vec<F192>,
    pub defer_value: F192,
    pub proof: leanvm_core::cpu::Proof,
}

impl EthereumProof {
    pub fn into_parts(self) -> Parts {
        Parts {
            claims: self.claims,
            defer_point: self.defer.bytecode_point,
            defer_value: self.defer.bytecode_value,
            proof: self.proof,
        }
    }

    /// An aggregate as a malicious child presents it: nothing is checked or recomputed, the deferred value
    /// included, which the wire never carries.
    pub fn from_parts(parts: Parts) -> Self {
        Self {
            claims: parts.claims,
            defer: DeferredClaim {
                bytecode_point: parts.defer_point,
                bytecode_value: parts.defer_value,
            },
            proof: parts.proof,
        }
    }

    /// The VM statement the aggregate's proof is about.
    pub fn statement(&self) -> [F192; 2] {
        self.vm_public_input()
    }

    /// The VM proof, read only.
    pub fn vm_proof(&self) -> &leanvm_core::cpu::Proof {
        &self.proof
    }

    /// The deferred claim's point and value.
    pub fn deferred(&self) -> (&[F192], F192) {
        (&self.defer.bytecode_point, self.defer.bytecode_value)
    }
}

/// The guest's source and the placeholders the unified guest fills it with, for a fuzzer that mutates the guest.
pub fn guest_source() -> (&'static str, std::collections::BTreeMap<String, String>) {
    let kbc = unified_guest().prog().len().trailing_zeros() as usize;
    (include_str!("../../guests/lean_ethereum.py"), placeholder_map(kbc))
}
