//! What the aggregation targets share: a node's inputs, how its outcome is named, and the oracle every accepted
//! run answers to: each published claim backed by a valid raw signature or a verified child, the DA root by the
//! node's blobs or a verified child.

use super::fixtures::{Fixtures, RawSphincs, RawXmss, root_of};
use crate::programs::fault_kind;
use crate::{Finding, Source};
use leanvm_core::cpu::ProveError;
use primitives::field::{F64, F192, g_pow};
use rec_aggregation::fuzzing::{NodeRun, execute_node};
use rec_aggregation::{AggregateVerifyError, AggregationError, EthereumClaims, EthereumProof};
use signatures::{lean_sphincs, lean_xmss};
use std::collections::{BTreeSet, HashMap};
use std::sync::OnceLock;

/// A node's hint streams, by name, each entry in the order the guest pops them.
pub type Streams = Vec<(String, Vec<Vec<F192>>)>;

/// One node's inputs, as `aggregate` takes them.
#[derive(Clone, Default)]
pub struct Inputs {
    pub children: Vec<EthereumProof>,
    /// Which fixture each child is, or a name for a forged one, for the finding's detail.
    pub names: Vec<String>,
    pub xmss: Vec<RawXmss>,
    pub sphincs: Vec<RawSphincs>,
    pub blobs: Vec<u64>,
    pub declare: Option<EthereumClaims>,
}

impl Inputs {
    pub fn child(&mut self, f: &Fixtures, i: usize) {
        self.children.push(f.proof(i).clone());
        self.names.push(f.children[i].name.to_string());
    }

    pub fn forged_child(&mut self, proof: EthereumProof, name: &str) {
        self.children.push(proof);
        self.names.push(name.to_string());
    }

    pub fn execute(&self) -> Result<NodeRun, AggregationError> {
        execute_node(
            &self.children,
            self.xmss.clone(),
            self.sphincs.clone(),
            &self.blobs,
            self.declare.as_ref(),
        )
    }

    pub fn describe(&self) -> String {
        format!(
            "children {:?}, {} raw leanXMSS {:?}, {} raw leanSPHINCS {:?}, {} blob rows, declare {}",
            self.names,
            self.xmss.len(),
            self.xmss
                .iter()
                .map(|(pk, m, s)| (short(&pk.to_bytes()), short(m), s.leaf_index()))
                .collect::<Vec<_>>(),
            self.sphincs.len(),
            self.sphincs
                .iter()
                .map(|(pk, m, _)| (short(&pk.to_bytes()), short(m)))
                .collect::<Vec<_>>(),
            self.blobs.len() / lean_da::BLOB_SYMBOLS,
            self.declare.as_ref().map_or("None".to_string(), describe_claims),
        )
    }

    /// What a successful run may publish: [`Backing`] of these inputs.
    pub fn backing(&self) -> Backing {
        Backing::of(&self.children, &self.xmss, &self.sphincs, &self.blobs)
    }

    /// What `aggregate` publishes on these inputs, when they are valid: the declared claims, or every claim, and
    /// the DA root `aggregate`'s rules pick.
    pub fn expected_claims(&self) -> EthereumClaims {
        if let Some(d) = &self.declare {
            let mut c = d.clone();
            super::fixtures::normalize(&mut c);
            return c;
        }
        let mut c = super::fixtures::claims_of(&self.xmss, &self.sphincs, None);
        for child in &self.children {
            c = super::fixtures::union(&c, child.claims());
        }
        c.da_commitment = if self.blobs.is_empty() {
            self.children.iter().find_map(|child| child.claims().da_commitment)
        } else {
            Some(root_of(&self.blobs))
        };
        c
    }
}

pub fn short(bytes: &[u8]) -> String {
    bytes[..4].iter().map(|b| format!("{b:02x}")).collect()
}

pub fn describe_claims(c: &EthereumClaims) -> String {
    format!(
        "{{xmss {:?}, sphincs {:?}, da {:?}}}",
        c.xmss
            .iter()
            .map(|(pk, m)| (short(&pk.to_bytes()), short(m)))
            .collect::<Vec<_>>(),
        c.lean_sphincs
            .iter()
            .map(|(pk, m)| (short(&pk.to_bytes()), short(m)))
            .collect::<Vec<_>>(),
        c.da_commitment.map(|r| short(&r)),
    )
}

/// The claims a node's inputs can back: raw signatures that verify natively, the claims of children that verify,
/// and the roots of its blobs and of those children.
pub struct Backing {
    pub xmss: BTreeSet<([u8; 32], [u8; 32])>,
    pub sphincs: BTreeSet<([u8; 32], [u8; 32])>,
    pub roots: BTreeSet<[u8; 32]>,
}

impl Backing {
    pub fn of(children: &[EthereumProof], xmss: &[RawXmss], sphincs: &[RawSphincs], blobs: &[u64]) -> Self {
        let mut b = Backing {
            xmss: BTreeSet::new(),
            sphincs: BTreeSet::new(),
            roots: BTreeSet::new(),
        };
        for (pk, m, sig) in xmss {
            if lean_xmss::verify(pk, m, sig).is_ok() {
                b.xmss.insert((pk.to_bytes(), *m));
            }
        }
        for (pk, m, sig) in sphincs {
            if lean_sphincs::verify(pk, m, sig).is_ok() {
                b.sphincs.insert((pk.to_bytes(), *m));
            }
        }
        if !blobs.is_empty()
            && let Ok((root, _)) = lean_da::commit(blobs)
        {
            b.roots.insert(root);
        }
        for child in children {
            if child.verify().is_ok() {
                let c = child.claims();
                b.xmss.extend(c.xmss.iter().map(|(pk, m)| (pk.to_bytes(), *m)));
                b.sphincs
                    .extend(c.lean_sphincs.iter().map(|(pk, m)| (pk.to_bytes(), *m)));
                b.roots.extend(c.da_commitment);
            }
        }
        b
    }

    /// The first published claim nothing backs, named.
    pub fn unbacked(&self, c: &EthereumClaims) -> Option<String> {
        for (pk, m) in &c.xmss {
            if !self.xmss.contains(&(pk.to_bytes(), *m)) {
                return Some(format!(
                    "leanXMSS claim ({}, {}) has no valid signature behind it",
                    short(&pk.to_bytes()),
                    short(m)
                ));
            }
        }
        for (pk, m) in &c.lean_sphincs {
            if !self.sphincs.contains(&(pk.to_bytes(), *m)) {
                return Some(format!(
                    "leanSPHINCS claim ({}, {}) has no valid signature behind it",
                    short(&pk.to_bytes()),
                    short(m)
                ));
            }
        }
        if let Some(root) = c.da_commitment
            && !self.roots.contains(&root)
        {
            return Some(format!(
                "DA root {} is neither the node's blobs' nor a verified child's",
                short(&root)
            ));
        }
        None
    }
}

/// A stable name for why a node was not built.
pub fn error_kind(e: &AggregationError) -> String {
    match e {
        AggregationError::InvalidChild(v) => format!("InvalidChild/{}", verify_kind(v)),
        AggregationError::Empty => "Empty".into(),
        AggregationError::NotCovered => "NotCovered".into(),
        AggregationError::MalformedRawSignature => "MalformedRawSignature".into(),
        AggregationError::TooLarge => "TooLarge".into(),
        AggregationError::InvalidBlobSize { .. } => "InvalidBlobSize".into(),
        AggregationError::BlobNotCovered => "BlobNotCovered".into(),
        AggregationError::BlobsUnpublished => "BlobsUnpublished".into(),
        AggregationError::InvalidRate { .. } => "InvalidRate".into(),
        AggregationError::ChildOutOfRange { .. } => "ChildOutOfRange".into(),
        AggregationError::ProofError(_) => "ProofError".into(),
    }
}

pub fn verify_kind(e: &AggregateVerifyError) -> &'static str {
    match e {
        AggregateVerifyError::MalformedSignerSet => "MalformedSignerSet",
        AggregateVerifyError::MalformedClaim => "MalformedClaim",
        AggregateVerifyError::MalformedEncoding => "MalformedEncoding",
        AggregateVerifyError::Snark(_) => "Snark",
    }
}

/// A stable name for why a run was refused.
pub fn refusal_kind(e: &ProveError) -> String {
    match e {
        ProveError::InvalidRate { .. } => "InvalidRate".into(),
        ProveError::PublicInputNotDigest => "PublicInputNotDigest".into(),
        ProveError::Execution(e) => format!("Execution/{}", fault_kind(&e.fault)),
        ProveError::UnconstrainedReads(_) => "UnconstrainedReads".into(),
        ProveError::WitnessOutOfRange { .. } => "WitnessOutOfRange".into(),
    }
}

/// How a node's build and run went: `Ok` for an accepted run, else a stable name of the refusal.
/// Where in the guest a refused run failed, as a note: `guest check <function> (line N)`. Over a campaign these notes
/// are the guest's kill map, which `leanvm-fuzz guest-coverage` sets against every check in `lean_ethereum.py`.
pub fn note_kill(ctx: &crate::Ctx, result: &Result<NodeRun, AggregationError>) {
    if let Ok(NodeRun {
        run: Err(leanvm_core::cpu::ProveError::Execution(e)),
        ..
    }) = result
    {
        ctx.note(format!("guest check {}", e.site));
    }
}

pub fn outcome(result: &Result<NodeRun, AggregationError>) -> Result<(), String> {
    match result {
        Err(e) => Err(error_kind(e)),
        Ok(run) => match &run.run {
            Ok(_) => Ok(()),
            Err(e) => Err(format!("refused/{}", refusal_kind(e))),
        },
    }
}

/// The full error of a build or run, for a finding's detail.
pub fn describe_outcome(result: &Result<NodeRun, AggregationError>) -> String {
    match result {
        Err(e) => format!("{e:?}"),
        Ok(run) => match &run.run {
            Ok(cycles) => format!("accepted in {cycles} cycles"),
            Err(e) => format!("refused: {e}"),
        },
    }
}

/// An accepted run answers to the backing oracle: Critical if it publishes anything its inputs do not back.
pub fn check_backed(context: &str, inputs: &Inputs, run: &NodeRun, extra: &str) -> Result<(), Finding> {
    if let Some(why) = inputs.backing().unbacked(&run.claims) {
        return Err(Finding::critical(
            format!("{context}: an accepted run publishes an unbacked claim"),
            format!(
                "{why}\npublished {}\ninputs: {}\n{extra}",
                describe_claims(&run.claims),
                inputs.describe()
            ),
        ));
    }
    Ok(())
}

/// `g^n`: a count as the guest carries it.
pub fn count(n: usize) -> F192 {
    F192::from(g_pow(n))
}

pub fn count_inv(n: usize) -> F192 {
    F192::from(g_pow(n).inv())
}

/// `n` for a cell `g^n` with `n < 2^17`.
pub fn log_g(x: F192) -> Option<usize> {
    static LOGS: OnceLock<HashMap<u64, usize>> = OnceLock::new();
    if x.c1 != 0 || x.c2 != 0 {
        return None;
    }
    let logs = LOGS.get_or_init(|| {
        let mut m = HashMap::new();
        let mut p = F64(1);
        let g = g_pow(1);
        for n in 0..1 << 17 {
            m.insert(p.0, n);
            p *= g;
        }
        m
    });
    logs.get(&x.c0).copied()
}

/// A count on an edge of the ranges the guest checks.
pub fn edge_count(src: &mut Source, near: usize) -> F192 {
    match src.below(10) {
        0 => count(0),
        1 => count(near.saturating_sub(1)),
        2 => count(near),
        3 => count(near + 1),
        4 => count(rec_aggregation::MAX_KEYS - 1),
        5 => count(rec_aggregation::MAX_KEYS),
        6 => count_inv(1),
        7 => count_inv(src.range(2, 64)),
        8 => count(rec_aggregation::MAX_RECURSIONS + src.below(3)),
        _ => count(1 << src.range(17, 30)),
    }
}

/// A 32-byte value as the two cells the guest holds it in.
pub fn cells_of(bytes: &[u8; 32]) -> [F192; 2] {
    let word = |o: usize| u64::from_le_bytes(bytes[o..o + 8].try_into().unwrap());
    [F192::new(word(0), word(8), 0), F192::new(word(16), word(24), 0)]
}

/// The 32 bytes two canonical cells hold.
pub fn bytes_of(cells: &[F192]) -> Option<[u8; 32]> {
    if cells.len() != 2 || cells.iter().any(|c| c.c2 != 0) {
        return None;
    }
    let mut out = [0; 32];
    for (i, c) in cells.iter().enumerate() {
        out[16 * i..16 * i + 8].copy_from_slice(&c.c0.to_le_bytes());
        out[16 * i + 8..16 * i + 16].copy_from_slice(&c.c1.to_le_bytes());
    }
    Some(out)
}

/// What a node's inputs deserve.
pub enum Expect {
    /// A run that publishes exactly these claims.
    Exactly(EthereumClaims),
    /// A refusal, its kind starting with one of these names.
    Refused(&'static [&'static str]),
}

/// A raw signature is refused by the guest, before it or by `lean_xmss_hints`.
pub const BAD_SIGNATURE: &[&str] = &["MalformedRawSignature", "refused/"];
/// A child no verifier accepts: refused by the replay, the shape check or the guest.
pub const BAD_CHILD: &[&str] = &["InvalidChild", "ChildOutOfRange", "refused/"];

/// Which raw signature `aggregate` keeps of each claim: the first given.
fn kept<T: Clone, K: PartialEq>(raw: &[T], key: impl Fn(&T) -> K) -> Vec<T> {
    let mut out: Vec<T> = Vec::new();
    for r in raw {
        if !out.iter().any(|o| key(o) == key(r)) {
            out.push(r.clone());
        }
    }
    out
}

/// What valid-looking inputs deserve: refused if a signature the node keeps does not verify natively, else exactly
/// [`Inputs::expected_claims`]. Assumes its children are fixtures and its `declare` covered.
pub fn expect_for(inputs: &Inputs) -> Expect {
    let xmss_ok = kept(&inputs.xmss, |(pk, m, _)| (pk.to_bytes(), *m))
        .iter()
        .all(|(pk, m, s)| lean_xmss::verify(pk, m, s).is_ok());
    let sphincs_ok = kept(&inputs.sphincs, |(pk, m, _)| (pk.to_bytes(), *m))
        .iter()
        .all(|(pk, m, s)| lean_sphincs::verify(pk, m, s).is_ok());
    if xmss_ok && sphincs_ok {
        Expect::Exactly(inputs.expected_claims())
    } else {
        Expect::Refused(BAD_SIGNATURE)
    }
}

/// Build and run a node, a panic being a finding: the outcome held to `expect`, and an accepted run to the
/// backing oracle. Returns the accepted run.
pub fn judge(ctx: &crate::Ctx, context: &str, inputs: &Inputs, expect: &Expect) -> Result<Option<NodeRun>, Finding> {
    let result = crate::catch(|| inputs.execute()).map_err(|(message, location)| {
        let mut finding = Finding::panic(&message, &location).in_context("aggregate panics");
        finding.detail = format!("{context}\n{}\ninputs: {}", finding.detail, inputs.describe());
        finding
    })?;
    note_kill(ctx, &result);
    match outcome(&result) {
        Ok(()) => {
            let run = result.expect("accepted");
            check_backed(context, inputs, &run, "")?;
            match expect {
                Expect::Exactly(want) if run.claims != *want => Err(Finding::high(
                    format!("{context}: publishes other claims than aggregate's rules"),
                    format!(
                        "published {}\nexpected {}\ninputs: {}",
                        describe_claims(&run.claims),
                        describe_claims(want),
                        inputs.describe()
                    ),
                )),
                Expect::Exactly(_) => {
                    ctx.note(format!("{context}: ok"));
                    Ok(Some(run))
                }
                Expect::Refused(kinds) => Err(Finding::low(
                    format!("{context}: accepted, expected {kinds:?}"),
                    format!(
                        "nothing unbacked is published, but the documented contract refuses these inputs\npublished {}\ninputs: {}",
                        describe_claims(&run.claims),
                        inputs.describe()
                    ),
                )),
            }
        }
        Err(kind) => match expect {
            Expect::Exactly(_) => Err(Finding::high(
                format!("{context}: a valid node is refused ({kind})"),
                format!("{}\ninputs: {}", describe_outcome(&result), inputs.describe()),
            )),
            Expect::Refused(kinds) if kinds.iter().any(|k| kind.starts_with(k)) => {
                ctx.note(format!("{context}: {kind}"));
                Ok(None)
            }
            Expect::Refused(kinds) => Err(Finding::low(
                format!("{context}: refused as {kind}, expected {kinds:?}"),
                format!("{}\ninputs: {}", describe_outcome(&result), inputs.describe()),
            )),
        },
    }
}

/// A child no verifier should accept: `verify` must reject it and the guest must refuse a node over it.
pub fn reject_child(
    ctx: &crate::Ctx,
    context: &str,
    mut inputs: Inputs,
    forged: EthereumProof,
    at: usize,
) -> Result<(), Finding> {
    if let Ok(()) = forged.verify() {
        return Err(Finding::critical(
            format!("{context}: the Rust verifier accepts a forged aggregate"),
            format!("claims {}", describe_claims(forged.claims())),
        ));
    }
    let at = at.min(inputs.children.len());
    inputs.children.insert(at, forged);
    inputs.names.insert(at, "forged".into());
    let result = crate::catch(|| inputs.execute()).map_err(|(message, location)| {
        let mut finding = Finding::panic(&message, &location).in_context("aggregate panics on an invalid child");
        finding.detail = format!("{context}\n{}\ninputs: {}", finding.detail, inputs.describe());
        finding
    })?;
    note_kill(ctx, &result);
    match outcome(&result) {
        Ok(()) => {
            if let Ok(f) = super::fixtures::fixtures(ctx)
                && let Some(j) = reads_a_valid_twin(f, &inputs, at)
            {
                return Err(benign_twin(context, f.children[j].name));
            }
            Err(Finding::critical(
                format!("{context}: the guest accepts a child the Rust verifier rejects"),
                format!(
                    "published {}\ninputs: {}",
                    describe_claims(&result.expect("ran").claims),
                    inputs.describe()
                ),
            ))
        }
        Err(kind) => {
            ctx.note(format!("{context}: {kind}"));
            Ok(())
        }
    }
}

/// The fixture whose valid proof of the forged child's statement hands the guest exactly the witness `inputs` did,
/// with the forged child at `k`. The host dropped every difference (a cap-level Merkle sibling another query's path
/// recomputes, `gen_verify` in rec_aggregation's child.rs), so the guest verified that valid proof. Fixtures share
/// statements: `x3r2` proves `x3`'s claims, and every leaf carries the same deferred claim.
pub fn reads_a_valid_twin(f: &Fixtures, inputs: &Inputs, k: usize) -> Option<usize> {
    let forged = inputs.children.get(k)?;
    let twins: Vec<usize> = (0..f.children.len())
        .filter(|&j| f.claims(j) == forged.claims() && f.proof(j).deferred() == forged.deferred())
        .collect();
    if twins.is_empty() {
        return None;
    }
    let seen = witness_of(inputs)?;
    twins.into_iter().find(|&j| {
        let mut twin = inputs.clone();
        twin.children[k] = f.proof(j).clone();
        witness_of(&twin).as_ref() == Some(&seen)
    })
}

/// The Low a forged child gets when [`reads_a_valid_twin`] finds the valid proof the guest really verified.
pub fn benign_twin(context: &str, twin: &str) -> Finding {
    Finding::low(
        format!("{context}: a child the verifier rejects reads into the honest child's witness"),
        format!(
            "benign for the guest: the forged proof differs from `{twin}`'s, which proves the same statement, only in data the host drops (a cap-level Merkle sibling another query's path recomputes), so the guest verified `{twin}`'s proof; the native verifier checks every path whole and rejects it"
        ),
    )
}

/// Prove a valid node in full: it verifies, publishes `want`, round-trips the wire, and verifies for no other claims.
pub fn prove_and_check(
    ctx: &crate::Ctx,
    src: &mut Source,
    context: &str,
    inputs: &Inputs,
    want: &EthereumClaims,
) -> Result<(), Finding> {
    let rate = src.range(leanvm_core::pcs::MIN_LOG_INV_RATE, leanvm_core::pcs::MAX_LOG_INV_RATE);
    let proof = rec_aggregation::aggregate(
        &inputs.children,
        inputs.xmss.clone(),
        inputs.sphincs.clone(),
        &inputs.blobs,
        inputs.declare.as_ref(),
        rate,
    )
    .map_err(|e| {
        Finding::high(
            format!("{context}: a valid node is not proven"),
            format!("{e:?}\nrate {rate}\ninputs: {}", inputs.describe()),
        )
    })?;
    let detail = || format!("rate {rate}\ninputs: {}", inputs.describe());
    if let Err(e) = proof.verify() {
        return Err(Finding::high(
            format!("{context}: an honest aggregate does not verify"),
            format!("{e:?}\n{}", detail()),
        ));
    }
    if proof.claims() != want {
        return Err(Finding::high(
            format!("{context}: the proven aggregate claims other than its run"),
            format!(
                "proven {}\nexpected {}\n{}",
                describe_claims(proof.claims()),
                describe_claims(want),
                detail()
            ),
        ));
    }
    let bytes = proof.proof_bytes();
    match EthereumProof::from_proof_bytes(&bytes, want.clone()).map(|p| p.verify()) {
        Ok(Ok(())) => {}
        other => {
            return Err(Finding::high(
                format!("{context}: an honest aggregate does not round-trip the wire"),
                format!("{other:?}\n{}", detail()),
            ));
        }
    }
    ctx.note(format!("{context}: proven"));
    let mut other = want.clone();
    let what = match src.below(5) {
        0 if !other.xmss.is_empty() => {
            other.xmss.pop();
            "one leanXMSS claim fewer"
        }
        1 if !other.lean_sphincs.is_empty() => {
            other.lean_sphincs.remove(0);
            "one leanSPHINCS claim fewer"
        }
        2 => {
            other.da_commitment = match other.da_commitment {
                Some(_) => None,
                None => Some([0x5A; 32]),
            };
            "another DA root"
        }
        3 if !other.xmss.is_empty() => {
            let (pk, m) = other.xmss.remove(0);
            other.lean_sphincs.push((
                signatures::lean_sphincs::LeanSphincsPublicKey::from_bytes(&pk.to_bytes()),
                m,
            ));
            other.lean_sphincs.sort();
            "a leanXMSS claim as leanSPHINCS"
        }
        _ => {
            let mut pk = [0u8; 32];
            src.rng().fill(&mut pk);
            other
                .xmss
                .push((signatures::lean_xmss::LeanXmssPublicKey::from_bytes(&pk), [3; 32]));
            other.xmss.sort();
            "one leanXMSS claim more"
        }
    };
    if let Ok(p) = EthereumProof::from_proof_bytes(&bytes, other.clone())
        && p.verify().is_ok()
    {
        return Err(Finding::critical(
            format!("{context}: an aggregate verifies for claims it was not proven for ({what})"),
            format!(
                "proven {}\naccepted {}\n{}",
                describe_claims(want),
                describe_claims(&other),
                detail()
            ),
        ));
    }
    Ok(())
}

/// The witness the host builds for `inputs`, every hint stream, without running the guest; `None` when no node is
/// built.
pub fn witness_of(inputs: &Inputs) -> Option<Streams> {
    let seen: std::rc::Rc<std::cell::RefCell<Option<Streams>>> = Default::default();
    let sink = seen.clone();
    rec_aggregation::fuzzing::arm_forgery(Box::new(move |hints| {
        *sink.borrow_mut() = Some(hints.streams_mut().clone())
    }));
    let built = crate::catch(|| {
        rec_aggregation::fuzzing::prepare_node(
            &inputs.children,
            inputs.xmss.clone(),
            inputs.sphincs.clone(),
            &inputs.blobs,
            inputs.declare.as_ref(),
        )
        .is_ok()
    });
    rec_aggregation::fuzzing::disarm_forgery();
    if built != Ok(true) {
        return None;
    }
    seen.take()
}
