//! An opinionated facade over `xmss` and `rec_aggregation`.
//!
//! Every tuning parameter is chosen internally. Callers needing control over `log_inv_rate`
//! or recursion topology should use `rec_aggregation` directly.
//!
//! # Trusted claims cannot enter through this facade
//!
//! `SingleMessageCore::bytecode_claim` carries a `value` that verification *trusts*, and
//! `rec_aggregation` warns that a claim taken from an untrusted source must be recomputed
//! before use. Every aggregate crossing this boundary is a byte slice, and deserializing one
//! always runs `rebuild_bytecode_claim`, which recomputes that value from the point alone.
//! There is no way to hand this crate a pre-built aggregate struct, so the unsound path is
//! unreachable here by construction rather than by discipline.
#![cfg_attr(not(test), warn(unused_crate_dependencies))]

mod codec;
mod error;
mod key;
mod plan;

use rec_aggregation::{
    MAX_XMSS_AGGREGATED, SingleMessageAggregateSignature, aggregate_single_message_signatures,
    init_aggregation_bytecode, verify_single_message_aggregate,
};
use ssz::Encode;
use std::borrow::Cow;
use std::collections::BTreeSet;
use xmss::{XmssPublicKey, XmssSignature};

pub use error::Error;
pub use key::SecretKey;

/// A raw signature paired with the public key that produced it.
type Raw = (XmssPublicKey, XmssSignature);

/// Pays the one-time aggregation-bytecode compile up front.
///
/// Entirely optional: [`aggregate`], [`verify`] and [`verify_with_signers`] all do this
/// themselves, and it is idempotent, so this only moves *when* the cost lands. A long-running
/// service calls it at startup rather than paying it inside its first real request.
///
/// # Panics
///
/// If the bytecode fails to compile. The program source is embedded in the binary, so that is
/// a bug in this workspace rather than anything a caller can provoke.
pub fn warm_up() {
    init_aggregation_bytecode();
}

/// Aggregates raw XMSS signatures and previously produced aggregates into a single proof, all
/// sharing one `(message, slot)`.
///
/// `public_keys` covers **raw signatures only** — aggregates carry their own signer sets — so
/// the k-th raw entry of `proof_or_sig` pairs with `public_keys[k]`. The two vectors are
/// therefore *not* index-aligned whenever an aggregate is present. Entries are told apart by
/// length: exactly `xmss::SIGNATURE_SSZ_LEN` bytes is a raw signature, anything else is parsed
/// as an aggregate.
///
/// The recursion tree, its fan-in, and every `log_inv_rate` are chosen internally. The result
/// is the wire proof, ready for [`verify`] or for feeding back into another `aggregate` call.
///
/// Repeated signers are dropped: the signer set of the result is the sorted, deduplicated union
/// of the raw pubkeys and every supplied aggregate's pubkeys. Supplying one signer twice is
/// therefore harmless, but wasteful — the same key in two *different* supplied aggregates still
/// costs a duplicate slot at the node that merges them.
///
/// # Cost
///
/// Proving is sequential within one call: wall-clock is the **sum** of every node's proving
/// time, with no parallelism across nodes. Seconds per node, at the leaf boundary as much as at
/// small signer counts — measured un-warmed at 19 small nodes in ~8s release and one full
/// 1500-signature leaf in about the same, so an embedder that has called
/// `lean_multisig::setup_prover_without_arena` may see different numbers. No progress reporting,
/// no way to resume.
///
/// Concurrency across calls is a property of the *process*, not of this crate. Two `aggregate`
/// calls on different threads are safe only while nothing has engaged `zk_alloc`'s arena. An
/// application calling `lean_multisig::setup_prover` engages it, after which `rec_aggregation`
/// asserts that proving phases neither nest nor overlap and the losing call **panics**. The same
/// code in a `lean_multisig_api`-only harness runs fine because the arena is never engaged there — that
/// is an artefact of the harness, not a guarantee. Serialize `aggregate` calls unconditionally.
///
/// # Errors
///
/// - [`Error::Empty`] if `proof_or_sig` is empty.
/// - [`Error::PubkeyCountMismatch`] if `public_keys.len()` is not the number of raw entries.
/// - [`Error::MalformedSignature`], [`Error::MalformedEntry`], [`Error::MalformedPublicKey`]
///   for a blob that does not decode; the index names the vector its variant documents.
/// - [`Error::MessageMismatch`] if a supplied aggregate proves a different `(message, slot)`.
/// - [`Error::TooManySigners`] if the deduplicated union exceeds `MAX_XMSS_AGGREGATED` (32768).
///   Recursion does not raise that ceiling — it is re-checked at every node including the root,
///   so the tree exists to get past the ~1500 signatures one node can prove, not past 32768.
/// - [`Error::Proof`] if a supplied aggregate's proof does not verify. Every child is checked,
///   including the lone-aggregate case that is passed straight through: a successful return
///   always means the bytes handed back are a valid aggregate.
/// - [`Error::Aggregation`] or [`Error::Proof`] if a proving job fails. A raw signature that does
///   not verify under the public key it was paired with — the shape a misordered `public_keys`
///   produces, since the counts still match and both blobs still decode — surfaces here as a bare
///   constraint-system mismatch carrying no index. Check the ordering first.
///
/// Everything except the last two is decided before any proving starts, so a malformed or
/// over-capacity request fails in milliseconds rather than after the whole tree has been proved.
///
/// The two faults a *supplied aggregate* can raise — [`Error::MessageMismatch`] and
/// [`Error::Proof`] — carry no index, so a caller passing several aggregates learns that one of
/// them is bad but not which, and has to bisect. Naming one cheaply would mean indexing the
/// filtered aggregate list rather than `proof_or_sig`, which is a third index space
/// contradicting the rule above; pointing at `proof_or_sig` needs `classify` to carry original
/// positions.
///
/// # Panics
///
/// If another proving job is already running in this process *and* something has engaged
/// `zk_alloc`'s arena — see the concurrency paragraph under [Cost](#cost) for why that condition
/// is not automatic, and why it is no reason to leave calls unserialized. Also if the aggregation
/// bytecode fails to compile — see [`warm_up`].
pub fn aggregate(
    proof_or_sig: Vec<Vec<u8>>,
    public_keys: Vec<Vec<u8>>,
    message: [u8; 32],
    slot: u32,
) -> Result<Vec<u8>, Error> {
    // Before `classify`, which parses aggregates: `from_bytes` silently returns `None` with the
    // bytecode uninitialized, so a valid aggregate would come back as `MalformedEntry`.
    init_aggregation_bytecode();
    let (mut raw, children) = codec::classify(proof_or_sig, public_keys)?;

    // A supplied aggregate over some other (message, slot) is caught here rather than by
    // `aggregate_single_message_signatures`, which only sees it at a node that consumes it.
    // For a lone aggregate the plan is a `Passthrough` and no node ever consumes it, so
    // without this check that call would return an aggregate over the wrong message as a
    // *success*. Other shapes reach upstream's own check eventually — immediately if every
    // sibling is a passthrough, but only after proving them if any sibling is a node this call
    // has to prove first. Checking the flat vector here covers every child wherever the
    // planner later puts it.
    if children
        .iter()
        .any(|c| c.info.core.message != message || c.info.core.slot != slot)
    {
        return Err(Error::MessageMismatch);
    }

    dedup_signers(&mut raw);

    // Reject over-capacity before proving anything: failing after the whole tree is cruel.
    // Held by reference — cloning 32768 public keys to count them would be its own small waste.
    let mut signers: BTreeSet<&XmssPublicKey> = raw.iter().map(|(pk, _)| pk).collect();
    signers.extend(children.iter().flat_map(|c| c.info.pubkeys.iter()));
    let got = signers.len();
    if got > MAX_XMSS_AGGREGATED {
        return Err(Error::TooManySigners {
            got,
            max: MAX_XMSS_AGGREGATED,
        });
    }

    // The plan is built here, from these exact lengths, and never accepted from outside: its
    // ranges and passthrough indices are bare `usize`s into the two slices below, with nothing
    // at type level tying them together.
    let tree = plan::plan(raw.len(), children.len());

    // A lone supplied aggregate is planned as a `Passthrough` and consumed by nothing, so this
    // is the one shape where no node verifies the child's proof — `classify` only decodes the
    // envelope. Every other shape gets it free from `aggregate_single_message_signatures`,
    // which verifies each child before folding it in. Without this, `aggregate` returns `Ok`
    // for a peer's structurally intact but unprovable aggregate and the caller re-gossips it.
    //
    // At the root rather than in `execute`'s `Passthrough` arm: the planner puts *every*
    // supplied child into the pool as a passthrough, so that arm would fire for all of them and
    // each would then be verified a second time by the node that consumes it — 32 verifications
    // for 16 supplied aggregates. Only the lone case is unconsumed, and the tree says which
    // case this is before any of it runs.
    if let plan::Plan::Passthrough(i) = tree {
        verify_single_message_aggregate(&children[i])?;
    }
    Ok(execute(&tree, &raw, &children, message, slot)?.to_bytes())
}

/// Drops repeat signers, keeping the earliest signature offered for each public key.
///
/// Every node deduplicates its own share anyway, so the *signer set* of the result is the same
/// either way. What this adds is that duplicates landing in two different leaves — which survive
/// the per-node dedup and reappear as `dup_pub_keys` at the node merging them — cost neither a
/// wasted leaf slot nor a second ceiling (`MAX_XMSS_DUPLICATES`) to blow through at the very top
/// of the tree, with everything below it already proved.
///
/// It is not *entirely* result-preserving: where one key is offered twice with different
/// signature bytes and the two would have landed in different leaves, upstream would have proved
/// both and this proves only the first. That is a laxening rather than a soundness hole — the
/// surviving signature is still proved, and the signer set is unchanged.
///
/// The sort is stable and the dedup drops the later of each equal pair, so "earliest" means
/// earliest in the caller's `proof_or_sig` order. This is exactly what upstream does per node.
fn dedup_signers(raw: &mut Vec<Raw>) {
    raw.sort_by(|(a, _), (b, _)| a.cmp(b));
    raw.dedup_by(|(a, _), (b, _)| a == b);
}

/// Proves one node of the plan, depth first, recursing into its children first.
///
/// Returns `Cow` so that a plan which is nothing but a `Passthrough` — a lone supplied
/// aggregate, re-encoded — does not clone a whole `ExecutionProof` on the way out. A
/// passthrough *under* a node still has to be cloned, because
/// `aggregate_single_message_signatures` wants a contiguous slice of owned children.
///
/// Recursion depth is not a stack concern. `dedup_signers` and the ceiling check together cap
/// `raw.len()` at 32768 before planning, so raw contributes at most 22 leaves; the pool is
/// otherwise supplied children, and the planner folds at a fan-in of 16, so reaching depth `d`
/// needs 16^(d-1) of them. Each is a decoded `ExecutionProof`, so a pathological input runs out
/// of addressable memory several levels before it runs out of stack.
///
/// Indexing `raw` and `children` cannot panic: `plan` was called with exactly these two
/// lengths, and it covers every index of both exactly once (pinned by its own tests).
fn execute<'a>(
    node: &plan::Plan,
    raw: &[Raw],
    children: &'a [SingleMessageAggregateSignature],
    message: [u8; 32],
    slot: u32,
) -> Result<Cow<'a, SingleMessageAggregateSignature>, Error> {
    match node {
        // Proof checking is not done here. A passthrough under a node is verified by that node,
        // and the one passthrough with no node above it — a lone supplied aggregate — is
        // verified by `aggregate` before this is ever called.
        plan::Plan::Passthrough(i) => Ok(Cow::Borrowed(&children[*i])),
        plan::Plan::Node {
            raw: range,
            children: kids,
            log_inv_rate,
        } => {
            let proved: Vec<SingleMessageAggregateSignature> = kids
                .iter()
                .map(|kid| execute(kid, raw, children, message, slot).map(Cow::into_owned))
                .collect::<Result<_, _>>()?;
            Ok(Cow::Owned(aggregate_single_message_signatures(
                &proved,
                raw[range.clone()].to_vec(),
                message,
                slot,
                *log_inv_rate,
            )?))
        }
    }
}

/// Verifies an aggregate and returns the signer set it actually proves, as SSZ-encoded public
/// keys.
///
/// The signer set is the success value rather than an input on purpose: an aggregate over the
/// wrong validator set is still a perfectly valid proof, so a `bool` return would invite
/// `if verify(..)` while the caller forgets to check *who* signed. Returning the set instead
/// means a caller who ignores who signed has to discard a value to do it, rather than simply
/// not asking. It is not a guarantee — `verify(..)?;` still compiles, because after `?` the
/// type is a plain `Vec<Vec<u8>>` and nothing on it is `#[must_use]` — which is why
/// [`verify_with_signers`] exists for the common case where the expected set is already known.
///
/// Keys come back in the library's canonical sorted order, not the order they were aggregated
/// in, and without duplicates. Compare as a set.
///
/// # Errors
///
/// - [`Error::MalformedAggregate`] if the bytes are not a well-formed aggregate, including
///   trailing bytes after a complete one.
/// - [`Error::MessageMismatch`] if the aggregate proves a different `(message, slot)`. This is
///   not implied by the proof check below, which validates the aggregate against its *own*
///   message and slot; it is what binds the proof to the pair you asked about.
/// - [`Error::Proof`] if the proof does not verify.
///
/// # Panics
///
/// If the aggregation bytecode fails to compile — see [`warm_up`], which is the only way this
/// can happen. Verification runs no proving job of its own, so unlike [`aggregate`] it never
/// takes the process-wide arena phase.
#[must_use = "an aggregate proves nothing until you check who signed it"]
pub fn verify(aggregate: &[u8], message: &[u8; 32], slot: u32) -> Result<Vec<Vec<u8>>, Error> {
    // Before parsing: `from_bytes` returns `None` rather than panicking with the bytecode
    // uninitialized, which would report a perfectly good aggregate as malformed.
    init_aggregation_bytecode();
    let sig = SingleMessageAggregateSignature::from_bytes(aggregate).ok_or(Error::MalformedAggregate)?;
    if &sig.info.core.message != message || sig.info.core.slot != slot {
        return Err(Error::MessageMismatch);
    }
    verify_single_message_aggregate(&sig)?;
    Ok(sig.info.pubkeys.iter().map(Encode::as_ssz_bytes).collect())
}

/// [`verify`], checking the proved signer set against one already known.
///
/// Both sides are compared as sets, so the order of `expected` is irrelevant and repeats in it
/// are ignored — `[a, a]` matches a proof of `{a}`.
///
/// # Errors
///
/// As [`verify`], plus [`Error::SignerSetMismatch`] if the proved set is not exactly
/// `expected`. A signer missing from `expected` fails just as loudly as an unexpected one.
///
/// Entries of `expected` are compared as opaque bytes and never decoded, so one that is not a
/// `xmss::PUB_KEY_SSZ_LEN` SSZ public key is not reported as malformed input — it simply
/// matches nothing, and surfaces as [`Error::SignerSetMismatch`] like any other wrong set.
pub fn verify_with_signers(aggregate: &[u8], expected: &[Vec<u8>], message: &[u8; 32], slot: u32) -> Result<(), Error> {
    // Inherits the bytecode initialization from `verify`, which is the first thing this calls
    // and which initializes before it parses anything.
    let proved = verify(aggregate, message, slot)?;
    let proved: BTreeSet<&[u8]> = proved.iter().map(Vec::as_slice).collect();
    let expected: BTreeSet<&[u8]> = expected.iter().map(Vec::as_slice).collect();
    if proved == expected {
        Ok(())
    } else {
        Err(Error::SignerSetMismatch)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ssz::Decode;

    const MSG: [u8; 32] = [42u8; 32];
    const SLOT: u32 = 100;

    /// A distinct, well-formed, entirely fictitious public key.
    ///
    /// `classify` checks SSZ length and field-element canonicality, never that a key belongs to
    /// anybody, and the ceiling counts distinct keys — so a real keygen (milliseconds each, and
    /// 32769 of them here) buys nothing these tests need. A small index in the leading field
    /// element is canonical for every index these tests use.
    fn synthetic_pubkey_bytes(index: u32) -> Vec<u8> {
        let mut bytes = vec![0u8; xmss::PUB_KEY_SSZ_LEN];
        bytes[..4].copy_from_slice(&index.to_le_bytes());
        bytes
    }

    fn synthetic_pubkey(index: u32) -> XmssPublicKey {
        XmssPublicKey::from_ssz_bytes(&synthetic_pubkey_bytes(index)).unwrap()
    }

    /// A decodable signature that is not a valid one. Only its identity matters here.
    fn synthetic_signature(tag: u8) -> XmssSignature {
        let mut bytes = vec![0u8; xmss::SIGNATURE_SSZ_LEN];
        bytes[0] = tag;
        XmssSignature::from_ssz_bytes(&bytes).unwrap()
    }

    #[test]
    fn aggregate_rejects_empty_input() {
        // Returns before the planner, so no prover is involved.
        assert!(matches!(aggregate(vec![], vec![], MSG, SLOT), Err(Error::Empty)));
    }

    #[test]
    fn aggregate_rejects_a_pubkey_count_mismatch() {
        // A zero-filled blob of signature length classifies as raw on length alone, and the
        // count check fires before anything is decoded — so this needs no real signature.
        let entry = vec![0u8; xmss::SIGNATURE_SSZ_LEN];
        assert!(matches!(
            aggregate(vec![entry], vec![], MSG, SLOT),
            Err(Error::PubkeyCountMismatch { expected: 1, got: 0 })
        ));
    }

    #[test]
    fn aggregate_rejects_more_signers_than_the_ceiling() {
        // Trap #2: the ceiling recursion does *not* raise. `aggregate_single_message_signatures`
        // re-checks it at every node including the root, so a tree buys capacity past the ~1500
        // signatures one node can prove, and nothing past 32768 signers. This is the check that
        // turns "fails after the whole tree is proved" into "fails in milliseconds", so it needs
        // pinned by something. Costs about 3s on top of the shared bytecode compile.
        //
        // Only the rejecting side of the boundary is testable: exactly 32768 signers gets *past*
        // this check and straight into proving 22 leaves, so no test at any tier can assert the
        // accepting side cheaply.
        let n = MAX_XMSS_AGGREGATED + 1;
        let entries = vec![vec![0u8; xmss::SIGNATURE_SSZ_LEN]; n];
        let pubkeys: Vec<Vec<u8>> = (0..u32::try_from(n).unwrap()).map(synthetic_pubkey_bytes).collect();
        assert!(matches!(
            aggregate(entries, pubkeys, MSG, SLOT),
            Err(Error::TooManySigners { got, max }) if got == n && max == MAX_XMSS_AGGREGATED
        ));
    }

    #[test]
    fn dedup_keeps_the_earliest_signature_offered_for_a_key() {
        // The property `dedup_signers` documents, and previously only claimed in a comment: a
        // stable sort plus `dedup_by` (which drops the *later* of each equal pair) means the
        // survivor is the earliest in the caller's order, matching what upstream does per node.
        // Reachable only through `aggregate`, and so only at proving cost, until it was extracted.
        let repeated = synthetic_pubkey(1);
        let other = synthetic_pubkey(2);
        let (first, second) = (synthetic_signature(1), synthetic_signature(2));
        assert_ne!(first, second, "the two signatures must be distinguishable");

        let mut raw = vec![
            (other.clone(), second.clone()),
            (repeated.clone(), first.clone()),
            (repeated.clone(), second.clone()),
        ];
        dedup_signers(&mut raw);

        assert_eq!(raw.len(), 2, "the repeated key must collapse to one entry");
        let kept = raw
            .iter()
            .find(|(pk, _)| *pk == repeated)
            .expect("the key must survive");
        assert_eq!(kept.1, first, "the earliest signature offered must be the survivor");
        // The other key is untouched, so dedup is not merely truncating.
        let kept_other = raw.iter().find(|(pk, _)| *pk == other).expect("the key must survive");
        assert_eq!(kept_other.1, second);
    }

    #[test]
    fn dedup_leaves_distinct_signers_alone() {
        let mut raw: Vec<Raw> = (0..8).map(|i| (synthetic_pubkey(i), synthetic_signature(1))).collect();
        dedup_signers(&mut raw);
        assert_eq!(raw.len(), 8);
    }

    #[test]
    fn verify_rejects_garbage() {
        // Not signature-length, not a postcard aggregate: rejected before any proof work.
        assert!(matches!(
            verify(&[0xffu8; 64], &MSG, SLOT),
            Err(Error::MalformedAggregate)
        ));
    }

    #[test]
    fn verify_rejects_empty_bytes() {
        assert!(matches!(verify(&[], &MSG, SLOT), Err(Error::MalformedAggregate)));
    }

    #[test]
    fn warm_up_is_idempotent() {
        // The bytecode lives in a `OnceLock`; a second init must be a no-op, not a panic.
        warm_up();
        warm_up();
    }

    #[test]
    fn every_entry_point_survives_without_an_explicit_warm_up() {
        // This pins only that none of the three entry points panics on a caller that never
        // called `warm_up`. It cannot pin that they *initialize* the bytecode: unit tests share
        // a process, so by the time this runs another test has very likely filled the
        // `OnceLock` already. That half is pinned by `tests/lazy_init_*.rs`, one file per entry
        // point so that each gets a process where it is the first thing to run.
        assert!(aggregate(vec![], vec![], MSG, SLOT).is_err());
        assert!(verify(&[0xffu8; 64], &MSG, SLOT).is_err());
        assert!(verify_with_signers(&[0xffu8; 64], &[], &MSG, SLOT).is_err());
    }
}
