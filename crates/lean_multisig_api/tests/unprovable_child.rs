//! A supplied aggregate whose envelope decodes but whose proof is worthless must be rejected.
//!
//! `codec::classify` only decodes the envelope — postcard, then `rebuild_bytecode_claim`, then
//! the pubkey well-formedness check. Nothing in it looks at the proof. Every plan shape that
//! *consumes* a child gets the proof checked for free, because
//! `aggregate_single_message_signatures` verifies each child before folding it in — but a lone
//! supplied aggregate is planned as a `Passthrough`, which is consumed by nothing. That one path
//! has to check the proof itself, and these tests are what say so.
//!
//! The blob below is the cheapest thing that gets past the envelope: a real bytecode-claim point
//! of the right length, one well-formed public key, and an empty proof. Building it by hand
//! avoids the minutes of proving a genuine aggregate would cost, and an empty transcript fails
//! verification for the most unambiguous reason available (`ExceededTranscript`).

use lean_vm::{EF, F};
use ssz::Decode;
use xmss::XmssPublicKey;

const MSG: [u8; 32] = [0u8; 32];
const SLOT: u32 = 0;

/// The postcard encoding of a `SingleMessageAggregateSignature`, field by field.
///
/// The type cannot be constructed directly from outside `rec_aggregation` — `Proof`'s fields are
/// `pub(crate)` — so this writes the wire format instead. Postcard encodes structs and tuples as
/// their fields back to back with no framing, so a tuple of the right leaves in the right order
/// is byte-identical to the real thing:
///
/// `SingleMessageAggregateSignature { info: { core: (message, slot, point), pubkeys }, proof }`,
/// where `ExecutionProof`'s only serialized field is `Proof { transcript, merkle_paths }`.
fn unprovable_aggregate() -> Vec<u8> {
    // The point must match the bytecode's variable count or `rebuild_bytecode_claim` rejects it
    // and the blob never gets past parsing — which would make these tests pass for the wrong
    // reason. Its *value* is recomputed on deserialize, so zeros are fine.
    let n_vars = rec_aggregation::get_aggregation_bytecode().cumulated_n_vars();
    let point: Vec<EF> = vec![EF::default(); n_vars];

    // One public key, non-empty and trivially sorted, as `check_single_message_pubkeys` demands.
    let mut pk_bytes = vec![0u8; xmss::PUB_KEY_SSZ_LEN];
    pk_bytes[0] = 1;
    let pubkeys: Vec<XmssPublicKey> = vec![XmssPublicKey::from_ssz_bytes(&pk_bytes).unwrap()];

    postcard::to_allocvec(&((MSG, SLOT, point), pubkeys, (Vec::<F>::new(), Vec::<u8>::new())))
        .expect("the fixture serializes infallibly")
}

#[test]
fn aggregate_rejects_an_unprovable_lone_aggregate() {
    lean_multisig_api::warm_up();
    let blob = unprovable_aggregate();

    // No raw signatures and one child, so the planner returns `Passthrough(0)` — the shape where
    // no node ever consumes the child. Without the check in that arm this returns `Ok`, and the
    // caller goes on to re-gossip a blob that fails everywhere downstream.
    let result = lean_multisig_api::aggregate(vec![blob], vec![], MSG, SLOT);
    assert!(
        matches!(result, Err(lean_multisig_api::Error::Proof(_))),
        "a passthrough must verify its child's proof, got {result:?}"
    );
}

#[test]
fn verify_rejects_an_unprovable_aggregate() {
    lean_multisig_api::warm_up();
    let blob = unprovable_aggregate();

    // Distinct from the malformed-bytes tests in the unit suite: those stop at parsing, so they
    // never reach `verify_single_message_aggregate`. This one is well-formed all the way to the
    // proof, so `Error::Proof` rather than `Error::MalformedAggregate` is the whole assertion.
    let result = lean_multisig_api::verify(&blob, &MSG, SLOT);
    assert!(
        matches!(result, Err(lean_multisig_api::Error::Proof(_))),
        "expected the proof check to reject this, got {result:?}"
    );
}

#[test]
fn the_fixture_really_does_get_past_the_envelope() {
    // If the wire format ever drifts, the two tests above would still pass — on
    // `MalformedAggregate`, having proved nothing about proof checking. This is what tells the
    // difference: a wrong (message, slot) has to be reported as a mismatch, which is only
    // reachable once the blob has parsed.
    lean_multisig_api::warm_up();
    let blob = unprovable_aggregate();
    let result = lean_multisig_api::verify(&blob, &[9u8; 32], SLOT);
    assert!(
        matches!(result, Err(lean_multisig_api::Error::MessageMismatch)),
        "the fixture must parse, or the tests above prove nothing, got {result:?}"
    );
}
