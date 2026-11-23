//! leanXMSS and leanSPHINCS aggregation through the safe facade.
#![cfg(feature = "aggregation")]

use std::sync::LazyLock;

use lean_pq::{
    aggregate, aggregate_only, setup, sphincs, xmss, Aggregate, Error, Message, MAX_CHILDREN,
};

/// Two signers, shared by every test so each key is generated once.
struct Signers {
    xmss: xmss::SecretKey,
    sphincs: sphincs::SecretKey,
}

static SIGNERS: LazyLock<Signers> = LazyLock::new(|| Signers {
    xmss: xmss::SecretKey::from_seed([5; 32]),
    sphincs: sphincs::SecretKey::from_seed([6; 32]),
});

/// One proven aggregate over a single leanXMSS claim, shared to prove only once.
static LEAF: LazyLock<Aggregate> =
    LazyLock::new(|| aggregate(&[], &[xmss_input(FIRST, 0)], &[]).unwrap());

const FIRST: Message = [0x11; 32];
const SECOND: Message = [0x22; 32];

/// Claim lists as `Aggregate::from_bytes` takes them.
type XmssClaims<'a> = &'a [(xmss::PublicKey, Message)];
type SphincsClaims<'a> = &'a [(sphincs::PublicKey, Message)];

fn xmss_input(message: Message, leaf_index: u32) -> (xmss::PublicKey, Message, xmss::Signature) {
    // A fresh leanXMSS signature of the message at the leaf index.
    let key = &SIGNERS.xmss;
    (key.public_key(), message, key.sign(&message, leaf_index))
}

fn sphincs_input(message: Message) -> (sphincs::PublicKey, Message, sphincs::Signature) {
    // A fresh leanSPHINCS signature of the message.
    let key = &SIGNERS.sphincs;
    (key.public_key(), message, key.sign(&message))
}

#[test]
fn aggregates_both_schemes_recursively_and_round_trips() {
    let xmss_key = SIGNERS.xmss.public_key();
    let sphincs_key = SIGNERS.sphincs.public_key();

    // Fixture state: a two-level tree of proofs.
    //
    //     LEAF  = { xmss: (key, FIRST) }
    //     right = { sphincs: (key, SECOND) }
    //     root  = LEAF + right + { xmss: (key, SECOND), (key, FIRST) again }
    let right = aggregate(&[], &[], &[sphincs_input(SECOND)]).unwrap();
    let root = aggregate(
        &[&LEAF, &right],
        &[xmss_input(SECOND, 1), xmss_input(FIRST, 2)],
        &[],
    )
    .unwrap();

    // The bytes are the proof alone: the receiver supplies the claims, here in another order
    // and with a duplicate, and decoding verifies the proof against them.
    let bytes = root.to_bytes();
    let received = Aggregate::from_bytes(
        &bytes,
        &[(xmss_key, SECOND), (xmss_key, FIRST), (xmss_key, SECOND)],
        &[(sphincs_key, SECOND)],
    )
    .unwrap();

    // Claims are the union, sorted, with (key, FIRST) once though proven twice.
    assert_eq!(root.xmss_claims(), [(xmss_key, FIRST), (xmss_key, SECOND)]);
    assert_eq!(received.xmss_claims(), root.xmss_claims());
    assert_eq!(received.sphincs_claims(), [(sphincs_key, SECOND)]);
    assert_eq!(received.to_bytes(), bytes);
    assert_eq!(
        format!("{received:?}"),
        "Aggregate { xmss_claims: 2, sphincs_claims: 1, .. }"
    );
}

#[test]
fn proves_only_the_claims_asked_for() {
    let xmss_key = SIGNERS.xmss.public_key();
    let sphincs_key = SIGNERS.sphincs.public_key();
    // LEAF proves (key, FIRST); the raw signatures add (key, SECOND) under each scheme. Keep two of the three.
    let only = aggregate_only(
        &[&LEAF],
        &[xmss_input(SECOND, 5)],
        &[sphincs_input(SECOND)],
        &[(xmss_key, SECOND), (xmss_key, FIRST), (xmss_key, SECOND)],
        &[],
    )
    .unwrap();
    assert_eq!(only.xmss_claims(), [(xmss_key, FIRST), (xmss_key, SECOND)]);
    assert_eq!(only.sphincs_claims(), Vec::new());
    let bytes = only.to_bytes();
    Aggregate::from_bytes(&bytes, &[(xmss_key, FIRST), (xmss_key, SECOND)], &[]).unwrap();
    assert_eq!(
        Aggregate::from_bytes(
            &bytes,
            &[(xmss_key, FIRST), (xmss_key, SECOND)],
            &[(sphincs_key, SECOND)]
        )
        .unwrap_err(),
        Error::AggregateRejected
    );

    // A claim the inputs do not cover.
    let uncovered = aggregate_only(&[&LEAF], &[], &[], &[(xmss_key, SECOND)], &[]).unwrap_err();
    assert!(
        uncovered.to_string().contains("not covered by the inputs"),
        "{uncovered}"
    );
}

#[test]
fn rejects_claims_the_proof_does_not_prove() {
    let xmss_key = SIGNERS.xmss.public_key();
    // The same 32 bytes, read as a leanSPHINCS key.
    let as_sphincs = sphincs::PublicKey::from_bytes(&xmss_key.to_bytes()).unwrap();
    let bytes = LEAF.to_bytes();
    Aggregate::from_bytes(&bytes, &[(xmss_key, FIRST)], &[]).unwrap();

    // Mutations of LEAF's claims { xmss: (key, FIRST) }: each is a different statement.
    //
    //     no claims                       one short
    //     (key, SECOND)                   another message
    //     (key, FIRST), (key, SECOND)     one extra
    //     sphincs: (key, FIRST)           the same claim under the other scheme
    let mutations: [(XmssClaims, SphincsClaims); 4] = [
        (&[], &[]),
        (&[(xmss_key, SECOND)], &[]),
        (&[(xmss_key, FIRST), (xmss_key, SECOND)], &[]),
        (&[], &[(as_sphincs, FIRST)]),
    ];
    for (xmss_claims, sphincs_claims) in mutations {
        assert_eq!(
            Aggregate::from_bytes(&bytes, xmss_claims, sphincs_claims).unwrap_err(),
            Error::AggregateRejected
        );
    }
}

#[test]
fn rejects_an_invalid_raw_signature_by_list_and_index() {
    // Mutation: sign FIRST, then claim the signature is over SECOND.
    //
    //     xmss[0]    valid
    //     xmss[1]    (key, SECOND, sig over FIRST at leaf 4)  -> rejected
    let (key, _, forged) = xmss_input(FIRST, 4);
    let error = aggregate(&[], &[xmss_input(FIRST, 3), (key, SECOND, forged)], &[]).unwrap_err();
    assert_eq!(
        error,
        Error::InvalidXmssInput {
            index: 1,
            leaf_index: 4,
        }
    );

    // Same mutation on the leanSPHINCS list, at index 0.
    let (key, _, forged) = sphincs_input(FIRST);
    let error = aggregate(&[], &[], &[(key, SECOND, forged)]).unwrap_err();
    assert_eq!(error, Error::InvalidSphincsInput { index: 0 });
}

#[test]
fn rejects_more_children_than_one_proof_recurses_over() {
    // Boundary: 16 children fit, 17 do not.
    //
    // The count is checked before any proving, so one shared leaf suffices.
    let children = [&*LEAF; MAX_CHILDREN + 1];
    let error = aggregate(&children, &[], &[]).unwrap_err();
    assert_eq!(error, Error::TooManyChildren { count: 17, max: 16 });
    assert_eq!(
        error.to_string(),
        "aggregation takes at most 16 children, got 17"
    );
}

#[test]
fn rejects_empty_input() {
    // Nothing to prove: no children, no raw signatures.
    let error = aggregate(&[], &[], &[]).unwrap_err();
    assert!(matches!(error, Error::Aggregation { .. }), "{error:?}");
    // Bindings match on this prefix; the reason after it is the prover's wording.
    assert!(error.to_string().starts_with("aggregation failed: "));
}

#[test]
fn rejects_tampered_and_truncated_bytes() {
    let claims = [(SIGNERS.xmss.public_key(), FIRST)];
    let bytes = LEAF.to_bytes();

    // Mutation 1: flip the last bit, inside the proof.
    let mut tampered = bytes.clone();
    *tampered.last_mut().unwrap() ^= 1;

    // Mutation 2: drop the last byte.
    let truncated = &bytes[..bytes.len() - 1];

    // Mutation 3: flip a bit of the deferred point, which the encoding carries first.
    let mut moved = bytes.clone();
    moved[8] ^= 1;

    // Each fails against the proof's own claims.
    for mutated in [&tampered[..], truncated, &moved[..]] {
        let error = Aggregate::from_bytes(mutated, &claims, &[]).unwrap_err();
        assert!(
            matches!(error, Error::MalformedAggregate | Error::AggregateRejected),
            "{error:?}"
        );
    }
}

#[test]
fn rejects_more_threads_than_the_machine_runs() {
    assert!(matches!(
        setup(usize::MAX),
        Err(Error::TooManyThreads {
            threads: usize::MAX,
            ..
        })
    ));
}
