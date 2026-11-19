//! leanXMSS and leanSPHINCS aggregation through the safe facade, against the sidecar listening on
//! `$LEANVM_SIDECAR_SOCKET`.
#![cfg(unix)]

use std::sync::LazyLock;

use lean_pq::{sphincs, xmss, Aggregate, Error, Message, Sidecar, MAX_CHILDREN};

static SIDECAR: LazyLock<Sidecar> = LazyLock::new(|| {
    let socket = std::env::var_os("LEANVM_SIDECAR_SOCKET")
        .expect("set LEANVM_SIDECAR_SOCKET to the socket of a running leanvm-sidecar");
    Sidecar::connect(socket).unwrap()
});

fn aggregate(
    children: &[&Aggregate],
    xmss: &[(xmss::PublicKey, Message, xmss::Signature)],
    sphincs: &[(sphincs::PublicKey, Message, sphincs::Signature)],
) -> Result<Aggregate, Error> {
    SIDECAR.aggregate(children, xmss, sphincs)
}

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

/// Claim lists as `Sidecar::verify` takes them.
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
    let received = SIDECAR
        .verify(
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
fn rejects_claims_the_proof_does_not_prove() {
    let xmss_key = SIGNERS.xmss.public_key();
    // The same 32 bytes, read as a leanSPHINCS key.
    let as_sphincs = sphincs::PublicKey::from_bytes(&xmss_key.to_bytes()).unwrap();
    let bytes = LEAF.to_bytes();
    SIDECAR.verify(&bytes, &[(xmss_key, FIRST)], &[]).unwrap();

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
            SIDECAR
                .verify(&bytes, xmss_claims, sphincs_claims)
                .unwrap_err(),
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
    // Bindings match on this prefix; the reason after it is the sidecar's wording.
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
        assert_eq!(
            SIDECAR.verify(mutated, &claims, &[]).unwrap_err(),
            Error::AggregateRejected
        );
    }
}

#[test]
fn starts_and_stops_its_own_sidecar() {
    let binary = std::env::var_os("LEANVM_SIDECAR_BIN")
        .expect("set LEANVM_SIDECAR_BIN to a leanvm-sidecar executable");
    // Short: a Unix socket path holds at most 104 bytes on macOS.
    let directory = std::env::temp_dir().join(format!("lpq{}", std::process::id()));
    let socket = directory.join("s.sock");

    let started = Sidecar::start(&binary, &socket, 2).unwrap();
    assert!(["experimental", "stable"].contains(&started.prover()));
    let claims = [(SIGNERS.xmss.public_key(), FIRST)];
    started.verify(&LEAF.to_bytes(), &claims, &[]).unwrap();

    // A second start on the same socket would steal it: it fails while the first one runs.
    let error = Sidecar::start(&binary, &socket, 0).unwrap_err();
    assert!(error.to_string().contains("already listens"), "{error}");

    // Dropping it stops the sidecar.
    drop(started);
    assert!(matches!(
        Sidecar::connect(&socket).unwrap_err(),
        Error::Sidecar { .. }
    ));
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn close_stops_a_started_sidecar_and_fails_the_call_in_progress() {
    let binary = std::env::var_os("LEANVM_SIDECAR_BIN")
        .expect("set LEANVM_SIDECAR_BIN to a leanvm-sidecar executable");
    let directory = std::env::temp_dir().join(format!("lpqc{}", std::process::id()));
    let socket = directory.join("s.sock");
    let started = Sidecar::start(&binary, &socket, 2).unwrap();

    std::thread::scope(|scope| {
        let proving = scope.spawn(|| started.aggregate(&[], &[xmss_input(SECOND, 9)], &[]));
        // Let the proof start, then close: it stops the sidecar under the call.
        std::thread::sleep(std::time::Duration::from_millis(500));
        started.close();
        assert!(proving.join().unwrap().is_err());
    });
    assert_eq!(
        started.verify(&LEAF.to_bytes(), &[], &[]).unwrap_err(),
        Error::SidecarClosed
    );
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn refuses_a_socket_directory_open_to_others() {
    use std::os::unix::fs::PermissionsExt;
    let directory = std::env::temp_dir().join(format!("lpqo{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    std::fs::set_permissions(&directory, std::fs::Permissions::from_mode(0o777)).unwrap();
    let error = Sidecar::start("leanvm-sidecar", directory.join("s.sock"), 0).unwrap_err();
    assert!(error.to_string().contains("open to other users"), "{error}");
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn refuses_empty_paths() {
    assert!(Sidecar::connect("").is_err());
    assert!(Sidecar::start("leanvm-sidecar", "", 0).is_err());
}

#[test]
fn fails_to_start_a_missing_binary() {
    let directory = std::env::temp_dir().join(format!("lpqm{}", std::process::id()));
    let error =
        Sidecar::start("/nonexistent/leanvm-sidecar", directory.join("s.sock"), 0).unwrap_err();
    assert!(error.to_string().contains("cannot run"), "{error}");
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn fails_to_connect_where_no_sidecar_listens() {
    let error = Sidecar::connect("/nonexistent/leanvm-sidecar.sock").unwrap_err();
    assert!(matches!(error, Error::Sidecar { .. }), "{error:?}");
    assert!(error.to_string().starts_with("leanVM sidecar: "));
}
