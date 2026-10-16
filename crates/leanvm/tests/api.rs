use leanvm::*;

const MSG_0: xmss::Message = [0; xmss::MESSAGE_LEN];
const MSG_1: xmss::Message = [1; xmss::MESSAGE_LEN];
const MSG_2: xmss::Message = [2; xmss::MESSAGE_LEN];

#[test]
fn public_api_end_to_end() {
    setup_prover();
    let rng = &mut rand::rng();

    // 1. Eight XMSS signatures over three messages, three of the first, four of the second, one of the third.
    //    Each signature carries its own leaf index, which the statement does not record.
    let mut xmss_input = Vec::new();
    let mut leaf_index = 7;
    for (message, count) in [(MSG_0, 3), (MSG_1, 4), (MSG_2, 1)] {
        for _ in 0..count {
            let (secret_key, pub_key) = xmss::key_gen(rng, leaf_index, leaf_index).unwrap();
            let signature = xmss::sign(&secret_key, &message, leaf_index).unwrap();
            xmss_input.push((pub_key, message, signature));
            leaf_index = leaf_index * 5 + 1;
        }
    }

    // 2. Three SPHINCS signatures, each on its own message, by keys pruned to a subtree of height 8
    let mut sphincs_input = Vec::new();
    for signer in 0..3u8 {
        let (secret_key, pub_key) = sphincs::key_gen(rng, 8);
        let message = [signer; sphincs::MESSAGE_LEN];
        let signature = sphincs::sign(&secret_key, &message).unwrap();
        sphincs_input.push((pub_key, message, signature));
    }

    // 3. Two leaves, then a root over both. Both leaves hold claims on the second message; the root's claims are the union.
    let blobs: Vec<_> = (0..lean_da::BLOB_SYMBOLS).map(|i| i as u64).collect();
    let (commitment, _) = lean_da::commit(&blobs);
    let left = aggregate(
        &[],
        xmss_input[..4].to_vec(),
        sphincs_input[..1].to_vec(),
        &blobs,
        None,
        2,
    )
    .unwrap();
    let left = EthereumProof::from_bytes(&left.to_bytes()).unwrap();
    left.verify().unwrap();
    assert_eq!(left.da_commitments(), &[commitment.root]);
    let other_blobs: Vec<_> = blobs.iter().map(|x| x ^ 42).collect();
    let (other_commitment, _) = lean_da::commit(&other_blobs);
    let right = aggregate(
        &[],
        xmss_input[4..7].to_vec(),
        sphincs_input[1..].to_vec(),
        &other_blobs,
        None,
        2,
    )
    .unwrap();
    let mut roots = vec![commitment.root, other_commitment.root];
    roots.sort();
    let root = aggregate(&[left, right], xmss_input[7..].to_vec(), vec![], &[], None, 2).unwrap();
    assert_eq!(root.num_signature_claims(), 11);
    assert_eq!(root.da_commitments(), roots);

    // 4. Onto the wire, and back to a receiver, which checks the statement itself:
    //    verifying says these pubkeys signed, the messages being the prover's.
    let bytes = root.to_bytes();
    let received = EthereumProof::from_bytes(&bytes).unwrap();
    received.verify().unwrap();
    assert_eq!(received.da_commitments(), roots);
    let on = |message| received.xmss_signers().iter().filter(|(_, m)| *m == message).count();
    assert_eq!((on(MSG_0), on(MSG_1), on(MSG_2)), (3, 4, 1));

    // 5. Removing some signatures from the aggregate: `declare` is what we keep. Here every claim on MSG_1 goes.
    let (dropped_claims, xmss_signers): (Vec<_>, Vec<_>) =
        received.xmss_signers().iter().cloned().partition(|(_, m)| *m == MSG_1);
    let mut sphincs_signers = received.sphincs_signers().to_vec();
    let dropped_signer = sphincs_signers.remove(0);
    let retained_signatures = SignatureClaims {
        xmss: xmss_signers,
        sphincs: sphincs_signers,
    };
    let narrowed = aggregate(
        &[received],
        vec![],
        vec![],
        &[],
        Some(ClaimSelection {
            signatures: &retained_signatures,
            da_commitments: &[commitment.root],
        }),
        2,
    )
    .unwrap();
    narrowed.verify().unwrap();
    assert_eq!(narrowed.da_commitments(), &[commitment.root]);
    assert_eq!(narrowed.num_signature_claims(), 11 - dropped_claims.len() - 1);
    assert!(
        dropped_claims
            .iter()
            .all(|claim| !narrowed.xmss_signers().contains(claim))
    );
    assert!(!narrowed.sphincs_signers().contains(&dropped_signer));

    let dropped = aggregate(
        &[narrowed],
        vec![],
        vec![],
        &[],
        Some(ClaimSelection {
            signatures: &retained_signatures,
            da_commitments: &[],
        }),
        2,
    )
    .unwrap();
    dropped.verify().unwrap();
    assert!(dropped.da_commitments().is_empty());
    assert_eq!(dropped.xmss_signers(), retained_signatures.xmss);
    assert_eq!(dropped.sphincs_signers(), retained_signatures.sphincs);
}
