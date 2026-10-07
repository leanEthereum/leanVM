use leanvm::*;

const LEAF_INDEX_A: xmss::LeafIndex = 7;
const LEAF_INDEX_B: xmss::LeafIndex = 11;
const MSG_0: xmss::Message = [0; xmss::MESSAGE_LEN];
const MSG_1: xmss::Message = [1; xmss::MESSAGE_LEN];
const MSG_2: xmss::Message = [2; xmss::MESSAGE_LEN];

#[test]
fn public_api_end_to_end() {
    setup_prover();
    let rng = &mut rand::rng();

    // 1. Eight XMSS signatures over three (leaf index, message) groups, three at the first,
    //    four at the second, one at the third. A group is the whole pair, so the first two share a leaf index.
    let mut xmss_input = Vec::new();
    for (leaf_index, message, count) in [
        (LEAF_INDEX_A, MSG_0, 3),
        (LEAF_INDEX_A, MSG_1, 4),
        (LEAF_INDEX_B, MSG_2, 1),
    ] {
        for _ in 0..count {
            let (secret_key, pub_key) = xmss::key_gen(rng, leaf_index, leaf_index).unwrap();
            let signature = xmss::sign(&secret_key, &message, leaf_index).unwrap();
            xmss_input.push((pub_key, leaf_index, message, signature));
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

    // 3. Two leaves, then a root over both. The leaves share the second group and the root's groups are their union.
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
    //    verifying says these keys signed, the leaf indices and messages being the prover's.
    let bytes = root.to_bytes();
    let received = EthereumProof::from_bytes(&bytes).unwrap();
    received.verify().unwrap();
    assert_eq!(received.da_commitments(), roots);
    let pairs: Vec<_> = received
        .xmss_signers()
        .iter()
        .map(|group| (group.leaf_index, group.message))
        .collect();
    assert_eq!(
        pairs,
        vec![(LEAF_INDEX_A, MSG_0), (LEAF_INDEX_A, MSG_1), (LEAF_INDEX_B, MSG_2)]
    );

    // 5. Removing some signatures from the aggregate: `declare` is what we keep. Here the first group goes whole.
    let mut groups = received.xmss_signers().to_vec();
    let mut sphincs_signers = received.sphincs_signers().to_vec();
    let dropped_group = groups.remove(0);
    let dropped_signer = sphincs_signers.remove(0);
    let retained_signatures = SignatureClaims {
        xmss: groups,
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
    assert_eq!(narrowed.num_signature_claims(), 11 - dropped_group.keys.len() - 1);
    assert!(
        !narrowed.xmss_signers().contains(&dropped_group),
        "unpublished, leaf index and message included"
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
