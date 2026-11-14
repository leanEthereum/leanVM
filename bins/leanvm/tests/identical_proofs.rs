//! The stable and the experimental prover give the same proof of the same statement, byte for byte: three leaves (leanXMSS
//! signatures and blobs, leanSPHINCS signatures, both schemes and blobs) and a recursion node over them, at the four
//! rates. Both trees' thread pools run in this one process, each idle while the other proves.

/// The proofs one prover gives: the three leaves', then the node's.
macro_rules! proofs {
    ($agg:ident, $da:ident, $par:ident) => {{
        use $agg::{OutputClaims, aggregate, signers_cache};
        $par::init();
        let symbols: Vec<u128> = (0..2 * $da::BLOB_SYMBOLS as u128)
            .map(|i| i.wrapping_mul(0x9e37_79b9_7f4a_7c15))
            .collect();
        let blobs = $da::BlobMatrix::build(symbols.as_chunks().0).unwrap();
        let (xmss, sphincs) = (
            signers_cache::get_signers(5),
            signers_cache::get_lean_sphincs_signers(2),
        );
        let left = aggregate(&[], xmss[..3].to_vec(), vec![], Some(&blobs), OutputClaims::All, 1).unwrap();
        let right = aggregate(&[], vec![], sphincs[..1].to_vec(), None, OutputClaims::All, 2).unwrap();
        let mixed = aggregate(
            &[],
            xmss[3..].to_vec(),
            sphincs[1..].to_vec(),
            Some(&blobs),
            OutputClaims::All,
            3,
        )
        .unwrap();
        let children = [left.clone(), right.clone(), mixed.clone()];
        let node = aggregate(&children, vec![], vec![], None, OutputClaims::All, 4).unwrap();
        [left, right, mixed, node].map(|(_, proof)| proof.to_bytes())
    }};
}

#[test]
fn stable_and_experimental_proofs_are_identical() {
    let experimental = proofs!(
        experimental_rec_aggregation,
        experimental_lean_da,
        experimental_parallel
    );
    let stable = proofs!(stable_rec_aggregation, stable_lean_da, stable_parallel);
    for (name, (e, s)) in ["left leaf", "right leaf", "mixed leaf", "node"]
        .iter()
        .zip(experimental.iter().zip(&stable))
    {
        assert!(e == s, "the {name}'s proofs differ ({} and {} bytes)", e.len(), s.len());
    }
}
