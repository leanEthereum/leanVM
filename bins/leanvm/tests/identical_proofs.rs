//! The stable and the experimental prover give the same proof of the same statement, byte for byte: a leaf over
//! signatures of both schemes and blobs, then a recursion node over two leaves.

/// The proofs one prover gives: the two leaves', then the node's.
macro_rules! proofs {
    ($agg:ident, $da:ident, $par:ident) => {{
        use $agg::{OutputClaims, aggregate, signers_cache};
        $par::init();
        let symbols: Vec<u128> = (0..2 * $da::BLOB_SYMBOLS as u128)
            .map(|i| i.wrapping_mul(0x9e37_79b9_7f4a_7c15))
            .collect();
        let blobs = $da::BlobMatrix::build(symbols.as_chunks().0).unwrap();
        let xmss = signers_cache::get_signers(3);
        let sphincs = signers_cache::get_lean_sphincs_signers(1);
        let left = aggregate(&[], xmss, vec![], Some(&blobs), OutputClaims::All, 1).unwrap();
        let right = aggregate(&[], vec![], sphincs, None, OutputClaims::All, 2).unwrap();
        let node = aggregate(
            &[left.clone(), right.clone()],
            vec![],
            vec![],
            None,
            OutputClaims::All,
            2,
        )
        .unwrap();
        [left, right, node].map(|(_, proof)| proof.to_bytes())
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
    for (name, (e, s)) in ["left leaf", "right leaf", "node"]
        .iter()
        .zip(experimental.iter().zip(&stable))
    {
        assert!(e == s, "the {name}'s proofs differ ({} and {} bytes)", e.len(), s.len());
    }
}
