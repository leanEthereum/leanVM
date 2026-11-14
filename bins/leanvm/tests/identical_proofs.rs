//! The stable and the experimental prover give the same proof of the same statement, byte for byte: three leaves (leanXMSS
//! signatures and blobs, leanSPHINCS signatures, both schemes and blobs) and a recursion node over them, at the four
//! rates. Both trees' thread pools run in this one process, each idle while the other proves.

use experimental_leanvm_core::Experimental;
use isa::Prover;
use rec_aggregation::{OutputClaims, aggregate, signers_cache};
use stable_leanvm_core::Stable;

/// The proofs `P` gives: the three leaves', then the node's.
fn proofs<P: Prover>() -> [Vec<u8>; 4] {
    P::init();
    let symbols: Vec<u128> = (0..2 * lean_da::BLOB_SYMBOLS as u128)
        .map(|i| i.wrapping_mul(0x9e37_79b9_7f4a_7c15))
        .collect();
    let blobs = lean_da::BlobMatrix::build::<P>(symbols.as_chunks().0).unwrap();
    let (xmss, sphincs) = (
        signers_cache::get_signers(5),
        signers_cache::get_lean_sphincs_signers(2),
    );
    let left = aggregate::<P>(&[], xmss[..3].to_vec(), vec![], Some(&blobs), OutputClaims::All, 1).unwrap();
    let right = aggregate::<P>(&[], vec![], sphincs[..1].to_vec(), None, OutputClaims::All, 2).unwrap();
    let mixed = aggregate::<P>(
        &[],
        xmss[3..].to_vec(),
        sphincs[1..].to_vec(),
        Some(&blobs),
        OutputClaims::All,
        3,
    )
    .unwrap();
    let children = [left.clone(), right.clone(), mixed.clone()];
    let node = aggregate::<P>(&children, vec![], vec![], None, OutputClaims::All, 4).unwrap();
    [left, right, mixed, node].map(|(_, proof)| proof.to_bytes())
}

#[test]
fn stable_and_experimental_proofs_are_identical() {
    let (experimental, stable) = (proofs::<Experimental>(), proofs::<Stable>());
    for (name, (e, s)) in ["left leaf", "right leaf", "mixed leaf", "node"]
        .iter()
        .zip(experimental.iter().zip(&stable))
    {
        assert!(e == s, "the {name}'s proofs differ ({} and {} bytes)", e.len(), s.len());
    }
}
