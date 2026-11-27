use aggregation::signers_cache::{get_lean_sphincs_signers, get_signers};
use fv_entry::{Error, decode_output, encode, prove};
use stable_lean_vm_core::StableProver;

/// A leaf from both schemes' signers, through the bytes: its proof verifies against its claims, and a cut input is
/// refused.
#[test]
fn a_leaf_through_the_bytes() {
    let input = encode(
        1,
        &[],
        &get_signers::<StableProver>(2),
        &get_lean_sphincs_signers::<StableProver>(1),
    );
    let mut out = vec![0; 1 << 24];
    let written = prove(&input, &mut out).expect("the leaf proves");
    let (claims, proof) = decode_output(&out[..written]).expect("the output decodes");
    assert_eq!((claims.lean_xmss.len(), claims.lean_sphincs.len()), (2, 1));
    assert!(proof.verify(&claims));
    assert_eq!(prove(&input[..input.len() - 1], &mut out), Err(Error::Decode));
}
