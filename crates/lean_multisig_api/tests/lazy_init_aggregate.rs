use lean_multisig_api::{Claim, SecretKey, aggregate};

#[test]
fn aggregate_initializes_the_bytecode() {
    let claim = Claim::new([0u8; 32], 0);
    let key = SecretKey::from_seed([1u8; 32], 0..=15).unwrap();
    aggregate(vec![key.sign(&claim).unwrap()], &claim).unwrap();

    // Panics if aggregation did not initialize the process-wide bytecode.
    let _ = rec_aggregation::get_aggregation_bytecode();
}
