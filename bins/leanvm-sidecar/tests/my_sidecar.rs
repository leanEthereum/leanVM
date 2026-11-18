//! A manual check against a sidecar already running, `#[ignore]`d so that only this command runs it:
//!
//!     cargo test --release -p leanvm-sidecar --test my_sidecar -- --ignored --nocapture
//!
//! Connects to `LEANVM_SIDECAR_SOCKET` (default `~/.leanvm/sidecar.sock`), proves a leaf of `LEANVM_XMSS` (default 8)
//! leanXMSS signatures, then a node over it with one more, and verifies both.

use aggregation::signers_cache;
use lean_vm::OutputClaims;
use sidecar::Client;
use stable_lean_vm_core::StableProver;
use std::path::PathBuf;
use std::time::Instant;

#[test]
#[ignore]
fn my_sidecar() {
    let socket = std::env::var_os("LEANVM_SIDECAR_SOCKET")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(std::env::var_os("HOME").expect("HOME")).join(".leanvm/sidecar.sock"));
    let n: usize = std::env::var("LEANVM_XMSS").map_or(8, |v| v.parse().expect("LEANVM_XMSS"));

    let mut client = Client::connect(&socket).unwrap_or_else(|e| panic!("{}: {e:?}", socket.display()));
    println!("connected to {}, {} prover", socket.display(), client.prover());

    let xmss = signers_cache::get_signers::<StableProver>(n + 1);

    let start = Instant::now();
    let leaf = client
        .aggregate(&[], &xmss[..n], &[], &[], OutputClaims::All, 1)
        .unwrap();
    println!("leaf: {n} signatures, {:.1?}, {} bytes", start.elapsed(), leaf.1.len());
    assert_eq!(leaf.0.num_signature_claims(), n);
    assert!(client.verify(&leaf.0, &leaf.1).unwrap());

    let start = Instant::now();
    let node = client
        .aggregate(&[leaf], &xmss[n..], &[], &[], OutputClaims::All, 1)
        .unwrap();
    println!(
        "node: the leaf and 1 more, {:.1?}, {} bytes",
        start.elapsed(),
        node.1.len()
    );
    assert_eq!(node.0.num_signature_claims(), n + 1);
    assert!(client.verify(&node.0, &node.1).unwrap());
    println!("both verified");
}
