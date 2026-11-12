//! The untimed pass the benchmarks run before measuring, done once before the first request.
//!
//! `leanvm::setup` builds the guest and spawns the pool. What is left to the first proof of a
//! shape is first-touch page faults on the gigabytes it allocates, which jemalloc then keeps
//! mapped, and the tables the prover and verifier cache per size and rate. One discarded
//! aggregation, verification and full-width recursion per rate pays for both.

use leanvm::lean_xmss::{self, LeafIndex, MESSAGE_LEN};
use leanvm::{MAX_RECURSIONS, aggregate};

/// Prove, verify and recurse over `signatures` fresh signatures at each of `rates`, discarding the
/// results. `signers` threads sign; they are gone before the first proof.
pub fn warm_up(signatures: usize, rates: &[usize], signers: usize) {
    let (secret_key, pub_key) = lean_xmss::key_gen();
    let secret_key = &secret_key;
    // One key, a distinct message per leaf index: `signatures` distinct claims.
    let raw: Vec<_> = std::thread::scope(|scope| {
        let workers: Vec<_> = (0..signers)
            .map(|worker| {
                scope.spawn(move || {
                    let sign = |index: usize| {
                        let mut message = [0u8; MESSAGE_LEN];
                        message[..8].copy_from_slice(&(index as u64).to_le_bytes());
                        let signature = lean_xmss::sign(secret_key, &message, index as LeafIndex).unwrap();
                        (pub_key, message, signature)
                    };
                    (worker..signatures).step_by(signers).map(sign).collect::<Vec<_>>()
                })
            })
            .collect();
        workers.into_iter().flat_map(|worker| worker.join().unwrap()).collect()
    });
    for &rate in rates {
        let leaf = aggregate(&[], raw.clone(), vec![], &[], None, rate).expect("warm-up aggregation");
        leaf.verify().expect("warm-up verification");
        // The same child in every slot: the recursion's full width, whatever the claims' union.
        let children = vec![leaf; MAX_RECURSIONS];
        aggregate(&children, vec![], vec![], &[], None, rate).expect("warm-up recursion");
    }
}
