//! The signature workloads: signers, each with its own key, sign one message.
//!
//! One message at one epoch for all is the Ethereum shape: validators attest to one block.

use crate::workload::Workload;

/// The message every signer signs.
const MESSAGE: [u64; 4] = [0x4242_4242_4242_4242; 4];
/// The epoch every leanXMSS signer signs at.
const EPOCH: u32 = 1234;

/// A signer's secret seed: its index, then zeros.
fn seed(i: usize) -> [u8; 32] {
    let mut seed = [0; 32];
    seed[..8].copy_from_slice(&(i as u64).to_le_bytes());
    seed
}

/// Verify `n` leanXMSS signatures in the `leanxmss` guest.
pub fn leanxmss(n: usize) -> Workload {
    // Keys and signatures are independent, so they are made in parallel.
    let entries = parallel::map_collect(n, |i| {
        let (sk, pk) = leanxmss::key_gen(seed(i), EPOCH);
        leanxmss::Entry::new(pk, EPOCH, MESSAGE, sk.sign(&MESSAGE).expect("a valid encoding"))
    });
    // The native run of the guest's own code is the reference output.
    let claims = leanxmss::verify_batch(&entries).expect("honest signatures verify");
    Workload {
        title: format!("leanXMSS verification, {n} signatures"),
        elf: include_bytes!("../guests/elf/leanxmss.elf"),
        input: [n as u64, 0, 0, 0],
        advice: entries.iter().flat_map(|e| e.as_words()).copied().collect(),
        expected: claims,
        items: n,
        item: "signature",
    }
}

/// Verify `n` leanSPHINCS signatures in the `leansphincs` guest.
pub fn leansphincs(n: usize) -> Workload {
    // Keys and signatures are independent, so they are made in parallel.
    let entries = parallel::map_collect(n, |i| {
        let (sk, public_key) = leansphincs::key_gen(seed(i));
        let signature = sk.sign(&MESSAGE).expect("an admissible digest and encodings");
        leansphincs::Entry {
            public_key,
            message: MESSAGE,
            signature,
        }
    });
    // The native run of the guest's own code is the reference output.
    let claims = leansphincs::verify_batch(&entries).expect("honest signatures verify");
    Workload {
        title: format!("leanSPHINCS verification, {n} signatures"),
        elf: include_bytes!("../guests/elf/leansphincs.elf"),
        input: [n as u64, 0, 0, 0],
        advice: entries.iter().flat_map(|e| e.as_words()).copied().collect(),
        expected: claims,
        items: n,
        item: "signature",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::workload;

    fn hex(bytes: impl IntoIterator<Item = u8>) -> String {
        bytes.into_iter().map(|b| format!("{b:02x}")).collect()
    }

    /// Words as their little-endian bytes.
    fn bytes(words: &[u64]) -> Vec<u8> {
        words.iter().flat_map(|w| w.to_le_bytes()).collect()
    }

    /// The seed `0, 1, .., 31` and the message `7, 10, 13, ..` the known answers were made with.
    fn fixed() -> ([u8; 32], [u64; 4]) {
        let message: [u8; 32] = std::array::from_fn(|i| (i * 3 + 7) as u8);
        (
            std::array::from_fn(|i| i as u8),
            std::array::from_fn(|i| u64::from_le_bytes(message[8 * i..8 * i + 8].try_into().unwrap())),
        )
    }

    /// A layer's counter, one-time signature and path, to tamper with.
    fn layer(s: &mut leansphincs::Signature, lay: usize) -> (&mut u64, &mut [[u64; 2]; 42], &mut [[u64; 2]]) {
        match lay {
            0 => (&mut s.layer0.counter, &mut s.layer0.ots, &mut s.layer0.path),
            1 => (&mut s.layer1.counter, &mut s.layer1.ots, &mut s.layer1.path),
            _ => (&mut s.layer2.counter, &mut s.layer2.ots, &mut s.layer2.path),
        }
    }

    #[test]
    fn leanxmss_is_the_specified_scheme() {
        // Known answers of the XMSS specification's implementation, at the edges of the epochs.
        //
        // Each: the epoch, the public key's bytes, the BLAKE2s digest of the signature's bytes.
        let (seed, message) = fixed();
        let known = [
            (
                0,
                "40b9356800f80f5952f617427ab29fd6c487ed3aef7201c095bf4c74aad6b6e3",
                "02ceeee5d838dcb47290e7c7d0ce8485df70c070bf97ac6bf06d294c5e9a3d61",
            ),
            (
                1234,
                "57c45784ed52b81893def5b5e3ef0aedc487ed3aef7201c095bf4c74aad6b6e3",
                "304b4e5fbb27dec445245843c7919907b3ea8c5b3f39397cd9483f47171a31e6",
            ),
            (
                u32::MAX,
                "4a66306093cfbc702910ce5dd02071e9c487ed3aef7201c095bf4c74aad6b6e3",
                "c06f727fd8bbaa02bc641f8d9382e2d69b9ad4f3e5022d4fa140c53d60a1e5d2",
            ),
        ];
        for (epoch, pk_hex, sig_digest) in known {
            let (sk, pk) = leanxmss::key_gen(seed, epoch);
            let entry = leanxmss::Entry::new(pk, epoch, message, sk.sign(&message).unwrap());
            // An entry's words are its bytes:
            //
            //     words 0..4   public key
            //     words 4..9   epoch, message
            //     words 9..    signature
            assert_eq!(hex(bytes(&entry.as_words()[..4])), pk_hex, "epoch {epoch}");
            assert_eq!(
                hex(primitives::hash::hash(&bytes(&entry.as_words()[9..]))),
                sig_digest,
                "epoch {epoch}"
            );
            assert_eq!(leanxmss::verify(&pk, epoch, &message, &entry.signature), Ok(()));
        }
    }

    #[test]
    fn leansphincs_is_the_specified_scheme() {
        // Known answers of the SPHINCS+ specification's implementation.
        //
        // The signature's digest is over its specification bytes, each counter in 4 bytes.
        let (seed, message) = fixed();
        let (sk, public_key) = leansphincs::key_gen(seed);
        let entry = leansphincs::Entry {
            public_key,
            message,
            signature: sk.sign(&message).unwrap(),
        };
        assert_eq!(
            hex(bytes(&entry.as_words()[..4])),
            "cd0efd73b0e58cec9291994a125dae7c5957ef5b2c556a3f7b0117d93e98e61b"
        );
        assert_eq!(
            hex(primitives::hash::hash(&entry.signature.to_bytes())),
            "76f771d246ae4460e0d2d193c567c8352cfc6e3ccd6e4d68d25955832d5e3431"
        );
        assert_eq!(leansphincs::verify(&public_key, &message, &entry.signature), Ok(()));
    }

    #[test]
    fn leanxmss_rejects_a_change_anywhere() {
        use leanxmss::VerifyError::{EpochOutOfRange, InvalidEncoding, InvalidMerklePath};
        // Invariant: a verifier binds the claim and every part of the signature.
        //
        // Fixture state: one honest signature at epoch 7.
        let (seed, message) = fixed();
        let (sk, pk) = leanxmss::key_gen(seed, 7);
        let signature = sk.sign(&message).unwrap();
        let verify = |pk: &leanxmss::PublicKey, epoch, message: &[u64; 4], signature: &leanxmss::Signature| {
            leanxmss::verify(pk, epoch, message, signature).err()
        };

        // Mutation: the message, the epoch, the randomness.
        //
        //     all three enter the encoding digest
        //     → a new digest, valid with probability about 2^-15
        let mut other = message;
        other[0] ^= 1;
        assert_eq!(verify(&pk, 7, &other, &signature), Some(InvalidEncoding));
        assert_eq!(verify(&pk, 8, &message, &signature), Some(InvalidEncoding));
        let mut bad = signature.clone();
        bad.randomness[0] ^= 1;
        assert_eq!(verify(&pk, 7, &message, &bad), Some(InvalidEncoding));

        // Mutation: the last chain tip's top bit, the last path node, the root.
        //
        //     the encoding still holds
        //     → a different leaf or fold, which misses the root
        let mut bad = signature.clone();
        bad.chain_tips[41][1] ^= 1 << 63;
        assert_eq!(verify(&pk, 7, &message, &bad), Some(InvalidMerklePath));
        let mut bad = signature.clone();
        bad.merkle_proof[31][0] ^= 1;
        assert_eq!(verify(&pk, 7, &message, &bad), Some(InvalidMerklePath));
        let mut bad_pk = pk;
        bad_pk.merkle_root[0] ^= 1;
        assert_eq!(verify(&bad_pk, 7, &message, &signature), Some(InvalidMerklePath));

        // Mutation: an entry's epoch word with bit 32 set.
        //
        //     claimed epoch   2^32 + 7
        //     leaf index      7, were it truncated
        //     → rejected rather than verified at another epoch than claimed
        let mut entry = leanxmss::Entry::new(pk, 7, message, signature);
        entry.epoch |= 1 << 32;
        assert_eq!(leanxmss::verify_batch(&[entry]), Err((0, EpochOutOfRange)));
    }

    #[test]
    fn leansphincs_rejects_a_change_anywhere() {
        use leansphincs::VerifyError::{InadmissibleDigest, InadmissibleEncoding, RootMismatch};
        // Invariant: a verifier binds every part of the signature, on every layer.
        //
        // Fixture state: one honest signature, checked after each mutation with its error.
        let (seed, message) = fixed();
        let (sk, pk) = leansphincs::key_gen(seed);
        let signature = sk.sign(&message).unwrap();
        let rejects = |change: &dyn Fn(&mut leansphincs::Signature), expected: leansphincs::VerifyError| {
            let mut bad = signature.clone();
            change(&mut bad);
            assert_eq!(leansphincs::verify(&pk, &message, &bad), Err(expected));
        };

        // Mutation: the randomizer, so a new message digest.
        //
        //     its last index is zero once in 2^10 → inadmissible
        rejects(&|s| s.randomizer[0] ^= 1, InadmissibleDigest);

        // Mutation: a few-time secret, a few-time path node.
        //
        //     a new few-time key → the bottom layer's encoding of it fails
        rejects(&|s| s.fts[0].secret[0] ^= 1, InadmissibleEncoding);
        rejects(&|s| s.fts[13].path[9][1] ^= 1 << 63, InadmissibleEncoding);

        for lay in 0..3 {
            // Mutation: the layer's counter, flipped or pushed past 32 bits.
            rejects(&|s| *layer(s, lay).0 ^= 1, InadmissibleEncoding);
            rejects(&|s| *layer(s, lay).0 |= 1 << 32, InadmissibleEncoding);

            // Mutation: a one-time chain value, the layer's last path node.
            //
            //     a new root of the layer's tree
            //     top layer    → it is not the public key's root
            //     other layer  → it is the next layer's message, whose encoding fails
            let moved = if lay == 0 { RootMismatch } else { InadmissibleEncoding };
            rejects(&|s| layer(s, lay).1[20][1] ^= 1, moved);
            rejects(&|s| layer(s, lay).2.last_mut().unwrap()[0] ^= 1, moved);
        }
    }

    #[test]
    fn the_signature_guests_check_what_the_native_code_checks() {
        for workload in [leanxmss(3), leansphincs(2)] {
            // The guest on the interpreter outputs what its code computes natively.
            assert_eq!(workload.run(), Ok(workload.expected), "{}", workload.title);

            // Mutation: the top bit of the advice's last word, a node of the last signature's path.
            //
            //     the guest's check fails → it panics → an illegal instruction → no output
            let mut forged = workload;
            *forged.advice.last_mut().unwrap() ^= 1 << 63;
            assert!(forged.run().is_err(), "{}", forged.title);
        }
    }

    #[test]
    fn the_signature_guests_prove() {
        // End to end: proven, verified, and the output the native digest.
        for workload in [leanxmss(2), leansphincs(1)] {
            workload::run(
                &workload,
                lean_vm::pcs::TEST_LOG_INV_RATE,
                primitives::bench::Plan::default(),
            );
        }
    }
}
