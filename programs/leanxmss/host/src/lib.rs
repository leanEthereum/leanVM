//! The leanXMSS program off the VM: it signs, lays the signatures out as the guest's
//! advice, and verifies them natively for the output the guest must give.
//!
//! One message at one leaf index for all signers is the Ethereum shape: validators attest to one block.

use leanvm_guest::{PublicValues, as_words_unchecked};
use leanxmss::{LeafIndex, Message, PublicKey, Signature};

/// The guest (`../guest`), built by `programs/build.sh`.
pub const ELF: &[u8] = include_bytes!("../../leanxmss.elf");

/// What one run of the guest is given, and what it must output.
pub struct Run {
    pub advice: Vec<u64>,
    pub expected: [u64; 4],
}

/// The message every signer signs.
const MESSAGE: Message = [0x4242_4242_4242_4242; 4];
/// The leaf index every signer signs at.
const LEAF_INDEX: LeafIndex = 1234;

/// A signer's secret seed: its index, then zeros.
fn seed(i: usize) -> [u8; 32] {
    let mut seed = [0; 32];
    seed[..8].copy_from_slice(&(i as u64).to_le_bytes());
    seed
}

/// `n` signers, each with its own key, sign the message.
pub fn batch(n: usize) -> Run {
    // Keys and signatures are independent, so they are made in parallel.
    let signed = parallel::map_collect(n, |i| {
        let (sk, pk) = leanxmss::key_gen(seed(i), LEAF_INDEX);
        (pk, sk.sign(&MESSAGE).expect("a valid encoding"))
    });
    // What the guest reads: the count, then key, leaf index, message and signature for each.
    let mut advice = vec![n as u64];
    // What it commits: each claim, key, leaf index and message.
    let mut public = PublicValues::new();
    for (pk, signature) in &signed {
        leanxmss::verify(pk, LEAF_INDEX, &MESSAGE, signature).expect("honest signatures verify");
        advice.extend(words_of_key(pk));
        advice.push(LEAF_INDEX.into());
        advice.extend(MESSAGE);
        advice.extend(words_of_signature(signature));
        public
            .commit(&pk.merkle_root)
            .commit(&pk.public_param)
            .commit(&u64::from(LEAF_INDEX))
            .commit(&MESSAGE);
    }
    Run {
        advice,
        expected: public.digest(),
    }
}

/// A key as the words the guest reads it from.
const fn words_of_key(pk: &PublicKey) -> &[u64] {
    // SAFETY: `repr(C)` words, with no padding (see its definition).
    unsafe { as_words_unchecked(pk) }
}

/// A signature as the words the guest reads it from.
const fn words_of_signature(signature: &Signature) -> &[u64] {
    // SAFETY: `repr(C)` words, with no padding (see its definition).
    unsafe { as_words_unchecked(signature) }
}

#[cfg(test)]
mod tests {
    use super::*;

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

    #[test]
    fn leanxmss_is_the_specified_scheme() {
        // Known answers of the XMSS specification's implementation, at the edges of the leaf indices.
        //
        // Each: the leaf index, the public key's bytes, the BLAKE2s digest of the signature's bytes.
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
        for (leaf_index, pk_hex, sig_digest) in known {
            let (sk, pk) = leanxmss::key_gen(seed, leaf_index);
            let signature = sk.sign(&message).unwrap();
            // The key's and the signature's words are their specification bytes.
            assert_eq!(hex(bytes(words_of_key(&pk))), pk_hex, "leaf index {leaf_index}");
            assert_eq!(
                hex(primitives::hash::hash(&bytes(words_of_signature(&signature)))),
                sig_digest,
                "leaf index {leaf_index}"
            );
            assert_eq!(leanxmss::verify(&pk, leaf_index, &message, &signature), Ok(()));
        }
    }

    #[test]
    fn leanxmss_rejects_a_change_anywhere() {
        use leanxmss::XmssVerifyError::{InvalidEncoding, InvalidMerklePath};
        // Invariant: a verifier binds the claim and every part of the signature.
        //
        // Fixture state: one honest signature at leaf index 7.
        let (seed, message) = fixed();
        let (sk, pk) = leanxmss::key_gen(seed, 7);
        let signature = sk.sign(&message).unwrap();
        let verify = |pk: &leanxmss::PublicKey, leaf_index, message: &[u64; 4], signature: &leanxmss::Signature| {
            leanxmss::verify(pk, leaf_index, message, signature).err()
        };

        // Mutation: the message, the leaf index, the randomness.
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
    }

    /// The guest on the interpreter, with no proof: its output, or the trap.
    fn on_the_vm(run: &Run) -> Result<[u64; 4], leanvm_core::rv::Trap> {
        let program = leanvm_core::cpu::Program::from_elf(ELF).expect("the guest's ELF file");
        leanvm_core::rv::Machine::new(program.rv(), &run.advice).run()
    }

    #[test]
    fn the_guest_checks_what_the_native_code_checks() {
        // The guest on the interpreter outputs what its code computes natively.
        let mut run = batch(3);
        assert_eq!(on_the_vm(&run), Ok(run.expected));

        // Mutation: the top bit of the advice's last word, a node of the last signature's path.
        //
        //     the guest's check fails → it panics → an illegal instruction → no output
        let mut forged = run.advice.clone();
        *forged.last_mut().unwrap() ^= 1 << 63;
        assert!(on_the_vm(&Run { advice: forged, ..run }).is_err());

        // Mutation: the first leaf index word (after the count and the key) with bit 32 set.
        //
        //     claimed leaf index   2^32 + 1234
        //     truncated            1234, which verifies
        //     → the guest refuses the word rather than verify at another leaf index than committed
        run = batch(1);
        run.advice[1 + 4] |= 1 << 32;
        assert!(on_the_vm(&run).is_err());
    }

    #[test]
    fn leanxmss_outputs_the_blake2s_of_its_claims() {
        // Invariant: the output is BLAKE2s-256 of the claims (key, leaf index, message: 9 words) back to back.
        //
        // Every count up to 9 claims: a claim is 72 bytes, so its end falls at each offset of a 64-byte block, 8 claims
        // end on a block boundary and 0 are the empty message.
        let claim = size_of::<PublicKey>() / 8 + 1 + MESSAGE.len();
        let entry = claim + size_of::<Signature>() / 8;
        for n in 0..=9 {
            let run = batch(n);
            // The advice is the count, then each entry: its claim, then its signature.
            assert_eq!(run.advice.len(), 1 + n * entry);
            let claims: Vec<u64> = run.advice[1..]
                .chunks(entry)
                .flat_map(|e| e[..claim].to_vec())
                .collect();
            let digest = primitives::hash::hash(&bytes(&claims));
            let expected = std::array::from_fn(|i| u64::from_le_bytes(digest[8 * i..8 * i + 8].try_into().unwrap()));
            assert_eq!(run.expected, expected, "{n} claims, natively");
            assert_eq!(on_the_vm(&run), Ok(expected), "{n} claims, on the VM");
        }
    }
}
