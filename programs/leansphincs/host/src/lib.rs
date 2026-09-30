//! The leanSPHINCS program off the VM: it signs, lays the signatures out as the guest's
//! advice, and verifies them natively for the output the guest must give.
//!
//! One message for all signers is the Ethereum shape: validators attest to one block.

use leansphincs::{Message, PublicKey, Signature};
use leanvm_guest::{PublicValues, as_words_unchecked};

/// The guest (`../guest`), built by `programs/build.sh`.
pub const ELF: &[u8] = include_bytes!("../../leansphincs.elf");

/// What one run of the guest is given, and what it must output.
pub struct Run {
    pub advice: Vec<u64>,
    pub expected: [u64; 4],
}

/// The message every signer signs.
const MESSAGE: Message = [0x4242_4242_4242_4242; 4];

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
        let (sk, pk) = leansphincs::key_gen(seed(i));
        (pk, sk.sign(&MESSAGE).expect("an admissible digest and encodings"))
    });
    // What the guest reads: the count, then key, message and signature for each.
    let mut advice = vec![n as u64];
    // What it commits: each claim, key and message.
    let mut public = PublicValues::new();
    for (pk, signature) in &signed {
        leansphincs::verify(pk, &MESSAGE, signature).expect("honest signatures verify");
        advice.extend(words_of_key(pk));
        advice.extend(MESSAGE);
        advice.extend(words_of_signature(signature));
        public.commit(&pk.root).commit(&pk.public_param).commit(&MESSAGE);
    }
    Run {
        advice,
        expected: public.digest(),
    }
}

/// A key as the words the guest reads it from.
fn words_of_key(pk: &PublicKey) -> &[u64] {
    // SAFETY: `repr(C)` words, with no padding (see its definition).
    unsafe { as_words_unchecked(pk) }
}

/// A signature as the words the guest reads it from.
fn words_of_signature(signature: &Signature) -> &[u64] {
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

    /// A layer's counter, one-time signature and path, to tamper with.
    fn layer(s: &mut leansphincs::Signature, lay: usize) -> (&mut u64, &mut [[u64; 2]; 42], &mut [[u64; 2]]) {
        match lay {
            0 => (&mut s.layer0.counter, &mut s.layer0.ots, &mut s.layer0.path),
            1 => (&mut s.layer1.counter, &mut s.layer1.ots, &mut s.layer1.path),
            _ => (&mut s.layer2.counter, &mut s.layer2.ots, &mut s.layer2.path),
        }
    }

    #[test]
    fn leansphincs_is_the_specified_scheme() {
        // Known answers of the SPHINCS+ specification's implementation.
        //
        // The signature's digest is over its specification bytes, each counter in 4 bytes.
        let (seed, message) = fixed();
        let (sk, public_key) = leansphincs::key_gen(seed);
        let signature = sk.sign(&message).unwrap();
        assert_eq!(
            hex(bytes(words_of_key(&public_key))),
            "cd0efd73b0e58cec9291994a125dae7c5957ef5b2c556a3f7b0117d93e98e61b"
        );
        assert_eq!(
            hex(primitives::hash::hash(&signature.to_bytes())),
            "76f771d246ae4460e0d2d193c567c8352cfc6e3ccd6e4d68d25955832d5e3431"
        );
        assert_eq!(leansphincs::verify(&public_key, &message, &signature), Ok(()));
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

    /// The guest on the interpreter, with no proof: its output, or the trap.
    fn on_the_vm(run: &Run) -> Result<[u64; 4], leanvm_core::rv::Trap> {
        let program = leanvm_core::cpu::Program::from_elf(ELF).expect("the guest's ELF file");
        leanvm_core::rv::Machine::new(program.rv(), &run.advice).run(1 << 30)
    }

    #[test]
    fn the_guest_checks_what_the_native_code_checks() {
        // The guest on the interpreter outputs what its code computes natively.
        let mut run = batch(2);
        assert_eq!(on_the_vm(&run), Ok(run.expected));

        // Mutation: the top bit of the advice's last word, a node of the last signature's path.
        //
        //     the guest's check fails → it panics → an illegal instruction → no output
        *run.advice.last_mut().unwrap() ^= 1 << 63;
        assert!(on_the_vm(&run).is_err());
    }
}
