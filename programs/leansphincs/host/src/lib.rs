//! The leanSPHINCS program off the VM: it signs, lays the signatures out as the guest's
//! advice, and builds the signer set the guest proves, whose digest gives its output.
//!
//! One message for all signers is the Ethereum shape: validators attest to one block.
//!
//! It also owns the program's signer sets ([`SignerSet`]): the claims an aggregate of its proofs publishes.

mod signers;

pub use leansphincs::{LayerSignature, Message, PublicKey, Signature};
pub use signers::{SignerSet, SignerSetError, SphincsClaim};

use core::ops::Range;
use leanvm_guest::{PublicValues, Run, as_words_unchecked};

/// The guest (`../guest`), built by `programs/build.sh`.
pub const ELF: &[u8] = include_bytes!("../../leansphincs.elf");

/// The message every signer of [`batch`] signs.
pub const MESSAGE: Message = [0x4242_4242_4242_4242; 4];

/// A signer's secret seed: its index, then zeros.
fn seed(i: usize) -> [u8; 32] {
    let mut seed = [0; 32];
    seed[..8].copy_from_slice(&(i as u64).to_le_bytes());
    seed
}

/// `n` signers, each with its own key, sign [`MESSAGE`]: each one's key and signature, as [`batch`]'s.
pub fn signers(n: usize) -> Vec<(PublicKey, Signature)> {
    // Keys and signatures are independent, so they are made in parallel.
    parallel::map_collect(n, |i| {
        let (sk, pk) = leansphincs::key_gen(seed(i));
        (pk, sk.sign(&MESSAGE).expect("an admissible digest and encodings"))
    })
}

/// Signers that sign one message. Signer `i`'s key is the one from `i`'s seed, in every group.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Group {
    /// The message.
    pub message: Message,
    /// The signers, by index.
    pub signers: Range<usize>,
}

/// Signatures as the guest reads them, and the signer set it proves.
#[derive(Clone, Debug)]
pub struct Batch {
    /// The guest's advice, and the output it must give: the BLAKE2s of `set`'s digest, the one value it commits.
    pub run: Run,
    /// The claims the guest verifies, each [`Group`]'s signers under its message, in their order (not canonical).
    pub set: SignerSet,
}

/// `n` signers, each with its own key, sign the message: one group.
pub fn batch(n: usize) -> Batch {
    batch_groups(&[Group {
        message: MESSAGE,
        signers: 0..n,
    }])
}

/// Each group's signers sign its message.
pub fn batch_groups(groups: &[Group]) -> Batch {
    // Every group's signers, one after the other; their keys and signatures are independent, so made in parallel.
    let jobs: Vec<(&Group, usize)> = (groups.iter())
        .flat_map(|g| g.signers.clone().map(move |i| (g, i)))
        .collect();
    let signed = parallel::map_collect(jobs.len(), |j| {
        let (g, i) = jobs[j];
        let (sk, pk) = leansphincs::key_gen(seed(i));
        (pk, sk.sign(&g.message).expect("an admissible digest and encodings"))
    });
    let mut signed = signed.iter();
    // What the guest reads: the number of groups, then for each its message and count, then each key and signature.
    let mut advice = vec![groups.len() as u64];
    let mut set = SignerSet::new();
    for g in groups {
        advice.extend(g.message);
        advice.push(g.signers.len() as u64);
        for (pk, signature) in signed.by_ref().take(g.signers.len()) {
            leansphincs::verify(pk, &g.message, signature).expect("honest signatures verify");
            advice.extend(words_of_key(pk));
            advice.extend(words_of_signature(signature));
            set.claims.push(SphincsClaim {
                key: *pk,
                message: g.message,
            });
        }
    }
    // What it commits: the set's digest.
    let mut public = PublicValues::new();
    public.commit(&set.digest());
    Batch {
        run: Run {
            advice,
            expected: public.digest(),
        },
        set,
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
    use leansphincs::SphincsVerifyError::{InadmissibleDigest, InadmissibleEncoding, RootMismatch};
    use leansphincs::signers::Stream;
    use leansphincs::{Signature, SphincsVerifyError};
    use leanvm::{Machine, Program, Trap};
    use primitives::hash::digest_words;

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
        (std::array::from_fn(|i| i as u8), digest_words(&message))
    }

    /// A layer's counter, one-time signature and path, to tamper with.
    fn layer(s: &mut Signature, lay: usize) -> (&mut u64, &mut [[u64; 2]; 42], &mut [[u64; 2]]) {
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

    /// The known answers' key, message and specification bytes of the signature, as hex, for the Lean
    /// specification's check of them (`verification/circuits/Spec/LeanSphincs/Kat.lean`).
    ///
    /// `cargo test -p leansphincs-host print_known_answers -- --ignored --nocapture`
    #[test]
    #[ignore = "prints the known answers for the Lean specification"]
    fn print_known_answers() {
        let (seed, message) = fixed();
        let (sk, public_key) = leansphincs::key_gen(seed);
        let signature = sk.sign(&message).unwrap();
        println!("public key {}", hex(bytes(words_of_key(&public_key))));
        println!("message {}", hex(bytes(&message)));
        println!("signature {}", hex(signature.to_bytes()));
    }

    #[test]
    fn leansphincs_rejects_a_change_anywhere() {
        // Invariant: a verifier binds every part of the signature, on every layer.
        //
        // Fixture state: one honest signature, checked after each mutation with its error.
        let (seed, message) = fixed();
        let (sk, pk) = leansphincs::key_gen(seed);
        let signature = sk.sign(&message).unwrap();
        let rejects = |change: &dyn Fn(&mut Signature), expected: SphincsVerifyError| {
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
        let bottom = InadmissibleEncoding {
            layer: leansphincs::D - 1,
        };
        rejects(&|s| s.fts[0].secret[0] ^= 1, bottom);
        rejects(&|s| s.fts[13].path[9][1] ^= 1 << 63, bottom);

        for lay in 0..3 {
            // Mutation: the layer's counter, flipped or pushed past 32 bits.
            rejects(&|s| *layer(s, lay).0 ^= 1, InadmissibleEncoding { layer: lay });
            rejects(&|s| *layer(s, lay).0 |= 1 << 32, InadmissibleEncoding { layer: lay });

            // Mutation: a one-time chain value, the layer's last path node.
            //
            //     a new root of the layer's tree
            //     top layer    → it is not the public key's root
            //     other layer  → it is the message of the layer above, whose encoding fails
            let moved = if lay == 0 {
                RootMismatch
            } else {
                InadmissibleEncoding { layer: lay - 1 }
            };
            rejects(&|s| layer(s, lay).1[20][1] ^= 1, moved);
            rejects(&|s| layer(s, lay).2.last_mut().unwrap()[0] ^= 1, moved);
        }
    }

    /// The guest on the interpreter, with no proof: its output, or the trap.
    fn on_the_vm(run: &Run) -> Result<[u64; 4], Trap> {
        let program = Program::from_elf(ELF).expect("the guest's ELF file");
        Machine::new(program.rv(), &run.advice).run()
    }

    /// The words of a key and of a signature in the advice.
    const KEY: usize = size_of::<PublicKey>() / 8;
    const SIGNATURE: usize = size_of::<Signature>() / 8;

    /// The digest the guest's stream computes over the advice, read as the guest reads it, signatures unchecked: a
    /// run of one message opens at a group with a signature and another message than the open run's.
    fn streamed(advice: &[u64]) -> [u64; 4] {
        let mut words = advice;
        let mut take = |n: usize| {
            let (head, tail) = words.split_at(n);
            words = tail;
            head
        };
        let mut signers = Stream::new();
        let mut open = None;
        for _ in 0..take(1)[0] {
            let message: &[u64; 4] = take(4).try_into().unwrap();
            let n = take(1)[0];
            if n != 0 && open != Some(message) {
                signers.group(message);
                open = Some(message);
            }
            for _ in 0..n {
                let k = take(KEY);
                signers.key(&PublicKey {
                    root: [k[0], k[1]],
                    public_param: [k[2], k[3]],
                });
                take(SIGNATURE);
            }
        }
        assert!(words.is_empty(), "the guest reads all its advice");
        signers.finish()
    }

    /// Message `i`: the word `i`, then zeros.
    const fn message(i: u64) -> Message {
        [i, 0, 0, 0]
    }

    /// Groups of two messages, then one again: one message in two groups in a row, overlapping signers, and an empty
    /// group.
    fn groups() -> [Group; 5] {
        let group = |message, signers| Group { message, signers };
        [
            group(message(1), 0..2),
            group(message(2), 1..3),
            group(message(2), 3..4),
            group(message(3), 0..0),
            group(message(1), 0..1),
        ]
    }

    #[test]
    fn leansphincs_outputs_the_digest_of_its_signer_set() {
        // Invariant: the guest commits one value, the digest of the signer set the host builds, which a stream over
        // the advice also computes.
        let outputs = |batch: &Batch| {
            let mut public = PublicValues::new();
            public.commit(&batch.set.digest());
            assert_eq!(batch.run.expected, public.digest(), "natively");
            assert_eq!(streamed(&batch.run.advice), batch.set.digest(), "streamed");
            assert_eq!(on_the_vm(&batch.run), Ok(batch.run.expected), "on the VM");
        };

        // One group, every count up to 3: keys are written two to a block, so none, odd and even counts.
        for n in 0..=3 {
            let batch = batch(n);
            assert_eq!(batch.set.claims.len(), n);
            assert_eq!(batch.run.advice.len(), 1 + 5 + n * (KEY + SIGNATURE));
            outputs(&batch);
        }

        // Several groups, in the advice's order.
        let batch = batch_groups(&groups());
        outputs(&batch);
        let set = &batch.set;
        let messages: Vec<u64> = set.claims.iter().map(|c| c.message[0]).collect();
        assert_eq!(messages, [1, 1, 2, 2, 2, 1]);
        // Written as runs of one message: the two groups of message 2 are one, the empty group none.
        assert_eq!(set.groups().count(), 3);
        // Signer 1 under two messages, signer 0 under one twice: one key, several claims.
        assert_eq!(set.claims[1].key, set.claims[2].key);
        assert_eq!(set.claims[0], set.claims[5]);
        // The set is not canonical (its claims are in the advice's order, one repeated); its canonical form holds
        // each claim once.
        assert!(set.check().is_err());
        assert_eq!(
            SignerSet::from_claims(set.claims.clone()).claims.len(),
            set.claims.len() - 1
        );
    }

    #[test]
    fn the_guest_checks_what_the_native_code_checks() {
        let batch = batch_groups(&groups()[..2]);
        assert_eq!(on_the_vm(&batch.run), Ok(batch.run.expected));
        let forged = |at: usize, change: u64| {
            let mut run = batch.run.clone();
            run.advice[at] ^= change;
            on_the_vm(&run)
        };
        // Where the second group starts: after the count and the first group's header and 2 entries.
        let second = 1 + 5 + 2 * (KEY + SIGNATURE);

        // Mutation: the top bit of the advice's last word, a node of the last signature's path.
        //
        //     the guest's check fails → it panics → an illegal instruction → no output
        assert!(forged(batch.run.advice.len() - 1, 1 << 63).is_err());

        // Mutation: the second group's message, then a word of its first signature.
        //
        //     its signatures were made under another message, or are changed → they fail
        assert!(forged(second, 1).is_err());
        assert!(forged(second + 5 + KEY, 1).is_err());
    }
}
