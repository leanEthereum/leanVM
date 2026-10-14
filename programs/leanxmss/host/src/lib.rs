//! The leanXMSS program off the VM: it signs, lays the signatures out as the guest's
//! advice, and builds the signer set the guest proves, whose digest gives its output.
//!
//! One message at one leaf index for all signers is the Ethereum shape: validators attest to one block.
//!
//! It also owns the program's signer sets ([`SignerSet`]): the claims an aggregate of its proofs publishes.

mod signers;

pub use signers::{SignerSet, SignerSetError, XmssClaim, XmssGroup};

use core::ops::Range;
use leanvm_guest::{PublicValues, Run, as_words_unchecked};
pub use leanxmss::{LeafIndex, Message, PublicKey, Signature};

/// The guest (`../guest`), built by `programs/build.sh`.
pub const ELF: &[u8] = include_bytes!("../../leanxmss.elf");

/// The message every signer of [`batch`] signs.
pub const MESSAGE: Message = [0x4242_4242_4242_4242; 4];
/// The leaf index every signer of [`batch`] signs at.
pub const LEAF_INDEX: LeafIndex = 1234;

/// A signer's secret seed: its index, then zeros.
fn seed(i: usize) -> [u8; 32] {
    let mut seed = [0; 32];
    seed[..8].copy_from_slice(&(i as u64).to_le_bytes());
    seed
}

/// `n` signers, each with its own key, sign [`MESSAGE`] at [`LEAF_INDEX`]: each one's key and signature, as [`batch`]'s.
pub fn signers(n: usize) -> Vec<(PublicKey, Signature)> {
    // Keys and signatures are independent, so they are made in parallel.
    parallel::map_collect(n, |i| {
        let (sk, pk) = leanxmss::key_gen(seed(i), LEAF_INDEX);
        (pk, sk.sign(&MESSAGE).expect("a valid encoding"))
    })
}

/// Signers that sign one message at one leaf index.
///
/// Signer `i` signs at a leaf index with its key for that leaf index, from `i`'s seed: so a signer in two
/// groups at one leaf index is one key, and at two leaf indices is two keys.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Group {
    /// The leaf index.
    pub leaf_index: LeafIndex,
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
    /// The claims the guest verifies, one group per [`Group`], in their order (not canonical).
    pub set: SignerSet,
}

/// `n` signers, each with its own key, sign the message at the leaf index: one group.
pub fn batch(n: usize) -> Batch {
    batch_groups(&[Group {
        leaf_index: LEAF_INDEX,
        message: MESSAGE,
        signers: 0..n,
    }])
}

/// Each group's signers sign its message at its leaf index.
pub fn batch_groups(groups: &[Group]) -> Batch {
    // Every group's signers, one after the other; their keys and signatures are independent, so made in parallel.
    let jobs: Vec<(&Group, usize)> = (groups.iter())
        .flat_map(|g| g.signers.clone().map(move |i| (g, i)))
        .collect();
    let signed = parallel::map_collect(jobs.len(), |j| {
        let (g, i) = jobs[j];
        let (sk, pk) = leanxmss::key_gen(seed(i), g.leaf_index);
        (pk, sk.sign(&g.message).expect("a valid encoding"))
    });
    let mut signed = signed.iter();
    // What the guest reads: the number of groups, then for each its leaf index, message and count, then each key
    // and signature.
    let mut advice = vec![groups.len() as u64];
    let mut set = SignerSet::new();
    for g in groups {
        advice.push(g.leaf_index.into());
        advice.extend(g.message);
        advice.push(g.signers.len() as u64);
        let mut keys = Vec::with_capacity(g.signers.len());
        for (pk, signature) in signed.by_ref().take(g.signers.len()) {
            leanxmss::verify(pk, g.leaf_index, &g.message, signature).expect("honest signatures verify");
            advice.extend(words_of_key(pk));
            advice.extend(words_of_signature(signature));
            keys.push(*pk);
        }
        set.groups.push(XmssGroup {
            leaf_index: g.leaf_index,
            message: g.message,
            keys,
        });
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
    use leanvm::{Machine, Program, Trap};
    use leanxmss::XmssVerifyError::{InvalidEncoding, InvalidMerklePath};
    use leanxmss::signers::Stream;
    use leanxmss::{PublicKey, Signature};
    use primitives::hash::{digest_words, hash};

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
                hex(hash(&bytes(words_of_signature(&signature)))),
                sig_digest,
                "leaf index {leaf_index}"
            );
            assert_eq!(leanxmss::verify(&pk, leaf_index, &message, &signature), Ok(()));
        }
    }

    #[test]
    fn leanxmss_rejects_a_change_anywhere() {
        // Invariant: a verifier binds the claim and every part of the signature.
        //
        // Fixture state: one honest signature at leaf index 7.
        let (seed, message) = fixed();
        let (sk, pk) = leanxmss::key_gen(seed, 7);
        let signature = sk.sign(&message).unwrap();
        let verify = |pk: &PublicKey, leaf_index, message: &[u64; 4], signature: &Signature| {
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
    fn on_the_vm(run: &Run) -> Result<[u64; 4], Trap> {
        let program = Program::from_elf(ELF).expect("the guest's ELF file");
        Machine::new(program.rv(), &run.advice).run()
    }

    /// The words of a key and of a signature in the advice.
    const KEY: usize = size_of::<PublicKey>() / 8;
    const SIGNATURE: usize = size_of::<Signature>() / 8;

    /// The digest the guest's stream computes over the advice, read as the guest reads it, signatures unchecked.
    fn streamed(advice: &[u64]) -> [u64; 4] {
        let mut words = advice;
        let mut take = |n: usize| {
            let (head, tail) = words.split_at(n);
            words = tail;
            head
        };
        let mut signers = Stream::new();
        for _ in 0..take(1)[0] {
            let leaf_index = LeafIndex::try_from(take(1)[0]).expect("a leaf index below 2^32");
            signers.group(leaf_index, take(4).try_into().unwrap());
            for _ in 0..take(1)[0] {
                let k = take(KEY);
                signers.key(&PublicKey {
                    merkle_root: [k[0], k[1]],
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

    /// Groups at two leaf indices: two messages at one, overlapping signers, and an empty group.
    fn groups() -> [Group; 4] {
        let group = |leaf_index, message, signers| Group {
            leaf_index,
            message,
            signers,
        };
        [
            group(1234, message(1), 0..3),
            group(7, message(1), 1..3),
            group(1234, message(2), 2..5),
            group(7, message(3), 0..0),
        ]
    }

    #[test]
    fn leanxmss_outputs_the_digest_of_its_signer_set() {
        // Invariant: the guest commits one value, the digest of the signer set the host builds, which a stream over
        // the advice also computes.
        let outputs = |batch: &Batch| {
            let mut public = PublicValues::new();
            public.commit(&batch.set.digest());
            assert_eq!(batch.run.expected, public.digest(), "natively");
            assert_eq!(streamed(&batch.run.advice), batch.set.digest(), "streamed");
            assert_eq!(on_the_vm(&batch.run), Ok(batch.run.expected), "on the VM");
        };

        // One group, every count up to 5: keys are written two to a block, so none, odd and even counts.
        for n in 0..=5 {
            let batch = batch(n);
            assert_eq!(batch.set.groups.len(), 1);
            assert_eq!(batch.set.n_claims(), n);
            assert_eq!(batch.run.advice.len(), 1 + 6 + n * (KEY + SIGNATURE));
            outputs(&batch);
        }

        // Several groups, in the advice's order.
        let groups = groups();
        let batch = batch_groups(&groups);
        outputs(&batch);
        let set = &batch.set;
        assert_eq!(set.groups.len(), groups.len());
        for (g, group) in set.groups.iter().zip(&groups) {
            assert_eq!(
                (g.leaf_index, g.message, g.keys.len()),
                (group.leaf_index, group.message, group.signers.len())
            );
        }
        // Signer 2 at leaf index 1234 under two messages: one key in two groups.
        assert_eq!(set.groups[0].keys[2], set.groups[2].keys[0]);
        // Signer 1 at another leaf index: another key.
        assert_ne!(set.groups[0].keys[1], set.groups[1].keys[0]);
        // The set is not canonical (its groups are in the advice's order), and holds what its canonical form holds.
        assert!(set.check().is_err());
        assert_eq!(
            SignerSet::from_claims(set.claims()).n_claims(),
            set.n_claims(),
            "no claim repeats"
        );
    }

    #[test]
    fn the_guest_checks_what_the_native_code_checks() {
        let batch = batch_groups(&groups()[..3]);
        assert_eq!(on_the_vm(&batch.run), Ok(batch.run.expected));
        let forged = |at: usize, change: u64| {
            let mut run = batch.run.clone();
            run.advice[at] ^= change;
            on_the_vm(&run)
        };
        // Where the second group starts: after the count and the first group's header and 3 entries.
        let second = 1 + 6 + 3 * (KEY + SIGNATURE);

        // Mutation: the top bit of the advice's last word, a node of the last signature's path.
        //
        //     the guest's check fails → it panics → an illegal instruction → no output
        assert!(forged(batch.run.advice.len() - 1, 1 << 63).is_err());

        // Mutation: the second group's message, then a word of its first signature.
        //
        //     its signatures were made under another message, or are changed → they fail
        assert!(forged(second + 1, 1).is_err());
        assert!(forged(second + 6 + KEY, 1).is_err());

        // Mutation: the first group's leaf index with bit 32 set.
        //
        //     claimed leaf index   2^32 + 1234
        //     truncated            1234, which verifies
        //     → the guest refuses the word rather than verify at another leaf index than it publishes
        assert!(forged(1, 1 << 32).is_err());
    }
}
