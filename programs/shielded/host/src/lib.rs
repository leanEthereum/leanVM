//! The shielded-transfer program off the VM.
//!
//! It makes spends in the specification's 1,680-byte input format.
//!
//! It lays them out as the guest's words, and checks them natively for the output the guest must give.
//!
//! Spends are deterministic: every secret is a BLAKE2s stream of the spend's index, so the advice never moves.
//!
//! Each spend's two inputs sit in one depth-20 tree that holds only them.
//! A fuller tree changes no hash count.
//!
//! The spends cycle through three shapes:
//!
//! - a private transfer: two notes in, two out, a fee;
//! - a withdrawal: value leaves the pool to a recipient, one output empty;
//! - a dummy input: one input of value zero, so the other alone is spent.

use leanvm_guest::{Blake2s, PublicValues, Run, as_words_unchecked};
use shielded::{Amount, DEPTH, Header, InputNote, OutputNote, Spend};
use std::collections::BTreeMap;

/// The guest (`../guest`), built by `programs/build.sh`.
pub const ELF: &[u8] = include_bytes!("../../shielded.elf");

/// Bytes in a spend's input.
const INPUT_BYTES: usize = 1680;

/// Bytes in an input note: spend key, rho, value, index, then the siblings.
const NOTE_BYTES: usize = 32 + 32 + 16 + 4 + 32 * DEPTH;
/// Where the input notes start: after the 136-byte header.
const NOTES_AT: usize = 136;
/// Where the outputs start.
const OUTPUTS_AT: usize = NOTES_AT + 2 * NOTE_BYTES;
/// Bytes in an output: inner, then value.
const OUTPUT_BYTES: usize = 48;

/// A spend in the specification's input format: big-endian integers, fixed offsets.
///
/// ```text
///   0     root, domain, public_amount, fee, recipient, authorizer     136 bytes
///   136   input note 0, then input note 1                             724 bytes each
///   1584  output 0, then output 1                                     48 bytes each
/// ```
#[derive(Clone, PartialEq, Eq)]
struct Input([u8; INPUT_BYTES]);

impl Input {
    /// The spend as the guest reads it.
    fn spend(&self) -> Spend {
        let input = &self.0;
        Spend {
            header: Header {
                root: words(&input[0..32]),
                domain: words(&input[32..64]),
                public_amount: Amount(words(&input[64..80])),
                fee: Amount(words(&input[80..96])),
                parties: words(&input[96..136]),
            },
            inputs: std::array::from_fn(|k| {
                let note = &input[NOTES_AT + k * NOTE_BYTES..][..NOTE_BYTES];
                InputNote {
                    spend_key: words(&note[0..32]),
                    rho: words(&note[32..64]),
                    value: Amount(words(&note[64..80])),
                    // The index is 4 big-endian bytes: the guest takes it as an integer.
                    index: u64::from(u32::from_be_bytes(note[80..84].try_into().unwrap())),
                    siblings: std::array::from_fn(|level| words(&note[84 + 32 * level..][..32])),
                }
            }),
            outputs: std::array::from_fn(|k| {
                let output = &input[OUTPUTS_AT + k * OUTPUT_BYTES..][..OUTPUT_BYTES];
                OutputNote {
                    inner: words(&output[0..32]),
                    value: Amount(words(&output[32..48])),
                }
            }),
        }
    }
}

/// `n` spends, the three shapes in turn.
pub fn spends(n: usize) -> Run {
    // What the guest reads: the count, then each spend's words.
    let mut advice = vec![n as u64];
    // What it commits: each spend's statement digest.
    let mut public = PublicValues::new();
    for i in 0..n {
        let spend = make(i).spend();
        let digest = spend.verify().expect("a spend made by the rules follows them");
        // SAFETY: a spend is `repr(C)` words, with no padding (see its definition).
        advice.extend(unsafe { as_words_unchecked(&spend) });
        public.commit(&digest);
    }
    Run {
        advice,
        expected: public.digest(),
    }
}

/// Spend `i`: shape `i % 3`, its secrets drawn from a stream of `i`.
fn make(i: usize) -> Input {
    let mut draw = Draw::new(i);

    // Two notes, each owned by its own key: values below 2^64, so every sum fits.
    let keys: [[u8; 32]; 2] = [draw.bytes(), draw.bytes()];
    let rhos: [[u8; 32]; 2] = [draw.bytes(), draw.bytes()];
    let mut values = [u128::from(draw.u64() >> 1), u128::from(draw.u64() >> 1)];
    // Two distinct leaves of the 2^20.
    let index_0 = draw.u64() as u32 % (1 << DEPTH);
    let index_1 = (index_0 + 1 + draw.u64() as u32 % ((1 << DEPTH) - 1)) % (1 << DEPTH);

    // The shape decides what leaves the pool, and which notes are empty.
    let shape = i % 3;
    if shape == 2 {
        values[1] = 0;
    }
    let total = values[0] + values[1];
    let fee = total / 1000;
    let public_amount = if shape == 1 { total / 2 } else { 0 };
    let out_0 = total - fee - public_amount;
    let outputs: [(u128, [u8; 32]); 2] = match shape {
        // The withdrawal's second output is empty: its inner part is its sink, 2.
        1 => [(out_0, draw.bytes()), (0, sink(1))],
        _ => [(out_0 - out_0 / 3, draw.bytes()), (out_0 / 3, draw.bytes())],
    };
    let recipient: [u8; 20] = if public_amount == 0 { [0; 20] } else { draw.bytes() };
    let authorizer: [u8; 20] = draw.bytes();
    let domain: [u8; 32] = draw.bytes();

    // Both inputs in one tree, whatever their values.
    let commitments = [0, 1].map(|k| note_commitment(&keys[k], &rhos[k], values[k]));
    let (root, paths) = tree([(index_0, commitments[0]), (index_1, commitments[1])]);

    // Laid out at the specification's offsets.
    let mut input = [0; INPUT_BYTES];
    let mut at = 0;
    let mut put = |bytes: &[u8]| {
        input[at..at + bytes.len()].copy_from_slice(bytes);
        at += bytes.len();
    };
    put(&root);
    put(&domain);
    put(&public_amount.to_be_bytes());
    put(&fee.to_be_bytes());
    put(&recipient);
    put(&authorizer);
    for (k, index) in [index_0, index_1].into_iter().enumerate() {
        put(&keys[k]);
        put(&rhos[k]);
        put(&values[k].to_be_bytes());
        put(&index.to_be_bytes());
        paths[k].iter().for_each(|sibling| put(sibling));
    }
    for (value, inner) in outputs {
        put(&inner);
        put(&value.to_be_bytes());
    }
    assert_eq!(at, INPUT_BYTES);
    Input(input)
}

/// BLAKE2s-256 of a tag byte, then the parts: every hash of the specification.
fn tagged(tag: u8, parts: &[&[u8]]) -> [u8; 32] {
    let mut hasher = Blake2s::new();
    hasher.update(&[tag]);
    parts.iter().for_each(|part| {
        hasher.update(part);
    });
    hasher.finalize()
}

/// A note's commitment, from its spend key, randomness and value.
fn note_commitment(spend_key: &[u8; 32], rho: &[u8; 32], value: u128) -> [u8; 32] {
    let owner = tagged(1, &[spend_key]);
    let inner = tagged(5, &[&owner, rho]);
    tagged(2, &[&inner, &value.to_be_bytes()])
}

/// The root of a depth-20 tree holding `leaves` and nothing else, and each leaf's siblings, the leaf's first.
///
/// An empty leaf is 32 zero bytes, and an empty subtree the hash of two empty ones.
fn tree(leaves: [(u32, [u8; 32]); 2]) -> ([u8; 32], [[[u8; 32]; DEPTH]; 2]) {
    let mut empty = [0; 32];
    // The nodes present at the current level, by position.
    let mut level: BTreeMap<u32, [u8; 32]> = leaves.into_iter().collect();
    // Each level's siblings of the two leaves' paths, the leaf level first.
    let mut siblings = Vec::with_capacity(DEPTH);
    for depth in 0..DEPTH {
        // A sibling is present, or an empty subtree.
        siblings.push(leaves.map(|(index, _)| *level.get(&((index >> depth) ^ 1)).unwrap_or(&empty)));
        // One level up: each parent from its two children.
        let parents: BTreeMap<u32, [u8; 32]> = (level.keys())
            .map(|&position| {
                let child = |p: u32| *level.get(&p).unwrap_or(&empty);
                let left = position & !1;
                (position >> 1, tagged(4, &[&child(left), &child(left | 1)]))
            })
            .collect();
        level = parents;
        empty = tagged(4, &[&empty, &empty]);
    }
    let paths = [0, 1].map(|k| std::array::from_fn(|depth| siblings[depth][k]));
    (level[&0], paths)
}

/// The inner part an empty output in position `k` must have: `k + 1` as a 32-byte big-endian word.
const fn sink(k: usize) -> [u8; 32] {
    let mut inner = [0; 32];
    inner[31] = k as u8 + 1;
    inner
}

/// Bytes as little-endian words, its bytes in order: at most `8 * W` of them, zero past their end.
fn words<const W: usize>(bytes: &[u8]) -> [u64; W] {
    assert!(bytes.len() <= 8 * W, "{} bytes do not fit {W} words", bytes.len());
    let mut padded = [0; 64 * 8];
    padded[..bytes.len()].copy_from_slice(bytes);
    std::array::from_fn(|k| u64::from_le_bytes(padded[8 * k..8 * k + 8].try_into().unwrap()))
}

/// A deterministic stream of bytes: BLAKE2s of a label, the spend's index and a counter.
struct Draw {
    /// The spend's index.
    spend: u64,
    /// Draws made so far.
    count: u64,
}

impl Draw {
    const fn new(spend: usize) -> Self {
        Self {
            spend: spend as u64,
            count: 0,
        }
    }

    /// The next `N` bytes, at most 32.
    fn bytes<const N: usize>(&mut self) -> [u8; N] {
        self.count += 1;
        let block = tagged(
            0xFF,
            &[b"shielded", &self.spend.to_le_bytes(), &self.count.to_le_bytes()],
        );
        block[..N].try_into().unwrap()
    }

    /// The next 64 bits.
    fn u64(&mut self) -> u64 {
        u64::from_le_bytes(self.bytes())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use leanvm::{Machine, Program, Trap};
    use proptest::prelude::*;
    use shielded::SpendError;

    /// The statement digest of a valid spend, from its bytes, as the specification writes it.
    fn reference(input: &Input) -> [u8; 32] {
        let bytes = &input.0;
        let domain = &bytes[32..64];

        // Each input's nullifier, bound to its key, the domain, its commitment and its index.
        let nullifiers = [0, 1].map(|k| {
            let note = &bytes[NOTES_AT + k * NOTE_BYTES..][..NOTE_BYTES];
            let (spend_key, rho) = (note[0..32].try_into().unwrap(), note[32..64].try_into().unwrap());
            let value = u128::from_be_bytes(note[64..80].try_into().unwrap());
            let commitment = note_commitment(spend_key, rho, value);
            let occurrence = tagged(7, &[&commitment, &note[80..84]]);
            let nullifier_key = tagged(6, &[domain, spend_key]);
            tagged(3, &[&nullifier_key, &occurrence])
        });

        // Each output's commitment, from its inner part and value as they stand.
        let commitments = [0, 1].map(|k| {
            let output = &bytes[OUTPUTS_AT + k * OUTPUT_BYTES..][..OUTPUT_BYTES];
            tagged(2, &[&output[0..32], &output[32..48]])
        });

        // The statement: the nullifiers, the commitments, then the header's 136 bytes.
        let [nf_0, nf_1] = &nullifiers;
        let [cm_0, cm_1] = &commitments;
        tagged(8, &[nf_0, nf_1, cm_0, cm_1, &bytes[..NOTES_AT]])
    }

    /// Little-endian words as their bytes.
    fn bytes(words: &[u64]) -> Vec<u8> {
        words.iter().flat_map(|w| w.to_le_bytes()).collect()
    }

    proptest! {
        #[test]
        fn a_spend_is_its_statement_from_the_bytes(i in 0..1_000_000usize) {
            // Invariant: the guest's word-level digest is the byte-level reference's, for every shape.
            //
            // The guest builds each message a word at a time, one byte off the tag.
            // The reference hashes the specification's byte strings as they are.
            let input = make(i);
            let digest = input.spend().verify();
            prop_assert_eq!(digest.map(|d| bytes(&d)), Ok(reference(&input).to_vec()));
        }
    }

    #[test]
    fn each_rule_refuses_the_spend_that_breaks_it() {
        // Fixture: one spend of each shape, all valid.
        let [transfer, withdrawal, dummy] = [0, 1, 2].map(|i| make(i).spend());
        for spend in [&transfer, &withdrawal, &dummy] {
            assert!(spend.verify().is_ok());
        }
        let refuses = |spend: &Spend, rule: SpendError| assert_eq!(spend.verify(), Err(rule), "{rule}");

        // Rule 1. Mutation: bit 20 of an index.
        //
        //     bits 0..20 still steer the path to the root → only the range check stops a second nullifier
        let mut spend = transfer;
        spend.inputs[0].index |= 1 << DEPTH;
        refuses(&spend, SpendError::IndexRange);

        // Rule 2. Mutation: one bit of a funded input's sibling.
        let mut spend = transfer;
        spend.inputs[1].siblings[DEPTH - 1][0] ^= 1;
        refuses(&spend, SpendError::Membership);

        // Rule 2, the other way. Mutation: the same bit of a dummy input's sibling.
        //
        //     value zero → no path is checked → and the siblings are not in the statement
        let mut spend = dummy;
        spend.inputs[1].siblings[DEPTH - 1][0] ^= 1;
        assert_eq!(spend.verify(), dummy.verify());

        // Rule 3. Mutation: both inputs emptied.
        let mut spend = transfer;
        spend.inputs.iter_mut().for_each(|note| note.value = Amount::new(0));
        refuses(&spend, SpendError::NonzeroInput);

        // Rule 4. Mutation: one more unit of fee.
        let mut spend = transfer;
        spend.header.fee = Amount::new(spend.header.fee.get() + 1);
        refuses(&spend, SpendError::Conservation);

        // Rule 4, with no wraparound. Mutation: 2^127 more in an output and in the fee.
        //
        //     outputs grow by 2^128 → equal to the inputs mod 2^128 → but not as integers
        let mut spend = transfer;
        spend.outputs[0].value = Amount::new(spend.outputs[0].value.get() + (1 << 127));
        spend.header.fee = Amount::new(spend.header.fee.get() + (1 << 127));
        refuses(&spend, SpendError::Conservation);

        // Rule 5. Mutation: the empty output's inner part, the other position's sink.
        let mut spend = withdrawal;
        spend.outputs[1].inner = spend.outputs[1].inner.map(|w| w >> 1);
        refuses(&spend, SpendError::ZeroOutputSink);

        // Rule 6. Mutation: a funded output's inner part, a sink.
        let mut spend = transfer;
        spend.outputs[0].inner = withdrawal.outputs[1].inner;
        refuses(&spend, SpendError::PositiveOutputNotSink);

        // Rule 7. Mutation: the authorizer zeroed, the top half of parties word 2 and words 3 and 4.
        let mut spend = transfer;
        let parties = &mut spend.header.parties;
        (parties[2], parties[3], parties[4]) = (parties[2] & 0xFFFF_FFFF, 0, 0);
        refuses(&spend, SpendError::AuthorizerNonzero);

        // Rule 8. Mutation: a recipient for a transfer, which makes nothing public.
        let mut spend = transfer;
        spend.header.parties[0] = 1;
        refuses(&spend, SpendError::RecipientMatchesAmount);

        // Rule 9. Mutation: the larger input spent twice, the fee taking the difference.
        //
        //     same note, same index → same nullifier
        let mut spend = transfer;
        let [big, small] = if spend.inputs[0].value.get() >= spend.inputs[1].value.get() {
            [0, 1]
        } else {
            [1, 0]
        };
        let extra = spend.inputs[big].value.get() - spend.inputs[small].value.get();
        spend.inputs[small] = spend.inputs[big];
        spend.header.fee = Amount::new(spend.header.fee.get() + extra);
        refuses(&spend, SpendError::DistinctNullifiers);

        // Rule 10. Mutation: the second output made the first, the fee taking the difference.
        let mut spend = transfer;
        let extra = spend.outputs[0].value.get() - spend.outputs[1].value.get();
        spend.outputs[0] = spend.outputs[1];
        spend.header.fee = Amount::new(spend.header.fee.get() + extra);
        refuses(&spend, SpendError::DistinctOutputs);
    }

    /// The guest on the interpreter, with no proof: its output, or the trap.
    fn on_the_vm(run: &Run) -> Result<[u64; 4], Trap> {
        let program = Program::from_elf(ELF).expect("the guest's ELF file");
        // The interpreter alone: the output the run commits, without proving it.
        Machine::new(program.rv(), &run.advice).run()
    }

    #[test]
    fn the_guest_outputs_the_digest_of_its_statements() {
        // Invariant: the guest commits what the host does, for no spend, one, and every shape.
        for n in [0, 1, 3] {
            let run = spends(n);
            assert_eq!(on_the_vm(&run), Ok(run.expected), "{n} spends");
        }

        // Mutation: one bit of the first spend's last sibling, a funded input's.
        //
        // The advice is the count, then the spend's words.
        // The first input's siblings follow the header, the spend key, rho, the value and the index.
        //
        //     its path misses the root → the guest panics → an illegal instruction → no output
        let mut run = spends(1);
        run.advice[1 + 17 + 4 + 4 + 2 + 1 + 4 * (DEPTH - 1)] ^= 1;
        assert!(on_the_vm(&run).is_err());
    }
}
