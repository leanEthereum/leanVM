//! The L1 state-proof program off the VM.
//!
//! It lays mainnet `eth_getProof` responses out as the guest's advice.
//!
//! It verifies them natively, for the output the guest must give.
//!
//! The fixture (`fixture/mainnet.json`, made by `fixture/fetch.py`) is one finalized mainnet block:
//!
//! - its header, RLP-encoded;
//! - `eth_getProof` of slot 0 for 32 accounts at it: tokens, protocol contracts, system contracts, an EOA.
//!
//! The reads cover what a proof meets on mainnet: a slot present or absent, an empty storage trie, a one-node one.
//!
//! The proofs are real, so the cycles are what a mainnet read costs.

use leanvm_guest::PublicValues;
use serde::Deserialize;
use stateproof::{Address, Hash, Node};

/// The guest (`../guest`), built by `programs/build.sh`.
pub const ELF: &[u8] = include_bytes!("../../stateproof.elf");

/// What one run of the guest is given, and what it must output.
pub struct Run {
    /// The words the guest reads.
    pub advice: Vec<u64>,
    /// The digest of the claims the guest must commit.
    pub expected: [u64; 4],
}

/// The fixture, as `fetch.py` writes it.
const FIXTURE: &str = include_str!("../fixture/mainnet.json");

/// A block's header, and `eth_getProof` responses at it.
#[derive(Deserialize)]
struct Fixture {
    /// The header's RLP, hex.
    header: String,
    /// One response per account.
    proofs: Vec<GetProof>,
}

/// An `eth_getProof` response, the fields a read needs.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct GetProof {
    /// The account's address, hex.
    address: String,
    /// The state trie's nodes on the account's path, root first, hex.
    account_proof: Vec<String>,
    /// The one slot asked for.
    storage_proof: [StorageProof; 1],
}

/// One slot of an `eth_getProof` response.
#[derive(Deserialize)]
struct StorageProof {
    /// The slot, 32 bytes, hex.
    key: String,
    /// The storage trie's nodes on the slot's path, root first, hex.
    proof: Vec<String>,
}

/// A byte string as the guest reads it: its length, and its bytes as little-endian words.
#[derive(Clone)]
struct Bytes {
    /// The length in bytes.
    len: usize,
    /// The bytes, eight to a word, zero past the end.
    words: Vec<u64>,
}

impl Bytes {
    /// The bytes of a `0x`-prefixed hex string.
    fn from_hex(hex: &str) -> Self {
        let bytes = decode_hex(hex);
        Self {
            len: bytes.len(),
            words: words(&bytes),
        }
    }

    /// The bytes as the guest's library takes them.
    fn node(&self) -> Node<'_> {
        Node::new(&self.words, self.len).expect("the words hold the bytes")
    }

    /// Append the length, then the words.
    fn write(&self, advice: &mut Vec<u64>) {
        advice.push(self.len as u64);
        advice.extend(&self.words);
    }
}

/// One read: an account, a slot, and their proofs.
struct Read {
    /// The account's address.
    address: Address,
    /// The slot read.
    slot: Hash,
    /// The state trie's nodes on the account's path.
    account_proof: Vec<Bytes>,
    /// The storage trie's nodes on the slot's path.
    storage_proof: Vec<Bytes>,
}

impl Read {
    /// A read from its `eth_getProof` response.
    fn of(response: &GetProof) -> Self {
        let [storage] = &response.storage_proof;
        // Hex strings become the guest's words: bytes in order, eight to a word.
        Self {
            address: word_array(&decode_hex(&response.address)),
            slot: word_array(&decode_hex(&storage.key)),
            account_proof: response.account_proof.iter().map(|n| Bytes::from_hex(n)).collect(),
            storage_proof: storage.proof.iter().map(|n| Bytes::from_hex(n)).collect(),
        }
    }

    /// Append the address, the slot, then each proof: its node count and its nodes.
    fn write(&self, advice: &mut Vec<u64>) {
        advice.extend(self.address);
        advice.extend(self.slot);
        for proof in [&self.account_proof, &self.storage_proof] {
            advice.push(proof.len() as u64);
            proof.iter().for_each(|node| node.write(advice));
        }
    }
}

/// The block's header and its reads, from the fixture.
fn fixture() -> (Bytes, Vec<Read>) {
    let fixture: Fixture = serde_json::from_str(FIXTURE).expect("the fixture is JSON");
    (
        Bytes::from_hex(&fixture.header),
        fixture.proofs.iter().map(Read::of).collect(),
    )
}

/// `n` reads of the fixture's block, its 32 accounts in turn.
pub fn reads(n: usize) -> Run {
    let (header, reads) = fixture();
    let state_root = stateproof::state_root(&header.node()).expect("a mainnet header");
    // What the guest reads: the header, the count, then each read.
    let mut advice = Vec::new();
    header.write(&mut advice);
    advice.push(n as u64);
    // What it commits: the block hash, then each read's claim.
    let mut public = PublicValues::new();
    public.commit(&header.node().hash());
    // Past 32 reads the accounts come round again.
    for read in reads.iter().cycle().take(n) {
        // The claim, from the guest's own library run natively.
        let account = stateproof::account(&state_root, &read.address, read.account_proof.iter().map(Bytes::node))
            .expect("a mainnet account proof");
        let value = stateproof::storage(
            &account.storage_root,
            &read.slot,
            read.storage_proof.iter().map(Bytes::node),
        )
        .expect("a mainnet storage proof");
        read.write(&mut advice);
        public
            .commit(&read.address)
            .commit(&account)
            .commit(&read.slot)
            .commit(&value);
    }
    Run {
        advice,
        expected: public.digest(),
    }
}

/// The bytes of a `0x`-prefixed hex string.
fn decode_hex(hex: &str) -> Vec<u8> {
    let digits = hex.strip_prefix("0x").expect("a 0x-prefixed hex string").as_bytes();
    assert!(digits.len().is_multiple_of(2), "whole bytes");
    // Two hex digits to a byte.
    digits
        .chunks(2)
        .map(|pair| u8::from_str_radix(str::from_utf8(pair).expect("ASCII"), 16).expect("hex digits"))
        .collect()
}

/// Bytes as little-endian words, zero past their end.
fn words(bytes: &[u8]) -> Vec<u64> {
    // A last chunk under eight bytes is padded with zeros.
    bytes
        .chunks(8)
        .map(|chunk| {
            let mut word = [0; 8];
            word[..chunk.len()].copy_from_slice(chunk);
            u64::from_le_bytes(word)
        })
        .collect()
}

/// At most `8 * W` bytes as `W` little-endian words: a hash, a slot, an address.
fn word_array<const W: usize>(bytes: &[u8]) -> [u64; W] {
    assert!(bytes.len() <= 8 * W, "{} bytes do not fit {W} words", bytes.len());
    // The words the bytes fill, then zeros: an address's 20 bytes fill 3 words, the last half empty.
    let mut array = [0; W];
    array[..bytes.len().div_ceil(8)].copy_from_slice(&words(bytes));
    array
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy_primitives::{B256, keccak256};
    use alloy_trie::proof::ProofRetainer;
    use alloy_trie::{HashBuilder, Nibbles};
    use leanvm_core::cpu::Program;
    use leanvm_core::rv::{Machine, Trap};
    use proptest::prelude::*;
    use serde_json::Value;
    use stateproof::{Account, EMPTY_CODE_HASH, EMPTY_ROOT, ProofError};
    use std::collections::BTreeMap;

    /// Words as their little-endian bytes.
    fn bytes(words: &[u64]) -> Vec<u8> {
        words.iter().flat_map(|w| w.to_le_bytes()).collect()
    }

    /// A `0x`-prefixed quantity of at most 256 bits, as little-endian limbs.
    fn quantity(hex: &str) -> [u64; 4] {
        let digits = hex.strip_prefix("0x").expect("0x-prefixed");
        // Left-pad to 64 digits, then limb i is the 16 digits ending 16 i from the right.
        //
        //     0x1a  → 00..001a → limbs [0x1a, 0, 0, 0]
        let padded = format!("{digits:0>64}");
        std::array::from_fn(|i| u64::from_str_radix(&padded[64 - 16 * (i + 1)..64 - 16 * i], 16).unwrap())
    }

    /// A 32-byte hash from hex, its bytes in order.
    fn hash(hex: &str) -> Hash {
        word_array(&decode_hex(hex))
    }

    #[test]
    fn the_fixture_is_what_mainnet_answered() {
        // Fixture: the header and the responses, and what the node reported for each.
        let fixture: Value = serde_json::from_str(FIXTURE).unwrap();
        let (header, reads) = super::fixture();

        // The header is the block's: its keccak256 is the block hash the node reported.
        assert_eq!(header.node().hash(), hash(fixture["hash"].as_str().unwrap()));
        let state_root = stateproof::state_root(&header.node()).unwrap();

        // Invariant: each read verifies, to the account and the value the node reported.
        for (read, response) in reads.iter().zip(fixture["proofs"].as_array().unwrap()) {
            let field = |name: &str| response[name].as_str().unwrap();
            let account = stateproof::account(&state_root, &read.address, read.account_proof.iter().map(Bytes::node));
            let expected = Account {
                nonce: quantity(field("nonce"))[0],
                balance: quantity(field("balance")),
                storage_root: hash(field("storageHash")),
                code_hash: hash(field("codeHash")),
            };
            assert_eq!(account, Ok(expected), "{}", field("address"));

            let value = stateproof::storage(
                &expected.storage_root,
                &read.slot,
                read.storage_proof.iter().map(Bytes::node),
            );
            let reported = response["storageProof"][0]["value"].as_str().unwrap();
            assert_eq!(value, Ok(quantity(reported)), "{}", field("address"));
        }
    }

    #[test]
    fn a_proof_is_refused_unless_it_is_exactly_the_path() {
        // Fixture: WETH, a full account proof of mainnet depth.
        let (header, reads) = super::fixture();
        let state_root = stateproof::state_root(&header.node()).unwrap();
        let read = &reads[0];
        let account = |proof: &[Bytes]| stateproof::account(&state_root, &read.address, proof.iter().map(Bytes::node));
        assert!(account(&read.account_proof).is_ok());

        // Mutation: one bit of each node in turn.
        //
        //     the node's hash moves → its parent's reference, or the root, no longer names it
        for i in 0..read.account_proof.len() {
            let mut proof = read.account_proof.clone();
            proof[i].words[0] ^= 1 << 40;
            assert_eq!(account(&proof), Err(ProofError::Hash), "node {i}");
        }

        // Mutation: the last node dropped, then a node appended.
        let (path, last) = read.account_proof.split_at(read.account_proof.len() - 1);
        assert_eq!(account(path), Err(ProofError::TooShort));
        let longer = [read.account_proof.as_slice(), last].concat();
        assert_eq!(account(&longer), Err(ProofError::TooLong));

        // Mutation: another account's address, with this account's proof.
        //
        //     its key leaves the path at some branch → that child's node is not the next one
        let other = stateproof::account(
            &state_root,
            &reads[1].address,
            read.account_proof.iter().map(Bytes::node),
        );
        assert_eq!(other, Err(ProofError::Hash));

        // Mutation: a nonzero byte past the address's twentieth.
        let mut address = read.address;
        address[2] |= 1 << 32;
        let padded = stateproof::account(&state_root, &address, read.account_proof.iter().map(Bytes::node));
        assert_eq!(padded, Err(ProofError::Malformed));
    }

    #[test]
    fn the_constants_are_their_hashes() {
        // The empty trie's root is keccak256(rlp("")) = keccak256(0x80).
        // No code hashes to keccak256("").
        assert_eq!(bytes(&EMPTY_ROOT), keccak256([0x80]).to_vec());
        assert_eq!(bytes(&EMPTY_CODE_HASH), keccak256([]).to_vec());
    }

    /// The RLP of an integer: its big-endian bytes without leading zeros, as a string.
    fn rlp_uint(value: &[u64; 4]) -> Vec<u8> {
        // Most significant limb first, each big-endian, leading zero bytes dropped.
        let be: Vec<u8> = value
            .iter()
            .rev()
            .flat_map(|limb| limb.to_be_bytes())
            .skip_while(|&b| b == 0)
            .collect();
        // A byte below 0x80 is its own encoding.
        // Anything else takes a length prefix.
        match be.as_slice() {
            [b] if *b < 0x80 => be,
            _ => [&[0x80 + be.len() as u8], be.as_slice()].concat(),
        }
    }

    /// A slot whose key shares its first three nibbles with `slot`'s, found by search.
    ///
    /// Two keys alone under a branch and sharing a nibble put an extension node between them and the branch.
    fn twin(slot: &[u8; 32]) -> [u8; 32] {
        // The key's first three nibbles: the top 12 bits of its first two bytes.
        let prefix = |s: &[u8; 32]| u16::from_be_bytes(keccak256(s)[..2].try_into().unwrap()) >> 4;
        // Rewrite the slot's first four bytes with a counter until the prefixes agree: about 4096 tries.
        (0u32..)
            .map(|i| {
                let mut s = *slot;
                s[..4].copy_from_slice(&i.to_le_bytes());
                s
            })
            .find(|s| s != slot && prefix(s) == prefix(slot))
            .unwrap()
    }

    proptest! {
        #[test]
        fn keccak256_matches_a_reference(message in prop::collection::vec(any::<u8>(), 0..300), junk in any::<u64>()) {
            // Up to 300 bytes: absorbing crosses the 136-byte rate twice, at every alignment of the end.
            //
            // The last word's bytes past the message are junk: the hash must not see them.
            let mut words = words(&message);
            if message.len() % 8 != 0 {
                *words.last_mut().unwrap() |= junk << (8 * (message.len() % 8));
            }
            let ours = stateproof::keccak256(&words, message.len());
            prop_assert_eq!(bytes(&ours), keccak256(&message).to_vec());
        }

        #[test]
        fn storage_proofs_match_alloy_trie(
            storage in prop::collection::btree_map(
                any::<[u8; 32]>(),
                any::<[u64; 4]>().prop_filter("the trie stores no zero", |v| *v != [0; 4]),
                0..24,
            ),
            twins in any::<bool>(),
            absent in any::<[u8; 32]>(),
            pick in any::<prop::sample::Index>(),
        ) {
            // Fixture: a storage trie of random slots, half the time with two twins, so extension nodes appear.
            let mut storage = storage;
            if twins {
                for (slot, value) in storage.clone().into_iter().take(2) {
                    storage.insert(twin(&slot), value);
                }
            }

            // The slot proven: one present, or one absent.
            let slot = if storage.is_empty() || pick.index(2) == 0 {
                absent
            } else {
                *storage.keys().nth(pick.index(storage.len())).unwrap()
            };

            // The reference: alloy-trie's root and proof.
            //
            //     leaf key    keccak256(slot)
            //     leaf value  RLP of the slot's value, as Ethereum stores it
            let leaves: BTreeMap<B256, Vec<u8>> = storage.iter().map(|(s, v)| (keccak256(s), rlp_uint(v))).collect();
            let target = Nibbles::unpack(keccak256(slot));
            let mut builder = HashBuilder::default().with_proof_retainer(ProofRetainer::new(vec![target]));
            for (key, leaf) in &leaves {
                builder.add_leaf(Nibbles::unpack(key), leaf);
            }
            let root = builder.root();
            let proof: Vec<Bytes> = builder
                .take_proof_nodes()
                .matching_nodes_sorted(&target)
                .into_iter()
                .map(|(_, node)| Bytes { len: node.len(), words: words(&node) })
                .collect();

            // Invariant: the value proven is the slot's, or zero for an absent one.
            let (root, slot_words) = (word_array(root.as_slice()), word_array(&slot));
            let ours = stateproof::storage(&root, &slot_words, proof.iter().map(Bytes::node));
            prop_assert_eq!(ours, Ok(storage.get(&slot).copied().unwrap_or([0; 4])));
        }
    }

    /// The guest on the interpreter, with no proof: its output, or the trap.
    fn on_the_vm(run: &Run) -> Result<[u64; 4], Trap> {
        let program = Program::from_elf(ELF).expect("the guest's ELF file");
        // The interpreter alone: the output the run commits, without proving it.
        Machine::new(program.rv(), &run.advice).run()
    }

    #[test]
    fn the_guest_outputs_the_digest_of_its_claims() {
        // Invariant: the guest commits what the host does, for no read, one, and past the fixture's 32.
        for n in [0, 1, 33] {
            let run = reads(n);
            assert_eq!(on_the_vm(&run), Ok(run.expected), "{n} reads");
        }

        // Mutation: one bit of the header's last word.
        //
        //     the header still parses → but the guest commits another block hash → another output
        //
        //     advice  [len | header words ...]   the header's last word is word `header_words`
        let mut run = reads(1);
        let header_words = (run.advice[0] as usize).div_ceil(8);
        run.advice[header_words] ^= 1;
        assert_ne!(on_the_vm(&run), Ok(run.expected));

        // Mutation: one bit of the first account proof's root node.
        //
        //     its hash is not the state root → the guest panics → an illegal instruction → no output
        //
        //     advice  [len | header words | n | address 3 | slot 4 | nodes | len | root node ...]
        let mut run = reads(1);
        let root_node = 1 + header_words + 1 + 3 + 4 + 1 + 1;
        run.advice[root_node] ^= 1 << 40;
        assert!(on_the_vm(&run).is_err());
    }
}
