//! Ethereum L1 state proofs, as `eth_getProof` ([EIP-1186]) gives them.
//!
//! A read is an account and one of its storage slots at a block.
//!
//! Every claim is anchored at the block hash:
//!
//! ```text
//!   block hash  = keccak256(header)                      the header's fourth field is the state root
//!   account     = state trie [keccak256(address)]        nonce, balance, storage root, code hash
//!   value       = storage trie [keccak256(slot)]         under the account's storage root, zero if absent
//! ```
//!
//! Values are 64-bit words, as the machine loads them:
//!
//! - bytes (a node, a hash, an address, a slot) are little-endian words, as keccak absorbs them;
//! - integers (a balance, a slot's value) are little-endian 64-bit limbs.
//!
//! [EIP-1186]: https://eips.ethereum.org/EIPS/eip-1186
#![no_std]
use leanvm_guest::Words;
use thiserror::Error;

mod keccak;
mod trie;

pub use keccak::keccak256;
pub use trie::{EMPTY_ROOT, Node};

/// A 32-byte hash, its bytes in order.
pub type Hash = [u64; 4];
/// A 256-bit integer, least significant limb first.
pub type U256 = [u64; 4];
/// A 20-byte address, its bytes in order, then four zero bytes.
pub type Address = [u64; 3];

/// Bytes in an address.
pub const ADDRESS_BYTES: usize = 20;

/// keccak256 of no bytes: the code hash of an account with no code.
pub const EMPTY_CODE_HASH: Hash = [
    0x3c23_f786_0146_d2c5,
    0xc003_c7dc_b27d_7e92,
    0x3b27_82ca_53b6_00e5,
    0x70a4_855d_04d8_fa7b,
];

/// An account, as the state trie holds it.
///
/// Its fields are words, so it has no padding and any 104 bytes are one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Account {
    /// Transactions sent, or contracts created.
    pub nonce: u64,
    /// Wei held.
    pub balance: U256,
    /// The root of the account's storage trie.
    pub storage_root: Hash,
    /// keccak256 of the account's code.
    pub code_hash: Hash,
}

impl Account {
    /// An account absent from the state: no balance, no storage, no code.
    pub const EMPTY: Self = Self {
        nonce: 0,
        balance: [0; 4],
        storage_root: EMPTY_ROOT,
        code_hash: EMPTY_CODE_HASH,
    };
}

// SAFETY: `repr(C)` words, with no padding, and any words are an account.
unsafe impl Words for Account {}

/// Why a proof is rejected.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum ProofError {
    /// A node's hash is not its parent's reference to it, or the root.
    #[error("a node's hash is not the reference to it")]
    Hash,
    /// A node, a value or the header is not the RLP Ethereum writes.
    #[error("not the RLP Ethereum writes")]
    Malformed,
    /// A node under 32 bytes, embedded in its parent.
    ///
    /// Ethereum's tries key by 32-byte hashes, so every node is longer and none is embedded.
    #[error("a node embedded in its parent")]
    InlineNode,
    /// The proof ends before the key's path does.
    #[error("the proof ends before the path does")]
    TooShort,
    /// The proof goes on past the key's path.
    #[error("the proof goes on past the path")]
    TooLong,
}

/// The state root a block header commits to.
///
/// The header is an RLP list: parent hash, ommers hash, beneficiary, state root, then the rest.
pub fn state_root(header: &Node<'_>) -> Result<Hash, ProofError> {
    // Skip three items, whatever their lengths: the fourth is the root.
    header.item()?.nth(3)?.hash()
}

/// The account at `address` under `state_root`.
///
/// An account the proof shows absent is the empty one: no nonce, no balance, no storage, no code.
pub fn account<'a>(
    state_root: &Hash,
    address: &Address,
    proof: impl IntoIterator<Item = Node<'a>>,
) -> Result<Account, ProofError> {
    // One address, one encoding: the bytes past the twentieth are zero.
    if address[2] >> 32 != 0 {
        return Err(ProofError::Malformed);
    }
    // The state trie keys an account by keccak256 of its 20 bytes.
    let key = keccak256(address, ADDRESS_BYTES);
    let Some(leaf) = trie::get(state_root, &key, proof)? else {
        return Ok(Account::EMPTY);
    };

    // The leaf's value is the account's RLP: [nonce, balance, storage root, code hash].
    let account = leaf.decode()?;
    // A nonce is 64 bits (EIP-2681).
    let nonce = account.nth(0)?.uint()?;
    if nonce[1..] != [0; 3] {
        return Err(ProofError::Malformed);
    }
    Ok(Account {
        nonce: nonce[0],
        balance: account.nth(1)?.uint()?,
        storage_root: account.nth(2)?.hash()?,
        code_hash: account.nth(3)?.hash()?,
    })
}

/// The value of storage slot `slot` under `storage_root`, zero if the proof shows it absent.
pub fn storage<'a>(
    storage_root: &Hash,
    slot: &Hash,
    proof: impl IntoIterator<Item = Node<'a>>,
) -> Result<U256, ProofError> {
    // The storage trie keys a slot by keccak256 of its 32 bytes.
    let key = keccak256(slot, 32);
    match trie::get(storage_root, &key, proof)? {
        // The leaf's value is the RLP of the integer.
        Some(leaf) => leaf.decode()?.uint(),
        // The trie stores no zero: an absent slot holds zero.
        None => Ok([0; 4]),
    }
}
