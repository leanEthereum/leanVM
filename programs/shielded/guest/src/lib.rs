//! A shielded transfer: one spend of a privacy pool, two notes in and two notes out.
//!
//! The statement is soispoke's minimal shielded pool spend, BLAKE2s edition ([spec]).
//!
//! A note is a value owned by a secret key, public only as a commitment in a Merkle tree:
//!
//! ```text
//!   owner       = H(01 | spend_key)
//!   inner       = H(05 | owner | rho)
//!   commitment  = H(02 | inner | value)
//!   nullifier   = H(03 | H(06 | domain | spend_key) | H(07 | commitment | index))
//! ```
//!
//! The commitment is a leaf of the depth-20 tree under the root.
//!
//! Spending reveals each input's nullifier, never its commitment, so a note is spent once and unlinked.
//!
//! The spend proves:
//!
//! - each funded input is in the tree, and its nullifier is the one its key and position give;
//! - the values balance: `in_0 + in_1 = out_0 + out_1 + public_amount + fee`, with no wraparound;
//! - the outputs are well formed, and nothing repeats.
//!
//! Its output is the statement digest: `H(08 | nullifiers | output commitments | header)`.
//!
//! What stays on chain: the root's freshness, the domain, spent nullifiers, the authorizer's signature.
//!
//! Every value is a word array, its bytes in the specification's order: an integer is big-endian bytes.
//!
//! [spec]: https://github.com/soispoke/evm-spend-challenge/blob/main/SPEC.md
#![no_std]
use leanvm_guest::Words;
use message::Tag;
use thiserror::Error;

mod message;

/// The Merkle tree's depth: room for `2^20` notes.
pub const DEPTH: usize = 20;

/// A 32-byte value, its bytes in order.
pub type Hash = [u64; 4];

/// A `u128` amount, as its 16 big-endian bytes in order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Amount(pub [u64; 2]);

impl Amount {
    /// An amount of `value`.
    pub const fn new(value: u128) -> Self {
        // Big-endian bytes in order: the high half's bytes come first, each word byte-reversed.
        Self([((value >> 64) as u64).swap_bytes(), (value as u64).swap_bytes()])
    }

    /// The amount as an integer.
    pub const fn get(&self) -> u128 {
        (self.0[0].swap_bytes() as u128) << 64 | self.0[1].swap_bytes() as u128
    }
}

/// What the spend makes public: the input's first 136 bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Header {
    /// The Merkle root the inputs are proven under.
    pub root: Hash,
    /// The pool, chain and tree epoch the nullifiers are bound to.
    pub domain: Hash,
    /// The value leaving the pool, to the recipient.
    pub public_amount: Amount,
    /// The value paid to whoever settles the spend.
    pub fee: Amount,
    /// The recipient's 20-byte address, then the authorizer's.
    pub parties: [u64; 5],
}

impl Header {
    /// Whether the recipient, bytes 0 to 19 of the parties, is zero.
    const fn recipient_is_zero(&self) -> bool {
        // Bytes 16 to 19 are the low half of word 2.
        let [a, b, c, ..] = self.parties;
        a | b | (c & 0xFFFF_FFFF) == 0
    }

    /// Whether the authorizer, bytes 20 to 39 of the parties, is zero.
    const fn authorizer_is_zero(&self) -> bool {
        // Bytes 20 to 23 are the high half of word 2.
        let [.., c, d, e] = self.parties;
        (c >> 32) | d | e == 0
    }
}

/// A note being spent, and the private data that proves it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct InputNote {
    /// The secret its owner key and nullifier key come from.
    pub spend_key: Hash,
    /// The note's randomness, which hides its commitment.
    pub rho: Hash,
    /// Its value: zero makes it a dummy, in the tree or not.
    pub value: Amount,
    /// Its leaf index: bit `i` says whether it is the right child at level `i`.
    pub index: u64,
    /// The siblings on its path, the leaf's first.
    pub siblings: [Hash; DEPTH],
}

/// A note being created.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct OutputNote {
    /// Its inner part, which its recipient provides.
    pub inner: Hash,
    /// Its value.
    pub value: Amount,
}

/// A spend: its public header, two inputs and two outputs.
///
/// Its fields are words, so it has no padding and any 1,688 bytes are one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Spend {
    /// What it makes public.
    pub header: Header,
    /// The notes it spends.
    pub inputs: [InputNote; 2],
    /// The notes it creates.
    pub outputs: [OutputNote; 2],
}

// SAFETY: `repr(C)` words throughout, with no padding, and any words are a spend.
unsafe impl Words for Spend {}

/// The rule a spend breaks, numbered as the specification does.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum SpendError {
    /// An input's index is not below `2^20`.
    #[error("an input's index is not below 2^20")]
    IndexRange = 1,
    /// A funded input's path does not lead to the root.
    #[error("a funded input is not in the tree")]
    Membership = 2,
    /// Both inputs are empty.
    #[error("the inputs carry no value")]
    NonzeroInput = 3,
    /// The inputs are not the outputs, the public amount and the fee.
    #[error("the values do not balance")]
    Conservation = 4,
    /// An empty output's inner part is not its position's sink, 1 or 2.
    #[error("an empty output is not its sink")]
    ZeroOutputSink = 5,
    /// A funded output's inner part is a sink.
    #[error("a funded output is a sink")]
    PositiveOutputNotSink = 6,
    /// The authorizer is zero.
    #[error("no authorizer")]
    AuthorizerNonzero = 7,
    /// The recipient is zero but the public amount is not, or the reverse.
    #[error("the recipient does not match the public amount")]
    RecipientMatchesAmount = 8,
    /// The two nullifiers are equal.
    #[error("the nullifiers repeat")]
    DistinctNullifiers = 9,
    /// The two output commitments are equal.
    #[error("the output commitments repeat")]
    DistinctOutputs = 10,
}

/// The inner part an empty output in position `k` must have: `k + 1` as a 32-byte big-endian word.
const fn sink(k: usize) -> Hash {
    // The last byte of the 32 is the top byte of the last word.
    [0, 0, 0, ((k + 1) as u64) << 56]
}

/// A note commitment: `H(02 | inner | value)`, 49 bytes.
fn commitment(inner: &Hash, value: &Amount) -> Hash {
    Tag::Commitment.hash::<49>(|m| {
        m.words(*inner).words(value.0);
    })
}

impl InputNote {
    /// The note's nullifier, once its index is in range and, when it carries value, its path leads to `root`.
    fn nullifier(&self, root: &Hash, domain: &Hash) -> Result<Hash, SpendError> {
        // Only 20 bits steer the path: a larger index would reach the root with another nullifier.
        if self.index >= 1 << DEPTH {
            return Err(SpendError::IndexRange);
        }

        // The commitment, from the spend key and the randomness.
        let owner = Tag::Owner.hash::<33>(|m| {
            m.words(self.spend_key);
        });
        let inner = Tag::Inner.pair(&owner, &self.rho);
        let commitment = commitment(&inner, &self.value);

        // Up the tree: at level `i`, bit `i` of the index says which side the node is on.
        //
        //     bit 0:  parent = H(04 | node | sibling)
        //     bit 1:  parent = H(04 | sibling | node)
        //
        // A mask, not a branch, picks the order.
        let mut node = commitment;
        for (level, sibling) in self.siblings.iter().enumerate() {
            let right = 0u64.wrapping_sub((self.index >> level) & 1);
            let swap: Hash = core::array::from_fn(|k| (node[k] ^ sibling[k]) & right);
            let left: Hash = core::array::from_fn(|k| node[k] ^ swap[k]);
            let right: Hash = core::array::from_fn(|k| sibling[k] ^ swap[k]);
            node = Tag::Node.pair(&left, &right);
        }
        // A dummy, of value zero, need not be in the tree.
        if node != *root && self.value.get() != 0 {
            return Err(SpendError::Membership);
        }

        // The nullifier binds the key, the domain, the commitment and its position.
        //
        // The index is written as 4 big-endian bytes: its low 32 bits, byte-reversed.
        let occurrence = Tag::Occurrence.hash::<37>(|m| {
            m.words(commitment).tail(u64::from((self.index as u32).swap_bytes()));
        });
        let nullifier_key = Tag::NullifierKey.pair(domain, &self.spend_key);
        Ok(Tag::Nullifier.pair(&nullifier_key, &occurrence))
    }
}

impl OutputNote {
    /// The note's commitment, once it is well formed for position `k`.
    fn commitment(&self, k: usize) -> Result<Hash, SpendError> {
        // An empty output is a placeholder, its inner part fixed by its position; a funded one is never that.
        let empty = self.value.get() == 0;
        if empty && self.inner != sink(k) {
            return Err(SpendError::ZeroOutputSink);
        }
        if !empty && (self.inner == sink(0) || self.inner == sink(1)) {
            return Err(SpendError::PositiveOutputNotSink);
        }
        Ok(commitment(&self.inner, &self.value))
    }
}

impl Spend {
    /// Check every rule, in the specification's order, and return the statement digest.
    pub fn verify(&self) -> Result<Hash, SpendError> {
        let Header {
            root,
            domain,
            public_amount,
            fee,
            parties,
        } = &self.header;

        // The inputs, then the outputs.
        let [nf_0, nf_1] = [
            self.inputs[0].nullifier(root, domain)?,
            self.inputs[1].nullifier(root, domain)?,
        ];
        let [cm_0, cm_1] = [self.outputs[0].commitment(0)?, self.outputs[1].commitment(1)?];

        // Balance, exactly: two u128 inputs fit in 129 bits, four u128 outputs in 130.
        //
        // Each side is summed as its carries and its low 128 bits, then compared whole.
        let sum = |values: &[u128]| {
            values.iter().fold((0u32, 0u128), |(high, low), &v| {
                let (low, carry) = low.overflowing_add(v);
                (high + u32::from(carry), low)
            })
        };
        let inputs = sum(&[self.inputs[0].value.get(), self.inputs[1].value.get()]);
        let outputs = sum(&[
            self.outputs[0].value.get(),
            self.outputs[1].value.get(),
            public_amount.get(),
            fee.get(),
        ]);
        if inputs == (0, 0) {
            return Err(SpendError::NonzeroInput);
        }
        if inputs != outputs {
            return Err(SpendError::Conservation);
        }

        // The public parties: someone authorizes, and a recipient exactly when value leaves the pool.
        if self.header.authorizer_is_zero() {
            return Err(SpendError::AuthorizerNonzero);
        }
        if (public_amount.get() == 0) != self.header.recipient_is_zero() {
            return Err(SpendError::RecipientMatchesAmount);
        }

        // No note is spent twice in one spend, nor created twice.
        if nf_0 == nf_1 {
            return Err(SpendError::DistinctNullifiers);
        }
        if cm_0 == cm_1 {
            return Err(SpendError::DistinctOutputs);
        }

        // The statement: 265 bytes, five compressions; the header is the input's first 136 bytes.
        Ok(Tag::Statement.hash::<265>(|m| {
            m.words(nf_0).words(nf_1).words(cm_0).words(cm_1);
            m.words(*root)
                .words(*domain)
                .words(public_amount.0)
                .words(fee.0)
                .words(*parties);
        }))
    }
}
