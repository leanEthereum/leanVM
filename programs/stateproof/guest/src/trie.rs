//! Ethereum's Merkle-Patricia trie: a proof of one key's value, or of its absence, under a root.
//!
//! A proof is the nodes on the key's path, root first, each the RLP encoding the trie hashes.
//!
//! A node is one of three lists:
//!
//! ```text
//!   branch     [child_0, ..., child_15, value]   child_i the reference for the next nibble i
//!   extension  [path, child]                     path a run of nibbles all keys below share
//!   leaf       [path, value]                     path the rest of the key
//! ```
//!
//! A reference is the keccak256 of the node it names, or the empty string for no node.
//!
//! The walk reads only the bytes it needs: the node's hash binds the rest.

use crate::keccak::keccak256;
use crate::{Hash, ProofError};

/// The root of the empty trie: keccak256 of the empty string's RLP, `0x80`.
pub const EMPTY_ROOT: Hash = [
    0xa655_cc1b_171f_e856,
    0x6ef8_c092_e645_83ff,
    0xc0ad_6c99_1be0_485b,
    0x21b4_63e3_b52f_6201,
];

/// Nibbles in a key: Ethereum keys its tries by 32-byte hashes.
const KEY_NIBBLES: usize = 64;

/// A byte string, as the words that hold it: the advice's form of a node or a header.
#[derive(Clone, Copy, Debug)]
pub struct Node<'a> {
    /// The bytes, little-endian: each word is the next eight bytes.
    words: &'a [u64],
    /// The length in bytes.
    len: usize,
}

impl<'a> Node<'a> {
    /// The first `len` bytes of `words`, or `None` if they hold fewer.
    pub const fn new(words: &'a [u64], len: usize) -> Option<Self> {
        // Every byte read later must sit in a word: refuse a length past the last one.
        if len <= 8 * words.len() {
            Some(Self { words, len })
        } else {
            None
        }
    }

    /// keccak256 of the bytes: the reference a parent holds to this node.
    pub fn hash(&self) -> Hash {
        keccak256(self.words, self.len)
    }

    /// The RLP item the bytes are, which must be all of them.
    pub(crate) fn item(&self) -> Result<Item<'a>, ProofError> {
        // View the whole node as one string, then decode its payload as a single item.
        let bytes = Item {
            words: self.words,
            start: 0,
            end: self.len,
            list: false,
        };
        bytes.decode()
    }
}

/// An RLP item: its payload, a window of a node's bytes, and whether it is a list.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Item<'a> {
    /// The node's bytes.
    words: &'a [u64],
    /// The payload's first byte.
    start: usize,
    /// One past its last byte.
    end: usize,
    /// A list, or a string.
    list: bool,
}

impl<'a> Item<'a> {
    /// The payload's length in bytes.
    pub(crate) const fn len(&self) -> usize {
        self.end - self.start
    }

    /// Byte `i` of the payload.
    const fn byte(&self, i: usize) -> Result<u8, ProofError> {
        // A read past the payload is a malformed length, never a read of the next item.
        if i >= self.len() {
            return Err(ProofError::Malformed);
        }
        // Byte `at` is byte `at % 8` of word `at / 8`, the lowest first.
        let at = self.start + i;
        Ok((self.words[at / 8] >> (8 * (at % 8))) as u8)
    }

    /// The first item of this list.
    pub(crate) fn first(&self) -> Result<Self, ProofError> {
        // A string's payload is bytes, not items.
        if !self.list {
            return Err(ProofError::Malformed);
        }
        self.item_at(self.start)
    }

    /// This string's payload, read as one RLP item: a leaf's value is itself an encoding.
    pub(crate) fn decode(&self) -> Result<Self, ProofError> {
        // The inner item must fill the payload exactly.
        //
        //     string  0xb8 0x46 | 0xf8 0x44 [nonce, balance, root, code]
        //                         ^ inner item, 70 bytes = the whole payload
        let item = self.item_at(self.start)?;
        if self.list || item.end != self.end {
            return Err(ProofError::Malformed);
        }
        Ok(item)
    }

    /// The item whose encoding starts at absolute byte `at`, which must end inside this payload.
    ///
    /// ```text
    ///   0x00..=0x7f   the byte itself, a string of one
    ///   0x80..=0xb7   a string of up to 55 bytes, its length the byte less 0x80
    ///   0xb8..=0xbf   a longer string, its length in the next (byte less 0xb7) bytes, big-endian
    ///   0xc0..=0xf7   a list of up to 55 bytes, as for strings
    ///   0xf8..=0xff   a longer list
    /// ```
    fn item_at(&self, at: usize) -> Result<Self, ProofError> {
        // The prefix byte says the kind and how the length is written.
        let prefix = self.byte(at - self.start)?;
        let (start, len, list) = match prefix {
            0x00..=0x7f => (at, 1, false),
            0x80..=0xb7 => (at + 1, usize::from(prefix - 0x80), false),
            0xc0..=0xf7 => (at + 1, usize::from(prefix - 0xc0), true),
            0xb8..=0xbf | 0xf8..=0xff => {
                let list = prefix >= 0xf8;
                // A length of one to three bytes: no node or header reaches 16 MiB.
                let n = usize::from(prefix - if list { 0xf7 } else { 0xb7 });
                if n > 3 {
                    return Err(ProofError::Malformed);
                }
                // The length's bytes, big-endian.
                //
                //     0xf9 0x02 0x11  → a list of 0x0211 = 529 bytes, a full branch
                let mut len = 0;
                for k in 1..=n {
                    len = len << 8 | usize::from(self.byte(at + k - self.start)?);
                }
                (at + 1 + n, len, list)
            }
        };
        // An item spilling past its parent is a malformed length.
        let end = start + len;
        if end > self.end {
            return Err(ProofError::Malformed);
        }
        Ok(Self {
            words: self.words,
            start,
            end,
            list,
        })
    }

    /// The `i`-th item of this list.
    pub(crate) fn nth(&self, i: usize) -> Result<Self, ProofError> {
        // Items have no index: skip each one by its encoded length.
        let mut item = self.first()?;
        for _ in 0..i {
            item = self.item_at(item.end)?;
        }
        Ok(item)
    }

    /// The payload as a 32-byte hash.
    pub(crate) fn hash(&self) -> Result<Hash, ProofError> {
        // A hash is a string of exactly 32 bytes, prefix 0xa0.
        if self.list || self.len() != 32 {
            return Err(ProofError::Malformed);
        }
        // Four words, at whatever alignment the payload starts.
        Ok(core::array::from_fn(|k| self.word(8 * k)))
    }

    /// Eight bytes of the payload from byte `i`, little-endian, at any alignment.
    ///
    /// A misaligned load traps on the VM, so a word across two is two loads and a funnel shift:
    ///
    /// ```text
    ///   words      | w0 . . . . . . . | w1 . . . . . . . |
    ///   at % 8 = r             |<- 8 bytes ->|
    ///   result     (w0 >> 8r) | (w1 << (64 - 8r))
    /// ```
    const fn word(&self, i: usize) -> u64 {
        let at = self.start + i;
        let (q, r) = (at / 8, at % 8);
        // Aligned: one word, and a shift by 64 would overflow.
        if r == 0 {
            self.words[q]
        } else {
            (self.words[q] >> (8 * r)) | (self.words[q + 1] << (64 - 8 * r))
        }
    }

    /// The payload as a big-endian integer of at most 32 bytes, in little-endian limbs.
    pub(crate) fn uint(&self) -> Result<[u64; 4], ProofError> {
        // At most 256 bits.
        if self.list || self.len() > 32 {
            return Err(ProofError::Malformed);
        }
        // The last byte is the least significant: it goes to bits 0..8 of limb 0.
        //
        //     payload  0x01 0x00 0x00  → 0x010000 → limbs [0x10000, 0, 0, 0]
        let mut limbs = [0; 4];
        for i in 0..self.len() {
            let byte = self.byte(self.len() - 1 - i)? as u64;
            limbs[i / 8] |= byte << (8 * (i % 8));
        }
        Ok(limbs)
    }
}

/// The value at `key` under `root`, `None` if the proof shows the key absent.
///
/// The value is the leaf's payload, the RLP string's bytes.
///
/// # Errors
///
/// - A node's hash is not its parent's reference to it.
/// - A node is not the RLP the trie writes.
/// - The proof ends before the path does, or goes on past it.
/// - A node is embedded in its parent, which no trie keyed by 32-byte hashes has.
pub(crate) fn get<'a>(
    root: &Hash,
    key: &Hash,
    proof: impl IntoIterator<Item = Node<'a>>,
) -> Result<Option<Item<'a>>, ProofError> {
    let mut nodes = proof.into_iter();
    // The reference the next node must hash to, and the key's nibbles walked so far.
    let mut expected = *root;
    let mut depth = 0;

    // The empty trie: its proof is no node (geth), or the empty string whose hash the root is (alloy-trie).
    if expected == EMPTY_ROOT {
        return match nodes.next() {
            None => Ok(None),
            Some(node) if node.hash() != EMPTY_ROOT => Err(ProofError::Hash),
            Some(_) => nodes.next().map_or(Ok(None), |_| Err(ProofError::TooLong)),
        };
    }

    let found = loop {
        // Invariant: the node is the one the reference names, so its bytes are the trie's own.
        let node = nodes.next().ok_or(ProofError::TooShort)?;
        if node.hash() != expected {
            return Err(ProofError::Hash);
        }

        // Two items make an extension or a leaf, seventeen a branch.
        let list = node.item()?;
        let first = list.first()?;
        let second = list.item_at(first.end)?;

        let child = if second.end == list.end {
            // An extension or a leaf: its path must be the key's next nibbles.
            let (matches, leaf) = follow(&first, key, &mut depth)?;
            match (matches, leaf) {
                // The key leaves the path here: it is absent.
                (false, _) => break None,
                // A leaf ending the key: its second item is the value.
                (true, true) if depth == KEY_NIBBLES => break Some(second),
                // A leaf ending short of a 64-nibble key: no Ethereum trie has one.
                (true, true) => return Err(ProofError::Malformed),
                // An extension: its second item is the reference to the next node.
                (true, false) => second,
            }
        } else {
            // A branch: the key's next nibble picks the child.
            //
            //     keys are 64 nibbles, so no branch sits at the end of one and holds a value
            if depth == KEY_NIBBLES {
                return Err(ProofError::Malformed);
            }
            let child = list.nth(nibble(key, depth))?;
            depth += 1;
            child
        };

        // The next node: none, or the one whose hash the reference is.
        //
        //     0x80          the empty string: no node, the key is absent
        //     0xa0 + 32     a hash: the next node of the proof
        //     0xc0..        a list under 32 bytes, embedded: never in Ethereum's tries
        match (child.list, child.len()) {
            (false, 0) => break None,
            (false, 32) => expected = child.hash()?,
            (true, _) => return Err(ProofError::InlineNode),
            _ => return Err(ProofError::Malformed),
        }
    };

    // The path ended: a canonical proof has no node past it.
    match nodes.next() {
        None => Ok(found),
        Some(_) => Err(ProofError::TooLong),
    }
}

/// Match an extension's or a leaf's path against the key from `depth` on.
///
/// Returns whether it matches and whether the node is a leaf.
///
/// On a match, `depth` moves past the path.
///
/// The path is hex-prefix encoded: a flag nibble, then a padding nibble when the length is even.
///
/// ```text
///   flag   0  extension, even     1  extension, odd
///          2  leaf, even          3  leaf, odd
///
///   [flag | 0] [n0 n1] [n2 n3] ...       even: the first byte holds no nibble of the path
///   [flag | n0] [n1 n2] ...              odd: the first byte holds the first one
/// ```
fn follow(path: &Item<'_>, key: &Hash, depth: &mut usize) -> Result<(bool, bool), ProofError> {
    // The path is a string holding at least the flag byte.
    if path.list || path.len() == 0 {
        return Err(ProofError::Malformed);
    }
    let flag = path.byte(0)? >> 4;
    if flag > 3 {
        return Err(ProofError::Malformed);
    }
    // Bit 0 of the flag is the parity, bit 1 the leaf marker.
    let (odd, leaf) = (usize::from(flag & 1), flag & 2 != 0);

    // Nibbles in the path: two per byte, less the flag and, when even, the padding.
    //
    //     3 bytes, odd   → 2 * 3 - 1 = 5 nibbles
    //     3 bytes, even  → 2 * 3 - 2 = 4 nibbles
    let len = 2 * path.len() - 2 + odd;
    // A path longer than the key's rest cannot be its continuation.
    if *depth + len > KEY_NIBBLES {
        return Ok((false, leaf));
    }
    for j in 0..len {
        // Nibble `j` of the path is nibble `j + 2 - odd` of the payload, high half first.
        let at = j + 2 - odd;
        let byte = path.byte(at / 2)?;
        let nib = if at % 2 == 0 { byte >> 4 } else { byte & 0xf };
        // One differing nibble and the key leaves the path.
        if usize::from(nib) != nibble(key, *depth + j) {
            return Ok((false, leaf));
        }
    }
    *depth += len;
    Ok((true, leaf))
}

/// Nibble `d` of a key: byte `d / 2`, its high half first.
const fn nibble(key: &Hash, d: usize) -> usize {
    // Byte `d / 2` of the key is byte `(d % 16) / 2` of word `d / 16`.
    let byte = key[d / 16] >> (8 * ((d % 16) / 2));
    // An even nibble is the byte's high half.
    (if d.is_multiple_of(2) { byte >> 4 } else { byte } & 0xf) as usize
}
