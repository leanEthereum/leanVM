//! Claim sets: the multisets of claims a claim-set tree's proofs publish, their written form and their digest.
//!
//! A claim is a label of six words and a member of four. What they mean is the program's: a leaf program publishes
//! the claims it checked, and the tree only proves that every claim a proof declares is one its leaves published.
//!
//! A set is written as groups of claims sharing their label, each a header block, then its members two to a block,
//! then an end:
//!
//! ```text
//! header    label[0..6], 0, 0                              t = START? | 0
//! members   member_a[0..4], member_b[0..4] (zeros if none)  t = START? | MEMBER | PAIR if member_b is one
//! end       TAG, 0, 0, 0, 0, 0, 0, 0                         t = START? | END, the last block
//! ```
//!
//! Its digest is the chain of BLAKE2s compressions of its blocks from the parameter IV, each block's counter `t`
//! above, `START` on the first. So each block says what it is: the counter is an input of every compression, two
//! chains of one digest are one sequence of blocks with one parse or a collision of the compression function, and a
//! recursion circuit reads a set of any shape in a fixed number of rows. A program's guest computes the same chain
//! with the SDK's compression.
//!
//! A set in any order has a digest. The canonical one, which a root's verifier asks for, has its groups strictly
//! increasing on their labels, each non-empty with strictly increasing members, words compared as integers, first
//! word first; it holds each claim once.

use crate::rec::circuit::{Compression, Limbs, PARAM_IV};
use thiserror::Error;

/// A claim's label.
pub type Label = [u64; 6];

/// A claim's member.
pub type Member = [u64; 4];

/// The counter bits of a block, and the end's tag.
pub(crate) mod code {
    /// The first block.
    pub(crate) const START: u64 = 1;
    /// A block of members.
    pub(crate) const MEMBER: u64 = 2;
    /// The end.
    pub(crate) const END: u64 = 4;
    /// A block of members whose second member is one.
    pub(crate) const PAIR: u64 = 8;
    /// The end block's first word.
    pub(crate) const TAG: u64 = u64::from_le_bytes(*b"claimset");
}

/// One claim: a label and a member.
///
/// Claims order as a canonical set lists them: by label, then member.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Claim {
    /// The label.
    pub label: Label,
    /// The member.
    pub member: Member,
}

/// The claims of one label.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ClaimGroup {
    /// The label.
    pub label: Label,
    /// The members.
    pub members: Vec<Member>,
}

/// A multiset of claims, as a claim-set tree's proof declares it: groups, in the order they are written.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct ClaimSet {
    /// The groups.
    pub groups: Vec<ClaimGroup>,
}

/// The most a set may hold: fewer claims than `claims`, at most `groups` groups.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Capacity {
    /// The bound the claims stay strictly below.
    pub claims: usize,
    /// The most groups.
    pub groups: usize,
}

/// Why a set is not one a root may declare.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum ClaimSetError {
    /// Two groups out of order, or of one label.
    #[error("the groups are not strictly increasing on their labels")]
    UnsortedGroups,
    /// A group with no member.
    #[error("a group has no member")]
    EmptyGroup,
    /// A group whose members are out of order or repeated.
    #[error("a group's members are not strictly increasing")]
    UnsortedMembers,
    /// As many claims as the capacity's bound, or more.
    #[error("{got} claims, and a set holds fewer than {bound}")]
    TooManyClaims {
        /// The set's claims.
        got: usize,
        /// The exclusive bound.
        bound: usize,
    },
    /// More groups than the capacity.
    #[error("{got} groups, and a set holds at most {most}")]
    TooManyGroups {
        /// The set's groups.
        got: usize,
        /// The most.
        most: usize,
    },
}

/// One block of a set's written form and its counter bits, `START` aside.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Item {
    /// The block.
    pub(crate) block: [u64; 8],
    /// Its counter bits but `START`, which only its place gives.
    pub(crate) code: u64,
}

impl Capacity {
    /// leanVM `main`'s aggregation bounds: fewer than `2^16` claims, at most 1,024 groups.
    pub const MAIN: Self = Self {
        claims: 1 << 16,
        groups: 1024,
    };

    /// The most blocks a set within the capacity is written as: a header a group, a block per two members, the end.
    ///
    /// Each group's members take at most one half-empty block, so `(claims + groups) / 2` blocks hold them.
    #[must_use]
    pub const fn items(&self) -> usize {
        let claims = self.claims.saturating_sub(1);
        self.groups + (claims + self.groups).div_ceil(2) + 1
    }
}

impl ClaimSet {
    /// The empty set.
    #[must_use]
    pub const fn new() -> Self {
        Self { groups: Vec::new() }
    }

    /// The canonical set of these claims, each once.
    pub fn from_claims(claims: impl IntoIterator<Item = Claim>) -> Self {
        let mut claims: Vec<Claim> = claims.into_iter().collect();
        claims.sort_unstable();
        claims.dedup();
        let mut set = Self::new();
        for c in claims {
            match set.groups.last_mut() {
                Some(g) if g.label == c.label => g.members.push(c.member),
                _ => set.groups.push(ClaimGroup {
                    label: c.label,
                    members: vec![c.member],
                }),
            }
        }
        set
    }

    /// Every claim, in the set's order.
    pub fn claims(&self) -> impl Iterator<Item = Claim> + '_ {
        (self.groups.iter()).flat_map(|g| g.members.iter().map(|&member| Claim { label: g.label, member }))
    }

    /// How many claims it holds, repeats included.
    #[must_use]
    pub fn n_claims(&self) -> usize {
        self.groups.iter().map(|g| g.members.len()).sum()
    }

    /// Whether it has no group.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.groups.is_empty()
    }

    /// Its written form, block by block.
    pub(crate) fn items(&self) -> Vec<Item> {
        let mut items = Vec::new();
        for g in &self.groups {
            let [l0, l1, l2, l3, l4, l5] = g.label;
            items.push(Item {
                block: [l0, l1, l2, l3, l4, l5, 0, 0],
                code: 0,
            });
            for pair in g.members.chunks(2) {
                let [a0, a1, a2, a3] = pair[0];
                let [b0, b1, b2, b3] = pair.get(1).copied().unwrap_or([0; 4]);
                items.push(Item {
                    block: [a0, a1, a2, a3, b0, b1, b2, b3],
                    code: code::MEMBER | if pair.len() == 2 { code::PAIR } else { 0 },
                });
            }
        }
        items.push(Item {
            block: [code::TAG, 0, 0, 0, 0, 0, 0, 0],
            code: code::END,
        });
        items
    }

    /// Its digest: the chain of its blocks' compressions, by the portable compression: both sides compute it, the
    /// native verifier included.
    #[must_use]
    pub fn digest(&self) -> [u64; 4] {
        let items = self.items();
        let last = items.len() - 1;
        (items.iter().enumerate()).fold(PARAM_IV, |h: Limbs, (i, item)| {
            let t = item.code | if i == 0 { code::START } else { 0 };
            Compression::new(h, item.block, t, i == last).output_portable()
        })
    }

    /// Check it is canonical and within a capacity: what a root's verifier asks of the set it declares.
    ///
    /// # Errors
    ///
    /// The first rule it breaks.
    pub fn check(&self, capacity: Capacity) -> Result<(), ClaimSetError> {
        if !self.groups.windows(2).all(|w| w[0].label < w[1].label) {
            return Err(ClaimSetError::UnsortedGroups);
        }
        if self.groups.iter().any(|g| g.members.is_empty()) {
            return Err(ClaimSetError::EmptyGroup);
        }
        if !self.groups.iter().all(|g| g.members.windows(2).all(|w| w[0] < w[1])) {
            return Err(ClaimSetError::UnsortedMembers);
        }
        let claims = self.n_claims();
        if claims >= capacity.claims {
            return Err(ClaimSetError::TooManyClaims {
                got: claims,
                bound: capacity.claims,
            });
        }
        if self.groups.len() > capacity.groups {
            return Err(ClaimSetError::TooManyGroups {
                got: self.groups.len(),
                most: capacity.groups,
            });
        }
        Ok(())
    }

    /// Its bytes, little-endian throughout.
    ///
    /// ```text
    /// | n_groups: u32 | per group: label: 6 words, n_members: u32, members: 4 words each |
    /// ```
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        let len = |n: usize| u32::try_from(n).expect("fewer than 2^32 entries").to_le_bytes();
        let mut out = Vec::new();
        out.extend(len(self.groups.len()));
        for g in &self.groups {
            out.extend(g.label.iter().flat_map(|w| w.to_le_bytes()));
            out.extend(len(g.members.len()));
            for m in &g.members {
                out.extend(m.iter().flat_map(|w| w.to_le_bytes()));
            }
        }
        out
    }

    /// The set these bytes encode, if they encode one and nothing more.
    #[must_use]
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let mut rest = Reader(bytes);
        // A length is read before what it counts, so a length past the bytes left fails at the read, not at an
        // allocation.
        let n_groups = rest.u32()?;
        let mut set = Self::new();
        for _ in 0..n_groups {
            let label = rest.words()?;
            let n_members = rest.u32()?;
            let members = (0..n_members).map(|_| rest.words()).collect::<Option<_>>()?;
            set.groups.push(ClaimGroup { label, members });
        }
        rest.0.is_empty().then_some(set)
    }
}

/// The bytes of a claim set not read yet.
struct Reader<'a>(&'a [u8]);

impl Reader<'_> {
    /// The next little-endian `u32`.
    fn u32(&mut self) -> Option<u32> {
        let (head, tail) = self.0.split_first_chunk::<4>()?;
        self.0 = tail;
        Some(u32::from_le_bytes(*head))
    }

    /// The next `N` little-endian words.
    fn words<const N: usize>(&mut self) -> Option<[u64; N]> {
        let (head, tail) = self.0.split_at_checked(8 * N)?;
        self.0 = tail;
        let (chunks, _) = head.as_chunks::<8>();
        Some(std::array::from_fn(|i| u64::from_le_bytes(chunks[i])))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn member(i: u64) -> Member {
        [i, i ^ 0x5555, i.wrapping_mul(0x9e37_79b9), 7]
    }

    fn group(tag: u64, word: u64, members: &[u64]) -> ClaimGroup {
        ClaimGroup {
            label: [tag, word, 0, 0, 1, 2],
            members: members.iter().map(|&i| member(i)).collect(),
        }
    }

    fn sample() -> ClaimSet {
        ClaimSet {
            groups: vec![group(1, 3, &[1, 2, 3]), group(1, 4, &[1]), group(2, 0, &[2, 5])],
        }
    }

    #[test]
    fn the_digest_is_the_chain_of_its_blocks() {
        let end = ([code::TAG, 0, 0, 0, 0, 0, 0, 0], code::END);
        let chain = |blocks: &[([u64; 8], u64)]| {
            let last = blocks.len() - 1;
            (blocks.iter().enumerate()).fold(PARAM_IV, |h, (i, &(m, c))| {
                let t = c | if i == 0 { code::START } else { 0 };
                Compression::new(h, m, t, i == last).output()
            })
        };
        assert_eq!(ClaimSet::new().digest(), chain(&[end]));
        let set = ClaimSet {
            groups: vec![group(1, 3, &[1, 2, 3])],
        };
        let [a, b, c] = [member(1), member(2), member(3)];
        let blocks = [
            ([1, 3, 0, 0, 1, 2, 0, 0], 0),
            (
                [a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3]],
                code::MEMBER | code::PAIR,
            ),
            ([c[0], c[1], c[2], c[3], 0, 0, 0, 0], code::MEMBER),
            end,
        ];
        assert_eq!(set.digest(), chain(&blocks));
    }

    #[test]
    fn the_written_form_counts_its_claims() {
        let set = sample();
        assert_eq!((set.n_claims(), set.groups.len()), (6, 3));
        // Groups of 3, 1, 2 members: 2, 1, 1 blocks of members, three headers, the end.
        assert_eq!(set.items().len(), 3 + 4 + 1);
        assert!(set.items().len() <= Capacity { claims: 7, groups: 3 }.items());
        assert_eq!(ClaimSet::new().items().len(), 1);
    }

    #[test]
    fn distinct_sets_have_distinct_digests() {
        let base = sample();
        let mut moved = base.clone();
        let m = moved.groups[0].members.pop().expect("a member");
        moved.groups[1].members.push(m);
        let mut split = base.clone();
        let tail = split.groups[0].members.split_off(2);
        split.groups.insert(
            1,
            ClaimGroup {
                members: tail,
                ..split.groups[0].clone()
            },
        );
        let mut dropped = base.clone();
        dropped.groups[2].members.pop();
        let mut relabeled = base.clone();
        relabeled.groups[2].label[0] = 3;
        let mut reordered = base.clone();
        reordered.groups.reverse();
        for (i, v) in [ClaimSet::new(), moved, split, dropped, relabeled, reordered]
            .iter()
            .enumerate()
        {
            assert_ne!(v.digest(), base.digest(), "variant {i}");
        }
    }

    #[test]
    fn from_claims_is_canonical() {
        let set = sample();
        let mut claims: Vec<Claim> = set.claims().collect();
        claims.extend(set.claims().take(4));
        claims.reverse();
        let canonical = ClaimSet::from_claims(claims);
        assert_eq!(canonical.check(Capacity::MAIN), Ok(()));
        assert_eq!(canonical, set);
        assert_eq!(ClaimSet::from_claims([]).check(Capacity::MAIN), Ok(()));
        assert!(ClaimSet::from_claims([]).is_empty() && !canonical.is_empty());
    }

    #[test]
    fn check_refuses_every_noncanonical_set() {
        let canonical = sample();
        let cap = Capacity::MAIN;
        let mut s = canonical.clone();
        s.groups.swap(0, 1);
        assert_eq!(s.check(cap), Err(ClaimSetError::UnsortedGroups));
        let mut s = canonical.clone();
        s.groups.push(s.groups[2].clone());
        assert_eq!(s.check(cap), Err(ClaimSetError::UnsortedGroups));
        let mut s = canonical.clone();
        s.groups[0].members.clear();
        assert_eq!(s.check(cap), Err(ClaimSetError::EmptyGroup));
        let mut s = canonical.clone();
        s.groups[0].members.swap(0, 1);
        assert_eq!(s.check(cap), Err(ClaimSetError::UnsortedMembers));
        let mut s = canonical.clone();
        let m = s.groups[0].members[0];
        s.groups[0].members.insert(0, m);
        assert_eq!(s.check(cap), Err(ClaimSetError::UnsortedMembers));
        assert_eq!(
            canonical.check(Capacity { claims: 6, groups: 8 }),
            Err(ClaimSetError::TooManyClaims { got: 6, bound: 6 })
        );
        assert_eq!(
            canonical.check(Capacity { claims: 7, groups: 2 }),
            Err(ClaimSetError::TooManyGroups { got: 3, most: 2 })
        );
        assert_eq!(canonical.check(Capacity { claims: 7, groups: 3 }), Ok(()));
    }

    #[test]
    fn bytes_round_trip_and_nothing_more() {
        let set = sample();
        let bytes = set.to_bytes();
        assert_eq!(ClaimSet::from_bytes(&bytes), Some(set));
        assert_eq!(ClaimSet::from_bytes(&ClaimSet::new().to_bytes()), Some(ClaimSet::new()));
        let mut longer = bytes.clone();
        longer.push(0);
        assert_eq!(ClaimSet::from_bytes(&longer), None);
        assert_eq!(ClaimSet::from_bytes(&bytes[..bytes.len() - 1]), None);
        assert_eq!(ClaimSet::from_bytes(&[0xff, 0xff, 0xff, 0xff]), None);
    }
}
