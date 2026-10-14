//! A leaf circuit's statement read as a claim set of one group: what a proof of a signature circuit publishes in a
//! claim-set tree.
//!
//! A batch of signatures states each signature's words, and each signature is one claim: its label (the scheme's
//! word, the epoch where the scheme has one, the message) and its member (the key) are words of its statement or
//! constants. The claims of a leaf share their label, so its set is one group, its members in the statement's order:
//! the set the scheme's guest publishes for the same signatures, in the written form of [`super::multiset`].
//!
//! A first-level node reads the set from the leaf statement's wires, the ones its verifier's transcript absorbs: it
//! holds each claim's label to the first's and chains the set's written form, whose shape the statement's length
//! fixes, and the union reads the leaf's set at that digest.

use super::multiset::{ClaimGroup, ClaimSet, code};
use crate::rec::circuit::{Builder, Dw, Kw, Limbs, PARAM_IV};
use crate::rv::Hash;

/// One word of a claim: a constant, or a word of one of its signature's statement words.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ClaimWord {
    /// The constant.
    Const(u64),
    /// Word `word` of the signature's statement word `at`.
    At {
        /// The statement word, among the signature's.
        at: usize,
        /// Its word, of three.
        word: usize,
    },
}

/// How a leaf circuit's statement states its claims: every `words` statement words are one signature's, one claim.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ClaimLayout {
    /// A signature's statement words.
    pub(crate) words: usize,
    /// The label's words.
    pub(crate) label: [ClaimWord; 6],
    /// The member's words.
    pub(crate) member: [ClaimWord; 4],
}

impl ClaimWord {
    /// Its value in a signature's statement words.
    const fn value(self, signature: &[Limbs]) -> u64 {
        match self {
            Self::Const(c) => c,
            Self::At { at, word } => signature[at][word],
        }
    }

    /// Its wire in a signature's statement words' wires.
    fn wire(self, b: &mut Builder, signature: &[[Kw; 4]]) -> Kw {
        match self {
            Self::Const(c) => b.k_const(c),
            Self::At { at, word } => signature[at][word],
        }
    }

    /// Its words, for a tree's session: a tag, then the constant or the place.
    const fn tag(self) -> [u64; 3] {
        match self {
            Self::Const(c) => [0, c, 0],
            Self::At { at, word } => [1, at as u64, word as u64],
        }
    }
}

impl ClaimLayout {
    /// The set a statement states: one group, its members in the statement's order, if every claim has the first's
    /// label; the empty set if it states none.
    pub(crate) fn set(&self, statement: &[Limbs]) -> Option<ClaimSet> {
        let mut set = ClaimSet::new();
        for signature in statement.chunks_exact(self.words) {
            let label = self.label.map(|w| w.value(signature));
            let member = self.member.map(|w| w.value(signature));
            match set.groups.first_mut() {
                Some(g) if g.label == label => g.members.push(member),
                Some(_) => return None,
                None => set.groups.push(ClaimGroup {
                    label,
                    members: vec![member],
                }),
            }
        }
        Some(set)
    }

    /// Its words, for a tree's session.
    pub(crate) fn tag(&self) -> impl Iterator<Item = u64> + '_ {
        let words = (self.label.iter().chain(&self.member)).flat_map(|w| w.tag());
        std::iter::once(self.words as u64).chain(words)
    }

    /// The rows reading a statement's set from its wires, each statement word's words: each claim's label held to
    /// the first's, then the chain of the set's written form, one compression a block. Returns the set's digest.
    pub(crate) fn digest_rows(&self, b: &mut Builder, statement: &[[Kw; 4]]) -> Dw {
        let signatures: Vec<&[[Kw; 4]]> = statement.chunks_exact(self.words).collect();
        let zero = b.k_const(0);
        let mut blocks: Vec<([Kw; 8], u64)> = Vec::with_capacity(signatures.len().div_ceil(2) + 2);
        if let Some(first) = signatures.first() {
            let label = self.label.map(|w| w.wire(b, first));
            for s in &signatures[1..] {
                for (w, &l) in self.label.iter().zip(&label) {
                    if let ClaimWord::At { at, word } = *w {
                        b.eq(s[at][word], l);
                    }
                }
            }
            let [l0, l1, l2, l3, l4, l5] = label;
            blocks.push(([l0, l1, l2, l3, l4, l5, zero, zero], 0));
            for pair in signatures.chunks(2) {
                let [a0, a1, a2, a3] = self.member.map(|w| w.wire(b, pair[0]));
                let ([b0, b1, b2, b3], pair_bit) =
                    (pair.get(1)).map_or(([zero; 4], 0), |s| (self.member.map(|w| w.wire(b, s)), code::PAIR));
                blocks.push(([a0, a1, a2, a3, b0, b1, b2, b3], code::MEMBER | pair_bit));
            }
        }
        let tag = b.k_const(code::TAG);
        blocks.push(([tag, zero, zero, zero, zero, zero, zero, zero], code::END));
        let last = blocks.len() - 1;
        let iv = b.d_const(PARAM_IV);
        (blocks.into_iter().enumerate()).fold(iv, |h, (i, (m, c))| {
            let t = c | if i == 0 { code::START } else { 0 };
            let tf = b.d_const([t, if i == last { Hash::FINAL } else { 0 }, 0, 0]);
            b.block(h, m, tf)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Two statement words a claim, constants among the label's and the member's words.
    const LAYOUT: ClaimLayout = ClaimLayout {
        words: 2,
        label: [
            ClaimWord::Const(7),
            ClaimWord::At { at: 1, word: 0 },
            ClaimWord::At { at: 1, word: 1 },
            ClaimWord::At { at: 1, word: 2 },
            ClaimWord::Const(0),
            ClaimWord::Const(9),
        ],
        member: [
            ClaimWord::At { at: 0, word: 0 },
            ClaimWord::At { at: 0, word: 1 },
            ClaimWord::Const(3),
            ClaimWord::At { at: 0, word: 2 },
        ],
    };

    /// `n` claims under one label, member `i` read from `[i, 10 i, 100 i]`.
    fn statement(n: u64) -> Vec<Limbs> {
        (0..n).flat_map(|i| [[i, 10 * i, 100 * i, 0], [5, 6, 8, 0]]).collect()
    }

    /// The digest the rows give for a statement, and the constraints they leave unsatisfied.
    fn rows(statement: &[Limbs]) -> (Limbs, usize) {
        let mut b = Builder::new();
        let wires: Vec<[Kw; 4]> = (statement.iter())
            .map(|l| [b.free_k(l[0]), b.free_k(l[1]), b.free_k(l[2]), b.free_k(l[3])])
            .collect();
        let digest = LAYOUT.digest_rows(&mut b, &wires);
        let value = b.d(digest);
        (value, b.finish().failures.len())
    }

    #[test]
    fn the_rows_give_the_digest_of_the_statements_set() {
        // Invariant: the rows chain the written form of the one-group set the statement states, at every count.
        //
        //     claims   0         the empty set: the end alone
        //              1, 3      a half-empty last block of members
        //              2, 4      every block of members full
        for n in 0..=4 {
            let statement = statement(n);
            let set = LAYOUT.set(&statement).expect("one label");
            assert_eq!(set.groups.len(), usize::from(n > 0));
            assert_eq!(set.n_claims(), n as usize);
            assert_eq!(
                set.claims().nth(1).map(|c| c.member),
                (n > 1).then_some([1, 10, 3, 100])
            );
            assert_eq!(rows(&statement), (set.digest(), 0), "{n} claims");
        }
    }

    #[test]
    fn claims_of_two_labels_make_no_set_and_no_rows() {
        // Invariant: a leaf's claims share one label: a statement whose second claim has another one states no set,
        // and its rows do not hold.
        //
        //     claim 1's message word 2   8 → 9
        //     → set: none, rows: an unsatisfied equality
        let mut statement = statement(2);
        statement[3][2] = 9;
        assert_eq!(LAYOUT.set(&statement), None);
        assert_ne!(rows(&statement).1, 0);
    }
}
