//! What every proof of a tree states, in one layout whatever its place in the tree.
//!
//! - Its kind: what its circuit verifies.
//! - The digest of the leaves' outputs under it.
//! - One claim on each dense polynomial, at prefixes of one point.
//! - Each flock circuit's two matrices at prefixes of one row point and one column point.

use primitives::F64;

use super::claims::DensePoly;
use crate::class_flock::{FlockId, N_FLOCKS};
use crate::rec::circuit::{Builder, Dw, Ew, Kw, Limbs, chain};
use primitives::F192;
use std::ops::Range;

/// What a tree proof's circuit verifies.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Kind {
    /// RISC-V proofs of the tree's program: a node of the first level.
    First,
    /// Recursion proofs of either kind: a node above the first level.
    Node,
}

/// Where each part of a tree statement sits among its words.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct StatementLayout {
    /// The dense point's coordinates: the most any dense polynomial has.
    n_dense: usize,
    /// The matrix points' coordinates: the most any flock circuit's matrices have.
    n_matrix: usize,
}

/// A section of a tree statement, in statement order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Section {
    /// The kind's word.
    Kind,
    /// The digest's two 128-bit halves.
    Digest,
    /// The dense claims' point.
    DensePoint,
    /// Each dense polynomial's value at its prefix of the point.
    DenseValues,
    /// The matrix claims' row point.
    Rows,
    /// The matrix claims' column point.
    Cols,
    /// Each flock circuit's two matrices at their prefixes of the points.
    Matrices,
}

/// A tree proof's statement, every word an `E` element: a value, or the wire holding it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TreeStatement<E = F192> {
    layout: StatementLayout,
    words: Vec<E>,
}

impl Kind {
    /// Both kinds, by their statement word.
    pub const ALL: [Self; 2] = [Self::First, Self::Node];

    /// Its statement word: the bit that selects its circuit's half of the nodes' fixed polynomial.
    pub(crate) const fn bit(self) -> u64 {
        self as u64
    }

    /// The kind a statement word names.
    pub(crate) fn of_word(word: F192) -> Option<Self> {
        Self::ALL
            .into_iter()
            .find(|k| F192::new([F64::new(k.bit()), F64::new(0), F64::new(0)]) == word)
    }

    /// The first word of its digest's message.
    const fn tag(self) -> u64 {
        match self {
            Self::First => u64::from_le_bytes(*b"tree-fst"),
            Self::Node => u64::from_le_bytes(*b"tree-nod"),
        }
    }

    /// Its digest's first block: its tag and how many items follow, then zeros.
    const fn header(self, count: usize) -> [u64; 8] {
        [self.tag(), count as u64, 0, 0, 0, 0, 0, 0]
    }

    /// The digest of the items under a proof of this kind: the leaves' outputs under a node of the first level, its children's digests under a node.
    ///
    /// The tag separates the levels and the count fixes the items, so a digest names its whole subtree.
    pub(crate) fn digest(self, items: &[Limbs]) -> Limbs {
        let words: Vec<u64> = (self.header(items.len()).into_iter())
            .chain(items.iter().flatten().copied())
            .collect();
        chain(&words)
    }

    /// The digest of the items' wires, in rows.
    pub(crate) fn digest_rows(self, b: &mut Builder, items: &[[Kw; 4]]) -> Dw {
        let header = self.header(items.len()).map(|w| b.k_const(w));
        let words: Vec<Kw> = header.into_iter().chain(items.iter().flatten().copied()).collect();
        b.chain(&words)
    }
}

impl Section {
    /// Every section, in statement order.
    const ALL: [Self; 7] = [
        Self::Kind,
        Self::Digest,
        Self::DensePoint,
        Self::DenseValues,
        Self::Rows,
        Self::Cols,
        Self::Matrices,
    ];
}

impl StatementLayout {
    /// The layout of a tree whose dense polynomials have at most this many variables.
    pub(crate) const fn new(n_dense: usize) -> Self {
        Self {
            n_dense,
            n_matrix: FlockId::MAX_K_LOG,
        }
    }

    /// How many words a section has.
    const fn width(self, section: Section) -> usize {
        match section {
            Section::Kind => 1,
            Section::Digest => 2,
            Section::DensePoint => self.n_dense,
            Section::DenseValues => DensePoly::COUNT,
            Section::Rows | Section::Cols => self.n_matrix,
            Section::Matrices => 2 * N_FLOCKS,
        }
    }

    /// Where a section's words sit: after every section before it.
    pub(crate) fn range(self, section: Section) -> Range<usize> {
        let start = (Section::ALL.into_iter())
            .take_while(|&s| s != section)
            .map(|s| self.width(s))
            .sum();
        start..start + self.width(section)
    }

    /// How many words a statement has.
    pub(crate) fn len(self) -> usize {
        Section::ALL.into_iter().map(|s| self.width(s)).sum()
    }
}

impl<E: Copy> TreeStatement<E> {
    /// The statement of these words, which must be the layout's number.
    pub(crate) fn new(layout: StatementLayout, words: Vec<E>) -> Self {
        assert_eq!(words.len(), layout.len(), "a statement has its layout's words");
        Self { layout, words }
    }

    /// A statement of the layout, every word `fill`, to be written section by section.
    pub(crate) fn filled(layout: StatementLayout, fill: E) -> Self {
        Self::new(layout, vec![fill; layout.len()])
    }

    /// A section's words, to write.
    pub(crate) fn section_mut(&mut self, section: Section) -> &mut [E] {
        &mut self.words[self.layout.range(section)]
    }

    /// A section's words.
    fn section(&self, section: Section) -> &[E] {
        &self.words[self.layout.range(section)]
    }

    /// Its words, in order.
    pub(crate) fn words(&self) -> &[E] {
        &self.words
    }

    /// The same statement, each word mapped by `f`.
    pub(crate) fn map<T>(&self, f: impl FnMut(&E) -> T) -> TreeStatement<T> {
        TreeStatement {
            layout: self.layout,
            words: self.words.iter().map(f).collect(),
        }
    }

    /// The kind's word.
    pub(crate) fn kind(&self) -> E {
        self.section(Section::Kind)[0]
    }

    /// The digest's two halves.
    pub(crate) fn digest(&self) -> [E; 2] {
        let d = self.section(Section::Digest);
        [d[0], d[1]]
    }

    /// The dense point.
    pub(crate) fn dense_point(&self) -> &[E] {
        self.section(Section::DensePoint)
    }

    /// A dense polynomial's claimed value at its prefix of the point.
    pub(crate) fn dense_value(&self, poly: DensePoly) -> E {
        self.section(Section::DenseValues)[poly as usize]
    }

    /// The matrices' row point.
    pub(crate) fn rows(&self) -> &[E] {
        self.section(Section::Rows)
    }

    /// The matrices' column point.
    pub(crate) fn cols(&self) -> &[E] {
        self.section(Section::Cols)
    }

    /// Flock circuit `f`'s two matrices at their prefixes of the points.
    pub(crate) fn matrices(&self, f: FlockId) -> [E; 2] {
        let m = self.section(Section::Matrices);
        [m[2 * f.index()], m[2 * f.index() + 1]]
    }
}

impl TreeStatement {
    /// The digest's words.
    pub(crate) fn digest_words(&self) -> Limbs {
        let [lo, hi] = self.digest();
        [
            lo.coefficients()[0].to_bits(),
            lo.coefficients()[1].to_bits(),
            hi.coefficients()[0].to_bits(),
            hi.coefficients()[1].to_bits(),
        ]
    }
}

impl TreeStatement<Ew> {
    /// The digest as one wire, its halves' top limbs held to zero.
    pub(crate) fn digest_wire(&self, b: &mut Builder) -> Dw {
        let [lo, hi] = self.digest();
        b.halves_to_d(lo, hi)
    }
}

/// A digest's wire as two halves, in rows.
pub(crate) fn digest_halves_rows(b: &mut Builder, d: Dw) -> [Ew; 2] {
    let [w0, w1, w2, w3] = b.d_to_k(d);
    let zero = b.k_const(0);
    [b.k_to_e([w0, w1, zero]), b.k_to_e([w2, w3, zero])]
}
