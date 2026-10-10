//! A tuple coordinate as a function of its block's row, and the public columns a coordinate reads.

use crate::rec::FixedColumn;
use fiat_shamir::arith::{Arith, Native};
use fiat_shamir::transcript::VerifierState;
use primitives::field::{F64, F192};
use std::sync::{Arc, OnceLock};

/// One tuple coordinate as a function of the block's row `z`.
#[derive(Clone, Debug)]
pub enum Coord {
    /// A public constant (domain separator, opcode, a position).
    Const(F64),
    /// A committed column, value `col[z]`.
    Col(usize),
    /// The product `col_a[z] · col_b[z]` of two columns, carried on the bus without
    /// committing it: the coordinate IS the product, so no column can disagree with
    /// it and no constraint has to say so (§sec:m3).
    Prod(usize, usize),
    /// A committed column times a public constant, `c · col[z]`: what makes a coordinate depend on a 0 or 1 column
    /// (an extension-field row's `base` bit choosing between two separators).
    Scaled(F64, usize),
    /// The integer index column `base ^ (z << shift)` (§sec:idxcol), the element
    /// whose bits are that integer's: what addresses a region whose cell `z` sits at
    /// `base + (z << shift)`. Free, its MLE being linear.
    IntIndex { base: F64, shift: u32 },
    /// A public column (the bytecode program, §sec:e2e-bc): not committed; both parties form
    /// its MLE directly, so it raises no claim. Shared rather than owned: a column is
    /// tens of megabytes at production sizes.
    Public(PublicColumn),
    /// A public column that is zero outside a few blocks (RAM as the run finds it,
    /// §sec:memchan): the verifier evaluates it in time proportional to the blocks,
    /// not to the column.
    Sparse(Arc<SparseColumn>),
    /// A sum of `Const`/`Col`/`Prod`/`Scaled` terms: any degree-2 form over the
    /// table's columns, which is all §sec:m3 asks of a coordinate. This is what
    /// carries a value a row DERIVES from its columns (a branch's successor, what a
    /// jump writes to `rd`, a hash row's block addresses) without committing a column for it, and
    /// with it the identity that would have tied the two. Like [`Coord::Prod`],
    /// only a table's blocks may carry one: the table sumcheck settles them,
    /// while a framework block has to split into per-column openings.
    Sum(Vec<Self>),
}

/// A public column's words, and which fixed column of a recursion circuit they are, if any.
#[derive(Clone, Debug)]
pub struct PublicColumn {
    /// The words.
    pub values: Arc<Vec<F64>>,
    /// The recursion circuit's fixed column the words are, whose evaluation a recursive verifier takes as a hint.
    pub(crate) fixed: Option<FixedColumn>,
}

impl PublicColumn {
    /// A column that is no recursion circuit's fixed column.
    pub const fn new(values: Arc<Vec<F64>>) -> Self {
        Self { values, fixed: None }
    }

    /// A recursion circuit's fixed column.
    pub(crate) const fn fixed(values: Arc<Vec<F64>>, column: FixedColumn) -> Self {
        Self {
            values,
            fixed: Some(column),
        }
    }
}

/// Arithmetic that evaluates public columns.
///
/// A recursive verifier takes a fixed column's evaluation as a hint rather than computing it.
pub(crate) trait PublicColumns: Arith {
    /// The multilinear extension of a public column at `point`, lowest coordinate first.
    fn column_mle(&mut self, column: &PublicColumn, point: &[Self::E]) -> Self::E {
        self.public_mle(&column.values, point)
    }
}

impl PublicColumns for Native {}

impl PublicColumns for VerifierState<'_> {}

impl Coord {
    /// The coordinate on a table's row, its columns' values given.
    ///
    /// # Panics
    ///
    /// Panics on a coordinate no table carries.
    pub fn value(&self, row: &[F64]) -> F64 {
        match self {
            Self::Const(c) => *c,
            Self::Col(i) => row[*i],
            Self::Prod(i, j) => row[*i] * row[*j],
            Self::Scaled(c, i) => *c * row[*i],
            Self::Sum(terms) => terms.iter().fold(F64::ZERO, |acc, t| acc + t.value(row)),
            Self::IntIndex { .. } | Self::Public(_) | Self::Sparse(_) => {
                unreachable!("a table carries no indexed coordinate")
            }
        }
    }

    /// Whether the coordinate is linear in the columns: it multiplies no column by another.
    pub fn is_linear(&self) -> bool {
        match self {
            Self::Prod(..) => false,
            Self::Sum(terms) => terms.iter().all(Self::is_linear),
            _ => true,
        }
    }

    /// The coordinate with every column index shifted by `base`: a table's local coordinate, made global.
    pub fn offset(self, base: usize) -> Self {
        match self {
            Self::Col(i) => Self::Col(base + i),
            Self::Prod(i, j) => Self::Prod(base + i, base + j),
            Self::Scaled(c, i) => Self::Scaled(c, base + i),
            Self::Sum(cs) => Self::Sum(cs.into_iter().map(|c| c.offset(base)).collect()),
            other => other,
        }
    }
}

/// A public column of `2^log_len` words given by its nonzero stretches, each cut into
/// ALIGNED blocks: a power of two of words, at an offset that is a multiple of it. Such
/// a block's share of the column's multilinear extension is its own extension in the
/// low variables times the indicator of its offset's bits in the high ones.
#[derive(Debug)]
pub struct SparseColumn {
    log_len: usize,
    blocks: Vec<(usize, Vec<F64>)>,
    /// The column written out, which only the prover needs.
    dense: OnceLock<Vec<F64>>,
}

impl SparseColumn {
    /// From `(offset, words)` stretches, which must not overlap.
    pub fn new(log_len: usize, stretches: &[(usize, &[u64])]) -> Self {
        let mut blocks = Vec::new();
        for &(mut at, mut words) in stretches {
            assert!(at + words.len() <= 1 << log_len, "a stretch runs past the column");
            while !words.is_empty() {
                // The largest aligned block starting here that the stretch still fills.
                let aligned = if at == 0 { usize::MAX } else { 1 << at.trailing_zeros() };
                let size = aligned.min(1 << words.len().ilog2());
                blocks.push((at, words[..size].iter().map(|&w| F64(w)).collect()));
                (at, words) = (at + size, &words[size..]);
            }
        }
        Self {
            log_len,
            blocks,
            dense: OnceLock::new(),
        }
    }

    pub(super) fn dense(&self) -> &[F64] {
        self.dense.get_or_init(|| {
            let mut column = vec![F64::ZERO; 1 << self.log_len];
            for (at, words) in &self.blocks {
                column[*at..at + words.len()].copy_from_slice(words);
            }
            column
        })
    }

    /// The column's multilinear extension at `point`.
    pub(crate) fn eval(&self, point: &[F192]) -> F192 {
        assert_eq!(point.len(), self.log_len);
        self.blocks.iter().fold(F192::ZERO, |acc, (at, words)| {
            let k = words.len().ilog2() as usize;
            let selector = point[k..].iter().enumerate().fold(F192::ONE, |s, (j, &z)| {
                s * if (at >> (k + j)) & 1 == 1 { z } else { z + F192::ONE }
            });
            acc + selector * primitives::multilinear::mle_eval(words, &point[..k])
        })
    }
}
