//! The verifier of a leanVM proof as rows of the recursion machine (Annex E).
//!
//! - The bus, its GKR and the table sumcheck are the native verifier's own code, run over wires.
//! - The flock reductions and the opening are the native verifier's code too, over the rows' transcript and Merkle openings.
//!
//! No row depends on a value: a circuit built from a proof equals the one built from its shape.

use super::circuit::{Builder, Dw, Ew, Kw};
use super::transcript::Transcript;
use crate::leaf::{PublicColumn, PublicColumns};
use fiat_shamir::TranscriptContext;
use fiat_shamir::arith::{Arith, PublicMle, Stage, Verifier};
use fiat_shamir::transcript::TranscriptError;
use pcs::verifier::OpeningVerifier;
use pcs::whir::{Stratum, strata};
use primitives::field::F192;
use recursion::FixedHints;
use std::fmt::Debug;

mod recursion;
mod riscv;

#[cfg(test)]
mod tests;

pub(crate) use recursion::{FixedHint, RecShape};
pub use riscv::ProofShape;

/// The verifier's arithmetic and transcript as rows: a circuit being built, and a transcript replayed in it.
///
/// A read never fails and an equality never refuses: both become rows, which the outer proof checks.
///
/// A public column is evaluated in rows, unless it is a fixed column of the recursion proof being verified: its evaluation is then a hint.
pub(crate) struct Rows<'a, 's> {
    b: &'a mut Builder,
    t: &'a mut Transcript<'s>,
    fixed: Option<&'a mut FixedHints<'s>>,
}

impl<'a, 's> Rows<'a, 's> {
    /// Rows appended to `b`, reading through `t`.
    pub(crate) const fn new(b: &'a mut Builder, t: &'a mut Transcript<'s>) -> Self {
        Self { b, t, fixed: None }
    }

    /// Rows appended to `b`, reading through `t`, that take every evaluation of a fixed column as a hint.
    pub(crate) const fn hinting(b: &'a mut Builder, t: &'a mut Transcript<'s>, fixed: &'a mut FixedHints<'s>) -> Self {
        Self {
            b,
            t,
            fixed: Some(fixed),
        }
    }
}

impl Arith for Builder {
    type E = Ew;

    fn constant(&mut self, c: F192) -> Ew {
        self.e_const(c)
    }

    fn mul_add(&mut self, a: Ew, b: Ew, d: Ew) -> Ew {
        Self::mul_add(self, a, b, d)
    }

    fn add(&mut self, a: Ew, d: Ew) -> Ew {
        Self::add(self, a, d)
    }

    fn mul_const_add(&mut self, a: Ew, c: F192, d: Ew) -> Ew {
        Self::mul_const_add(self, a, c, d)
    }

    fn inv(&mut self, a: Ew) -> Ew {
        Self::inv(self, a)
    }

    /// `v + c2 (Y + Y^2) + c1 Y^2` for `v = c0 + c1 Y + c2 Y^2`.
    fn frobenius2(&mut self, a: Ew) -> Ew {
        let [_, c1, c2] = self.e_to_k(a);
        let y_y2 = self.e_const(F192::new(0, 1, 1));
        let y2 = self.e_const(F192::new(0, 0, 1));
        let u = self.mul_k_add(y_y2, c2, a);
        self.mul_k_add(y2, c1, u)
    }

    fn zero(&mut self) -> Ew {
        Self::zero(self)
    }

    fn one(&mut self) -> Ew {
        Self::one(self)
    }

    fn mul(&mut self, a: Ew, b: Ew) -> Ew {
        Self::mul(self, a, b)
    }
}

impl PublicMle for Builder {}

impl Arith for Rows<'_, '_> {
    type E = Ew;

    fn constant(&mut self, c: F192) -> Ew {
        self.b.e_const(c)
    }

    fn mul_add(&mut self, a: Ew, b: Ew, d: Ew) -> Ew {
        self.b.mul_add(a, b, d)
    }

    fn add(&mut self, a: Ew, d: Ew) -> Ew {
        self.b.add(a, d)
    }

    fn mul_const_add(&mut self, a: Ew, c: F192, d: Ew) -> Ew {
        self.b.mul_const_add(a, c, d)
    }

    fn inv(&mut self, a: Ew) -> Ew {
        self.b.inv(a)
    }

    fn frobenius2(&mut self, a: Ew) -> Ew {
        self.b.frobenius2(a)
    }

    fn zero(&mut self) -> Ew {
        self.b.zero()
    }

    fn one(&mut self) -> Ew {
        self.b.one()
    }

    fn mul(&mut self, a: Ew, b: Ew) -> Ew {
        self.b.mul(a, b)
    }
}

impl PublicMle for Rows<'_, '_> {}

impl PublicColumns for Rows<'_, '_> {
    fn column_mle(&mut self, column: &PublicColumn, point: &[Ew]) -> Ew {
        match (self.fixed.as_deref_mut(), column.fixed) {
            (Some(hints), Some(fixed)) => hints.evaluate(self.b, fixed, point),
            _ => self.b.public_mle(&column.values, point),
        }
    }
}

impl Verifier for Rows<'_, '_> {
    fn next_scalar(&mut self) -> Result<Ew, TranscriptError> {
        Ok(self.t.next_scalar(self.b))
    }

    fn next_round_poly(&mut self, n_coeffs: usize, claim: Ew, eq: Option<Ew>) -> Result<Vec<Ew>, TranscriptError> {
        Ok(self.t.next_round_poly(self.b, n_coeffs, claim, eq))
    }

    fn sample(&mut self) -> Ew {
        self.t.sample(self.b)
    }

    fn grind_check(&mut self, bits: u32) -> Result<(), TranscriptError> {
        self.t.grind_check(self.b, bits);
        Ok(())
    }

    fn ensure_eq<Er>(&mut self, a: Ew, b: Ew, _: impl FnOnce() -> Er) -> Result<(), Er> {
        self.b.eq_e(a, b);
        Ok(())
    }

    fn finish(&mut self) -> Result<(), TranscriptError> {
        if !self.t.finished() {
            self.begin_scope(Stage::Transcript);
            self.b.fail("the proof has data the verifier never reads");
            self.end_scope();
        }
        Ok(())
    }

    fn begin_scope(&mut self, stage: Stage) {
        let name = match stage {
            Stage::Announcement => "announcement",
            Stage::BusAndTables => "bus and tables",
            Stage::Flock => "flock",
            Stage::Lincheck => "lincheck",
            Stage::Opening => "opening",
            Stage::Rows => "rows",
            Stage::Target => "target",
            Stage::Terminal => "terminal",
            Stage::Transcript => "transcript",
            Stage::Whir => "whir",
            Stage::Zerocheck => "zerocheck",
        };
        self.b.enter(name);
    }

    fn end_scope(&mut self) {
        self.b.leave();
    }
}

impl OpeningVerifier for Rows<'_, '_> {
    type Root = Dw;
    type K = Kw;
    /// A query's index bits, lowest first.
    type Query = Vec<Kw>;

    fn context(&mut self) -> TranscriptContext<Kw, Dw> {
        self.t.context()
    }

    fn zero_k(&mut self) -> Kw {
        self.b.k_const(0)
    }

    fn root_scalars(&mut self, root: Dw) -> [Ew; 2] {
        let [w0, w1, w2, w3] = self.b.d_to_k(root);
        let zero = self.b.k_const(0);
        [self.e_of_limbs([w0, w1, zero]), self.e_of_limbs([w2, w3, zero])]
    }

    fn next_root(&mut self) -> Result<Dw, TranscriptError> {
        Ok(self.t.next_root(self.b))
    }

    /// Each challenge's 192 bits `c0 | c1 << 64 | c2 << 128`, split, then cut into queries.
    fn sample_queries(&mut self, depth: usize, count: usize) -> Vec<Vec<Kw>> {
        let per = 192 / depth;
        let mut out = Vec::with_capacity(count);
        while out.len() < count {
            let v = self.sample();
            let n = per.min(count - out.len());
            let limbs = self.b.e_to_k(v);
            let mut bits = Vec::with_capacity(192);
            for &limb in &limbs[..(n * depth).div_ceil(64)] {
                bits.extend(self.b.split(limb));
            }
            out.extend((0..n).map(|j| bits[j * depth..(j + 1) * depth].to_vec()));
        }
        // Each query's top bits are its stratum's, constants of the shape.
        for (bits, s) in out.iter_mut().zip(strata(count, depth)) {
            let low = depth - s.bits;
            for (i, bit) in bits[low..].iter_mut().enumerate() {
                *bit = self.b.k_const((s.index >> i) as u64 & 1);
            }
        }
        out
    }

    fn open_rows(
        &mut self,
        root: &Dw,
        _depth: usize,
        queries: &[Vec<Kw>],
        row_words: usize,
        leaf_words: usize,
    ) -> Result<Vec<Vec<Kw>>, TranscriptError> {
        Ok(authenticate(self, *root, queries, row_words, leaf_words))
    }

    fn mul_k_add(&mut self, a: Ew, k: Kw, d: Ew) -> Ew {
        self.b.mul_k_add(a, k, d)
    }

    fn e_of_limbs(&mut self, limbs: [Kw; 3]) -> Ew {
        self.b.k_to_e(limbs)
    }

    fn query_point(&mut self, bits: &Vec<Kw>) -> Ew {
        let q = self.b.pack(bits);
        self.b.k_to_e1(q)
    }
}

/// Each query's row, hashed up its own low levels to its stratum's node, every node then tied to `root`.
///
/// A query of stratum `(s, j)` is hashed up its `depth - s` low levels to node `j` of the top subtree's level `s`.
/// The batch's largest group reaches every node of the subtree's bottom level, which is hashed once up to the root; every other query's node is the subtree's.
/// So each leaf sits `depth` levels below the root, as the shape fixes.
fn authenticate(
    r: &mut Rows<'_, '_>,
    root: Dw,
    queries: &[Vec<Kw>],
    row_words: usize,
    leaf_words: usize,
) -> Vec<Vec<Kw>> {
    let depth = queries[0].len();
    let strata: Vec<Stratum> = strata(queries.len(), depth);
    let top = strata[0].bits;
    let mut nodes: Vec<Vec<Option<Dw>>> = (0..=top).map(|s| vec![None; 1 << s]).collect();
    let tie = |b: &mut Builder, slot: &mut Option<Dw>, node: Dw| match *slot {
        Some(known) => b.eq_d(known, node),
        None => *slot = Some(node),
    };
    let rows = (queries.iter().zip(&strata))
        .map(|(bits, s)| {
            let (node, row) = r.t.open_row(r.b, &bits[..depth - s.bits], row_words, leaf_words);
            tie(r.b, &mut nodes[s.bits][s.index], node);
            row
        })
        .collect();
    for s in (1..=top).rev() {
        for j in 0..1 << (s - 1) {
            let [left, right] = [2 * j, 2 * j + 1].map(|i| nodes[s][i].expect("the largest group covers its level"));
            let node = r.b.parent(left, right);
            tie(r.b, &mut nodes[s - 1][j], node);
        }
    }
    tie(r.b, &mut nodes[0][0], root);
    rows
}

/// The value of a read the rows never refuse.
pub(crate) fn infallible<T, Er: Debug>(read: Result<T, Er>) -> T {
    read.unwrap_or_else(|e| unreachable!("rows record a failure rather than refuse: {e:?}"))
}
