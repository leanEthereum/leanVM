//! The verifier of a leanVM proof as rows of the recursion machine (Annex E).
//!
//! - The bus, its GKR and the table sumcheck are the native verifier's own code, run over wires.
//! - The flock reductions and the opening are the native verifier's code too, over the rows' transcript and Merkle openings.
//!
//! No row depends on a value: a circuit built from a proof equals the one built from its shape.

use super::circuit::{Builder, Dw, Ew, Kw};
use super::transcript::Transcript;
use crate::leaf::{PublicColumn, PublicColumns};
use ::pcs::verifier::OpeningVerifier;
use fiat_shamir::arith::{Arith, Verifier};
use fiat_shamir::transcript::TranscriptError;
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
            self.scope("transcript", |r| {
                r.b.fail("the proof has data the verifier never reads");
            });
        }
        Ok(())
    }

    fn scope<T>(&mut self, name: &'static str, f: impl FnOnce(&mut Self) -> T) -> T {
        self.b.enter(name);
        let out = f(self);
        self.b.leave();
        out
    }
}

impl OpeningVerifier for Rows<'_, '_> {
    type Root = Dw;
    type K = Kw;
    /// A query's index bits, lowest first.
    type Query = Vec<Kw>;

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
        Ok((queries.iter())
            .map(|bits| self.t.open_row(self.b, *root, bits, row_words, leaf_words))
            .collect())
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

/// The value of a read the rows never refuse.
pub(crate) fn infallible<T, Er: Debug>(read: Result<T, Er>) -> T {
    read.unwrap_or_else(|e| unreachable!("rows record a failure rather than refuse: {e:?}"))
}
