//! The verifier of a leanVM proof as rows of the recursion machine (Annex E).
//!
//! - The bus, its GKR and the table sumcheck are the native verifier's own code, run over wires.
//! - The flock reductions and the opening are replayed here, and tests pin them to the native verifier.
//!
//! No row depends on a value: a circuit built from a proof equals the one built from its shape.

mod flock;
mod recursion;
mod ring;
mod riscv;
mod whir;

#[cfg(test)]
mod tests;

pub(crate) use flock::SkipDomain;
pub(crate) use recursion::{FixedHint, RecShape};
pub(crate) use ring::RingMap;
pub use riscv::{CoreRows, ProofShape};

use super::circuit::{Builder, Ew};
use super::transcript::Transcript;
use crate::arith::{Arith, Verifier};
use fiat_shamir::transcript::Error as TranscriptError;
use primitives::field::{F64, F192};
use recursion::FixedHints;

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

    /// Run `f` under a name, which an equality that fails reports.
    fn scope<T>(&mut self, name: impl Into<String>, f: impl FnOnce(&mut Rows<'_, 's>) -> T) -> T {
        let (t, fixed) = (&mut *self.t, self.fixed.as_deref_mut());
        self.b.scope(name, |b| f(&mut Rows { b, t, fixed }))
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

    fn zero(&mut self) -> Ew {
        self.b.zero()
    }

    fn one(&mut self) -> Ew {
        self.b.one()
    }

    fn mul(&mut self, a: Ew, b: Ew) -> Ew {
        self.b.mul(a, b)
    }

    fn public_mle(&mut self, column: &[F64], point: &[Ew]) -> Ew {
        match self.fixed.as_deref_mut() {
            Some(fixed) => fixed.evaluate(self.b, column, point),
            None => Arith::public_mle(&mut *self.b, column, point),
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

    fn ensure_eq<Er>(&mut self, a: Ew, b: Ew, _: impl FnOnce() -> Er) -> Result<(), Er> {
        self.b.eq_e(a, b);
        Ok(())
    }
}

/// The value of a read the rows never refuse.
pub(crate) fn infallible<T, Er: std::fmt::Debug>(read: Result<T, Er>) -> T {
    read.unwrap_or_else(|e| unreachable!("rows record a failure rather than refuse: {e:?}"))
}
