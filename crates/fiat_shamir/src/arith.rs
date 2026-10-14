//! The verifier's arithmetic and transcript, written once for the native verifier and for its replay in rows.
//!
//! Code generic over these traits never reads a value: it takes the same steps whatever the proof holds.
//!
//! - Natively an element is an `F192`, a read comes off the proof, and a failed equality is an error.
//! - In rows an element is a wire, a read is a free wire bound by a hash row, and an equality joins two wires.

use crate::verifier::{TranscriptError, VerifierState};
use primitives::field::{F64, F192};
use primitives::multilinear::mle_eval_par;

/// Arithmetic over `E`, on values or on the wires that hold them.
pub trait Arith {
    /// An element of `E`: a value, or a wire, two of which are equal when they are one wire.
    type E: Copy + PartialEq;

    /// The constant `c`.
    fn constant(&mut self, c: F192) -> Self::E;

    /// `a·b + d`.
    fn mul_add(&mut self, a: Self::E, b: Self::E, d: Self::E) -> Self::E;

    /// `a + d`.
    fn add(&mut self, a: Self::E, d: Self::E) -> Self::E;

    /// `a·c + d` for a constant `c`.
    fn mul_const_add(&mut self, a: Self::E, c: F192, d: Self::E) -> Self::E;

    /// `1 / a`, zero for zero.
    fn inv(&mut self, a: Self::E) -> Self::E;

    /// `a^(2^128)`: two Frobenius maps of `E` over `K`, which take `a` to `a^(2^-64)`.
    fn frobenius2(&mut self, a: Self::E) -> Self::E;

    /// The constant zero.
    fn zero(&mut self) -> Self::E {
        self.constant(F192::ZERO)
    }

    /// The constant one.
    fn one(&mut self) -> Self::E {
        self.constant(F192::ONE)
    }

    /// `a·b`.
    fn mul(&mut self, a: Self::E, b: Self::E) -> Self::E {
        let zero = self.zero();
        self.mul_add(a, b, zero)
    }

    /// `a^2`.
    fn square(&mut self, a: Self::E) -> Self::E {
        self.mul(a, a)
    }

    /// `a·c` for a constant `c`.
    fn mul_const(&mut self, a: Self::E, c: F192) -> Self::E {
        let zero = self.zero();
        self.mul_const_add(a, c, zero)
    }

    /// `a + c` for a constant `c`.
    fn add_const(&mut self, a: Self::E, c: F192) -> Self::E {
        let c = self.constant(c);
        self.add(a, c)
    }

    /// `prod_i factors_i`.
    fn product(&mut self, factors: &[Self::E]) -> Self::E {
        let one = self.one();
        let mut acc = one;
        for &f in factors {
            acc = self.mul(acc, f);
        }
        acc
    }

    /// `sum_i c_i x^i`, by Horner, constant first.
    fn poly_eval(&mut self, coeffs: &[Self::E], x: Self::E) -> Self::E {
        let zero = self.zero();
        let mut acc = zero;
        let mut i = coeffs.len();
        while i > 0 {
            i -= 1;
            acc = self.mul_add(acc, x, coeffs[i]);
        }
        acc
    }

    /// The line through `(0, lo)` and `(1, hi)` at `t`: `lo + t·(lo + hi)`.
    fn interp(&mut self, lo: Self::E, hi: Self::E, t: Self::E) -> Self::E {
        let d = self.add(lo, hi);
        self.mul_add(t, d, lo)
    }

    /// `v·(1 + r)`.
    fn times_one_plus(&mut self, v: Self::E, r: Self::E) -> Self::E {
        self.mul_add(v, r, v)
    }

    /// `eq(x, y) = prod_j (1 + x_j + y_j)`.
    fn eq_eval(&mut self, x: &[Self::E], y: &[Self::E]) -> Self::E {
        assert_eq!(x.len(), y.len(), "two points of one cube");
        let one = self.one();
        let mut acc = one;
        for i in 0..x.len() {
            let s = self.add(x[i], y[i]);
            acc = self.times_one_plus(acc, s);
        }
        acc
    }

    /// `eq(bits, point)` for public bits, lowest first: `prod_j (bit_j ? z_j : 1 + z_j)`.
    ///
    /// The product runs from the highest coordinate down.
    /// Why: selectors of nearby offsets share their high bits, so in rows their common partial products are made once.
    fn eq_bits(&mut self, bits: usize, point: &[Self::E]) -> Self::E {
        let one = self.one();
        let mut acc = one;
        let mut j = point.len();
        while j > 0 {
            j -= 1;
            acc = if bits >> j & 1 == 1 {
                self.mul(acc, point[j])
            } else {
                self.times_one_plus(acc, point[j])
            };
        }
        acc
    }

    /// `eq(point, x)` for every vertex `x`, lowest coordinate first.
    fn eq_table(&mut self, point: &[Self::E]) -> Vec<Self::E> {
        self.eq_table_prefix(point, 1 << point.len())
    }

    /// `eq(point, x)` for the first `len` vertices `x`, lowest coordinate first, with no work for the others.
    fn eq_table_prefix(&mut self, point: &[Self::E], len: usize) -> Vec<Self::E> {
        assert!(len <= 1 << point.len(), "a prefix of the cube");
        let mut table = Vec::with_capacity(1);
        table.push(self.one());
        let mut i = 0;
        while i < point.len() {
            let r = point[i];
            let need = len.min(2 << i);
            let count = need.saturating_sub(table.len());
            let mut high = Vec::with_capacity(count);
            let mut j = 0;
            while j < count {
                high.push(self.mul(table[j], r));
                j += 1;
            }
            let mut j = 0;
            while j < table.len() {
                table[j] = self.times_one_plus(table[j], r);
                j += 1;
            }
            table.extend(high);
            i += 1;
        }
        table.truncate(len);
        table
    }

    /// The multilinear extension of `values` at `point`, folding the lowest coordinate first.
    fn mle(&mut self, values: &[Self::E], point: &[Self::E]) -> Self::E {
        assert_eq!(values.len(), 1 << point.len(), "a value per vertex");
        let mut folded = values.to_vec();
        for &x in point {
            let len = folded.len();
            let mut next = Vec::with_capacity(len / 2 + len % 2);
            let mut i = 0;
            while i < len {
                next.push(self.interp(folded[i], folded[i + 1], x));
                i += 2;
            }
            folded = next;
        }
        folded[0]
    }

    /// `[1, x, x^2, ...]`, `n` terms.
    fn powers(&mut self, x: Self::E, n: usize) -> Vec<Self::E> {
        let mut out = Vec::with_capacity(n);
        let mut acc = self.one();
        for _ in 0..n {
            out.push(acc);
            acc = self.mul(acc, x);
        }
        out
    }

    /// The integer index column `base ^ (z << shift)` at `point`: `base + sum_i point_i 2^(i + shift)`.
    fn int_index(&mut self, base: F64, shift: u32, point: &[Self::E]) -> Self::E {
        let base = self.constant(F192::from(base));
        let mut acc = base;
        for (i, &z) in point.iter().enumerate() {
            acc = self.mul_const_add(z, F192::from(F64(1 << (i as u32 + shift))), acc);
        }
        acc
    }
}

/// Arithmetic that also evaluates multilinear extensions of public columns.
pub trait PublicMle: Arith {
    /// The multilinear extension of public `K` words at `point`, lowest coordinate first.
    fn public_mle(&mut self, values: &[F64], point: &[Self::E]) -> Self::E {
        assert_eq!(values.len(), 1 << point.len(), "a column has a word per vertex");
        let eq = self.eq_table(point);
        let zero = self.zero();
        let mut acc = zero;
        for i in 0..eq.len().min(values.len()) {
            acc = self.mul_const_add(eq[i], F192::from(values[i]), acc);
        }
        acc
    }
}

/// Named stages of the generic verifier, independent of its native or row representation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stage {
    Announcement,
    BusAndTables,
    Flock,
    Lincheck,
    Opening,
    Rows,
    Target,
    Terminal,
    Transcript,
    Whir,
    Zerocheck,
}

/// A verifier: arithmetic, a transcript to read and sample, and equalities to check.
pub trait Verifier: Arith {
    /// The next prover message, an element of `E`, read and absorbed.
    ///
    /// # Errors
    ///
    /// Returns an error past the end of the proof.
    fn prover_message(&mut self) -> Result<Self::E, TranscriptError>;

    /// A verifier message: a uniform element of `E`, drawn from the sponge.
    fn verifier_message(&mut self) -> Self::E;

    /// Check `bits` of proof of work before the next verifier message.
    ///
    /// # Errors
    ///
    /// Returns an error past the end of the proof, or on a nonce short of the work when the verifier checks values.
    fn check_pow(&mut self, bits: u32) -> Result<(), TranscriptError>;

    /// Check two elements are equal, refusing with the given error when they differ.
    ///
    /// # Errors
    ///
    /// Returns the error when the two differ and the verifier checks values.
    fn ensure_eq<Er>(&mut self, a: Self::E, b: Self::E, err: impl FnOnce() -> Er) -> Result<(), Er>;

    /// Check the whole proof was read.
    ///
    /// # Errors
    ///
    /// Returns an error when the proof holds data past what was read and the verifier checks values.
    fn check_eof(&mut self) -> Result<(), TranscriptError>;

    /// Mark the prover messages read from now on as sent under one-time-pad keys, or not.
    ///
    /// - A verifier of values reads a padded scalar as it is.
    /// - A verifier that records a zero-knowledge proof's checks holds it as its value plus an unknown key.
    ///
    /// By default the section is not tracked.
    fn set_hidden(&mut self, hidden: bool) {
        let _ = hidden;
    }

    /// Whether the prover messages read next were sent under one-time-pad keys.
    ///
    /// The opening of a hiding commitment reveals its claim exactly when it was hidden.
    fn is_hidden(&self) -> bool {
        false
    }

    /// Start a named stage of the verifier.
    ///
    /// A verifier that records failed checks reports them under the active stages.
    /// The caller must evaluate the stage's result, end the stage, then propagate errors.
    /// A panicking body leaves the stage active.
    fn begin_scope(&mut self, stage: Stage);

    /// End the most recently started stage.
    fn end_scope(&mut self);

    /// The next `n` prover messages.
    ///
    /// # Errors
    ///
    /// Returns an error past the end of the proof.
    fn prover_messages(&mut self, n: usize) -> Result<Vec<Self::E>, TranscriptError> {
        (0..n).map(|_| self.prover_message()).collect()
    }

    /// `n` verifier messages.
    fn verifier_messages(&mut self, n: usize) -> Vec<Self::E> {
        (0..n).map(|_| self.verifier_message()).collect()
    }

    /// Read one sumcheck round's polynomial of `n_coeffs` coefficients, constant first.
    ///
    /// The prover sent all of them but the one the round's claim fixes, which is rebuilt here.
    ///
    /// - Plain round, `eq` absent: `h(0) + h(1) = claim` fixes `c_1 = claim + sum_{i>=2} c_i`.
    /// - Round with its eq weight `r = eq` factored out: `claim = c_0 + r sum_{i>=1} c_i` fixes `c_0`.
    ///
    /// Either way the fixed coefficient is a sum, and no inverse is needed.
    ///
    /// # Errors
    ///
    /// Returns an error past the end of the proof.
    ///
    /// # Panics
    ///
    /// Panics on fewer than two coefficients.
    fn read_round(
        &mut self,
        n_coeffs: usize,
        claim: Self::E,
        eq: Option<Self::E>,
    ) -> Result<Vec<Self::E>, TranscriptError> {
        assert!(n_coeffs >= 2, "a round polynomial has at least two coefficients");

        // Read the sent coefficients, then put the claim in the fixed one's place.
        let fixed = eq.map_or(RoundWeight::Plain, |_| RoundWeight::Eq).fixed_index();
        let mut coeffs = self.prover_messages(n_coeffs - 1)?;
        coeffs.insert(fixed, claim);

        // The coefficients past the fixed one, summed.
        let zero = self.zero();
        let tail = coeffs[fixed + 1..].iter().fold(zero, |acc, &c| self.add(acc, c));

        // c_1 = claim + sum_{i>=2} c_i, or c_0 = claim + r sum_{i>=1} c_i.
        coeffs[fixed] = match eq {
            None => self.add(claim, tail),
            Some(r) => self.mul_add(r, tail, claim),
        };
        Ok(coeffs)
    }
}

/// Which coefficient of a sumcheck round's polynomial the round's claim fixes, so that the prover never sends it.
///
/// The fixed coefficient is a function of the claim and the sent ones, so binding it would add nothing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RoundWeight {
    /// A plain round, `h(0) + h(1) = claim`: the claim fixes the linear coefficient.
    Plain,
    /// A round with its eq weight `r` factored out, `claim = c_0 + r sum_{i>=1} c_i`: the claim fixes the constant.
    Eq,
}

impl RoundWeight {
    /// The index of the coefficient the claim fixes.
    pub(crate) const fn fixed_index(self) -> usize {
        match self {
            Self::Plain => 1,
            Self::Eq => 0,
        }
    }
}

/// Plain `F192` arithmetic, for the prover's share of code the verifiers also run.
#[derive(Clone, Copy, Debug, Default)]
pub struct Native;

impl Arith for Native {
    type E = F192;

    fn constant(&mut self, c: F192) -> F192 {
        c
    }

    fn mul_add(&mut self, a: F192, b: F192, d: F192) -> F192 {
        a * b + d
    }

    fn add(&mut self, a: F192, d: F192) -> F192 {
        a + d
    }

    fn mul_const_add(&mut self, a: F192, c: F192, d: F192) -> F192 {
        a * c + d
    }

    fn inv(&mut self, a: F192) -> F192 {
        a.inv()
    }

    fn frobenius2(&mut self, a: F192) -> F192 {
        a.frobenius().frobenius()
    }
}

impl PublicMle for Native {
    fn public_mle(&mut self, values: &[F64], point: &[F192]) -> F192 {
        mle_eval_par(values, point)
    }
}

/// The native verifier computes in the clear, as the prover does.
impl Arith for VerifierState<'_> {
    type E = F192;

    fn constant(&mut self, c: F192) -> F192 {
        Native.constant(c)
    }

    fn mul_add(&mut self, a: F192, b: F192, d: F192) -> F192 {
        Native.mul_add(a, b, d)
    }

    fn add(&mut self, a: F192, d: F192) -> F192 {
        Native.add(a, d)
    }

    fn mul_const_add(&mut self, a: F192, c: F192, d: F192) -> F192 {
        Native.mul_const_add(a, c, d)
    }

    fn inv(&mut self, a: F192) -> F192 {
        Native.inv(a)
    }

    fn frobenius2(&mut self, a: F192) -> F192 {
        Native.frobenius2(a)
    }
}

impl PublicMle for VerifierState<'_> {
    fn public_mle(&mut self, values: &[F64], point: &[F192]) -> F192 {
        Native.public_mle(values, point)
    }
}

impl Verifier for VerifierState<'_> {
    fn prover_message(&mut self) -> Result<F192, TranscriptError> {
        Self::prover_message(self)
    }

    fn verifier_message(&mut self) -> F192 {
        Self::verifier_message(self)
    }

    fn check_pow(&mut self, bits: u32) -> Result<(), TranscriptError> {
        Self::check_pow(self, bits)
    }

    fn ensure_eq<Er>(&mut self, a: F192, b: F192, err: impl FnOnce() -> Er) -> Result<(), Er> {
        if a == b { Ok(()) } else { Err(err()) }
    }

    fn check_eof(&mut self) -> Result<(), TranscriptError> {
        Self::check_eof(self)
    }

    #[inline]
    fn begin_scope(&mut self, _: Stage) {}

    #[inline]
    fn end_scope(&mut self) {}

    fn set_hidden(&mut self, hidden: bool) {
        Self::set_hidden(self, hidden);
    }

    fn is_hidden(&self) -> bool {
        Self::is_hidden(self)
    }
}
