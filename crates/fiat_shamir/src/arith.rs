//! The verifier's arithmetic and transcript, written once for the native verifier and for its replay in rows.
//!
//! Code generic over these traits never reads a value: it takes the same steps whatever the proof holds.
//!
//! - Natively an element is an `F192`, a read comes off the proof, and a failed equality is an error.
//! - In rows an element is a wire, a read is a free wire bound by a hash row, and an equality joins two wires.

use primitives::{Field, HasFrobenius, PrimeCharacteristicRing};

use crate::transcript::{Challenger, Receiver, TranscriptError, VerifierState};
use primitives::multilinear::mle_eval_par;
use primitives::{F64, F192};

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

    /// The multilinear extension of public `K` words at `point`, lowest coordinate first.
    fn public_mle(&mut self, values: &[F64], point: &[Self::E]) -> Self::E {
        assert_eq!(values.len(), 1 << point.len(), "a column has a word per vertex");
        let eq = self.eq_table(point);
        let zero = self.zero();
        (eq.iter().zip(values)).fold(zero, |acc, (&e, &v)| self.mul_const_add(e, F192::from(v), acc))
    }

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
        factors.iter().fold(one, |acc, &f| self.mul(acc, f))
    }

    /// `sum_i c_i x^i`, by Horner, constant first.
    fn poly_eval(&mut self, coeffs: &[Self::E], x: Self::E) -> Self::E {
        let zero = self.zero();
        coeffs.iter().rev().fold(zero, |acc, &c| self.mul_add(acc, x, c))
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
        x.iter().zip(y).fold(one, |acc, (&u, &v)| {
            let s = self.add(u, v);
            self.times_one_plus(acc, s)
        })
    }

    /// `eq(bits, point)` for public bits, lowest first: `prod_j (bit_j ? z_j : 1 + z_j)`.
    ///
    /// The product runs from the highest coordinate down.
    /// Why: selectors of nearby offsets share their high bits, so in rows their common partial products are made once.
    fn eq_bits(&mut self, bits: usize, point: &[Self::E]) -> Self::E {
        let one = self.one();
        (point.iter().enumerate()).rev().fold(one, |acc, (j, &z)| {
            if bits >> j & 1 == 1 {
                self.mul(acc, z)
            } else {
                self.times_one_plus(acc, z)
            }
        })
    }

    /// `eq(point, x)` for every vertex `x`, lowest coordinate first.
    fn eq_table(&mut self, point: &[Self::E]) -> Vec<Self::E> {
        self.eq_table_prefix(point, 1 << point.len())
    }

    /// `eq(point, x)` for the first `len` vertices `x`, lowest coordinate first, with no work for the others.
    fn eq_table_prefix(&mut self, point: &[Self::E], len: usize) -> Vec<Self::E> {
        assert!(len <= 1 << point.len(), "a prefix of the cube");
        let mut table = vec![self.one()];
        for (i, &r) in point.iter().enumerate() {
            let need = len.min(2 << i);
            let high: Vec<Self::E> = table[..need.saturating_sub(table.len())]
                .iter()
                .map(|&v| self.mul(v, r))
                .collect();
            for v in &mut table {
                *v = self.times_one_plus(*v, r);
            }
            table.extend(high);
        }
        table.truncate(len);
        table
    }

    /// The multilinear extension of `values` at `point`, folding the lowest coordinate first.
    fn mle(&mut self, values: &[Self::E], point: &[Self::E]) -> Self::E {
        assert_eq!(values.len(), 1 << point.len(), "a value per vertex");
        let mut folded = values.to_vec();
        for &x in point {
            folded = folded.chunks(2).map(|pair| self.interp(pair[0], pair[1], x)).collect();
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
        (point.iter().enumerate()).fold(base, |acc, (i, &z)| {
            self.mul_const_add(z, F192::from(F64::new(1 << (i as u32 + shift))), acc)
        })
    }
}

/// A verifier: arithmetic, a transcript to read and sample, and equalities to check.
pub trait Verifier: Arith {
    /// The next scalar of the stream, bound into the transcript.
    ///
    /// # Errors
    ///
    /// Returns an error past the end of the stream.
    fn next_scalar(&mut self) -> Result<Self::E, TranscriptError>;

    /// A sumcheck round's coefficients, constant first, one of them fixed by the claim.
    ///
    /// - With an eq weight `r` the claim fixes the constant: `c_0 = claim + r·sum_{i>=1} c_i`.
    /// - Without, it fixes the linear coefficient: `c_1 = claim + sum_{i>=2} c_i`.
    ///
    /// # Errors
    ///
    /// Returns an error past the end of the stream.
    fn next_round_poly(
        &mut self,
        n_coeffs: usize,
        claim: Self::E,
        eq: Option<Self::E>,
    ) -> Result<Vec<Self::E>, TranscriptError>;

    /// A challenge.
    fn sample(&mut self) -> Self::E;

    /// Read a nonce, check it clears a proof of work of the given bits, then bind it.
    ///
    /// # Errors
    ///
    /// Returns an error past the end of the stream, or on a nonce short of the work when the verifier checks values.
    fn grind_check(&mut self, bits: u32) -> Result<(), TranscriptError>;

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
    fn finish(&mut self) -> Result<(), TranscriptError>;

    /// Run `f` as a named stage of the verifier.
    ///
    /// A verifier that records its failed checks rather than refusing reports each under its stages' names.
    fn scope<T>(&mut self, name: &'static str, f: impl FnOnce(&mut Self) -> T) -> T {
        let _ = name;
        f(self)
    }

    /// The next `n` scalars.
    ///
    /// # Errors
    ///
    /// Returns an error past the end of the stream.
    fn next_scalars(&mut self, n: usize) -> Result<Vec<Self::E>, TranscriptError> {
        (0..n).map(|_| self.next_scalar()).collect()
    }

    /// `n` challenges.
    fn sample_vec(&mut self, n: usize) -> Vec<Self::E> {
        (0..n).map(|_| self.sample()).collect()
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
        if a.is_zero() { F192::ZERO } else { a.invert_or_zero() }
    }

    fn frobenius2(&mut self, a: F192) -> F192 {
        a.frobenius().frobenius()
    }

    fn public_mle(&mut self, values: &[F64], point: &[F192]) -> F192 {
        mle_eval_par(values, point)
    }
}

impl Arith for VerifierState<'_> {
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
        if a.is_zero() { F192::ZERO } else { a.invert_or_zero() }
    }

    fn frobenius2(&mut self, a: F192) -> F192 {
        a.frobenius().frobenius()
    }

    fn public_mle(&mut self, values: &[F64], point: &[F192]) -> F192 {
        mle_eval_par(values, point)
    }
}

impl Verifier for VerifierState<'_> {
    fn next_scalar(&mut self) -> Result<F192, TranscriptError> {
        Receiver::next_scalar(self)
    }

    fn next_round_poly(
        &mut self,
        n_coeffs: usize,
        claim: F192,
        eq: Option<F192>,
    ) -> Result<Vec<F192>, TranscriptError> {
        Receiver::next_round_poly(self, n_coeffs, claim, eq)
    }

    fn sample(&mut self) -> F192 {
        Challenger::sample(self)
    }

    fn grind_check(&mut self, bits: u32) -> Result<(), TranscriptError> {
        Receiver::grind_check(self, bits)
    }

    fn ensure_eq<Er>(&mut self, a: F192, b: F192, err: impl FnOnce() -> Er) -> Result<(), Er> {
        if a == b { Ok(()) } else { Err(err()) }
    }

    fn finish(&mut self) -> Result<(), TranscriptError> {
        VerifierState::finish(self)
    }
}
