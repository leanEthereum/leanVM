// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! The lincheck: the zerocheck's claims on `a = A z`, `b = B z` and `c = z`, reduced to claims on `z` alone.
//!
//! The matrices are block-diagonal, one base matrix repeated over the instances:
//!
//! ```text
//!     A = I_(2^n_log) (x) A_0          the row and column indices split as (inner, outer)
//!     A^(i, x) = A_0^(i_inner, x_inner) * eq(i_outer, x_outer)
//! ```
//!
//! So a claim `v = a^(x) = sum_i z(i) A^(i, x)` collapses its outer sum by the eq identity:
//!
//! ```text
//!     v = sum_(i_inner) A_0^(i_inner, x_inner) * z^(i_inner, x_outer)
//! ```
//!
//! That is `2^k_log` terms, `z^(., x_outer)` being the witness partially folded at the outer half of the point.
//!
//! The zerocheck leaves `a`, `b` and `c` at one point, so the witness is folded once.
//! The prover forms the column marginal of `A + alpha B + alpha^2 I`, the constant wire pinned at `alpha^3`.
//! A product sumcheck then reduces its inner product with the folded witness to the `2^k_skip` slices of `z`.
//! Ring switching binds those slices to the commitment.
//!
//! Several circuits share one `alpha` and one product sumcheck: circuit `f`'s identity takes the weight `alpha^(4f)`.
//! Every circuit binds its top inner coordinate in the first round.
//! A circuit done early adds the line `X u` its lifting variable makes.
//! That line reaches only the coefficient the claim fixes.
//!
//! The first `k_skip` inner variables are the zerocheck's univariate skip: one coordinate `z_skip` stands for them.
//! Its eq factor is the Lagrange basis on `phi_8(0), .., phi_8(2^k_skip - 1)` at `z_skip`.
//! The other coordinates stay multilinear.

use fiat_shamir::arith::{Arith, Native, Verifier};
use fiat_shamir::transcript::{Challenger, ProverState, TranscriptError, Transmitter};
use pcs::ring_switch::SliceClaim;
use primitives::field::F192;
use primitives::multilinear::{eq_table, inner_product, skip_lagrange_weights};
use thiserror::Error;

use crate::reduction::Shape;
use crate::zerocheck::{SkipDomain, ZerocheckReplay};
use sumcheck::ProductSumcheck;

mod fold;
mod sumcheck;

/// A circuit's linear maps as the lincheck reads them, never as matrices.
///
/// The one implementation walks its gate list: backwards for the prover's marginal, forwards for the verifier's form.
pub trait LincheckCircuit: Sync {
    /// The columns of the base matrices: `2^k_log`.
    fn n_cols(&self) -> usize;

    /// The batched column marginal, `(eq^T A_0)[c] + alpha (eq^T B_0)[c]` for every column `c`.
    fn fold_alpha_batched(&self, alpha: F192, eq_inner: &[F192]) -> Vec<F192>;

    /// The column of the constant wire.
    ///
    /// The lincheck pins it to one at `alpha^3`, at no transcript cost.
    /// That closes the all-zero witness, and requires the wire to be one in every instance, padding included.
    fn const_pin_col(&self) -> usize;

    /// The batched bilinear form `u^T A_0 w + alpha u^T B_0 w`, without the length-`2^k_log` marginal.
    ///
    /// A circuit that walks its gates answers in time linear in the circuit.
    /// `None` lets the verifier fall back on the marginal.
    fn bilinear_form(&self, _alpha: F192, _u: &[F192], _w: &[F192]) -> Option<F192> {
        None
    }
}

/// A claim point with a univariate-skip coordinate.
///
/// `1 + (k_log - k_skip) + n_log` coordinates in all, the shape the zerocheck's claims come at.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct QuirkyPoint {
    /// The skip challenge, standing for the first `k_skip` inner variables.
    pub z_skip: F192,

    /// The other inner coordinates, low variable first.
    pub x_inner_rest: Vec<F192>,

    /// The outer coordinates, which index the instances.
    pub x_outer: Vec<F192>,
}

/// The lincheck's output on one circuit: the bit slices of `z` at the inner point `r_inner_rest`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LincheckClaim {
    /// The inner coordinates the product sumcheck drew, low variable first.
    pub r_inner_rest: Vec<F192>,

    /// The `2^k_skip` bit slices of `z` at `(r_inner_rest, x_outer)`, pinned by the terminal identity.
    ///
    /// They are the ring switch's claim too, so the opening reuses them rather than receive them again.
    pub s_hat_v: Vec<F192>,
}

impl LincheckClaim {
    /// The claim on the packed witness: the lincheck's inner coordinates, then the zerocheck's outer ones.
    pub(crate) fn slice_claim(self, x_outer: &[F192]) -> SliceClaim {
        let mut suffix_point = self.r_inner_rest;
        suffix_point.extend_from_slice(x_outer);
        SliceClaim {
            suffix_point,
            s_hat_v: self.s_hat_v,
        }
    }
}

/// Why the lincheck verifier refuses.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum LincheckError {
    /// The circuit's column count is not `2^k_log`.
    #[error("the circuit has {got} columns, and lincheck needs {expected}")]
    BadNCols { expected: usize, got: usize },

    /// More skipped variables than the matrix's inner dimension has.
    #[error("k_skip {k_skip} exceeds k_log {k_log}")]
    KSkipExceedsKLog { k_skip: usize, k_log: usize },

    /// The sumcheck's final claim is not the batched `A`, `B`, `C` evaluation.
    #[error("the sumcheck's final claim does not match the matrices")]
    SumcheckMismatch,

    /// The proof stream is malformed.
    #[error(transparent)]
    Transcript(#[from] TranscriptError),
}

/// The eq table of the inner half of a quirky point, the skip's Lagrange weights on the low index bits.
///
/// ```text
///     out[i_skip + i_rest 2^k_skip] = L_(i_skip)(z_skip) * eq(x_inner_rest, i_rest)
/// ```
pub fn build_quirky_eq_table(z_skip: F192, x_inner_rest: &[F192], k_skip: usize) -> Vec<F192> {
    outer_product(&eq_table(x_inner_rest), &skip_lagrange_weights(k_skip, z_skip))
}

/// `out[i_lo + i_hi lo.len()] = lo[i_lo] * hi[i_hi]`: `lo` varies fastest.
fn outer_product(hi: &[F192], lo: &[F192]) -> Vec<F192> {
    // Sized up front: a flattened iterator cannot report its length.
    let mut out = Vec::with_capacity(hi.len() * lo.len());
    for &h in hi {
        out.extend(lo.iter().map(|&l| l * h));
    }
    out
}

/// The weights of a batch's circuits: circuit `f`'s `A`, `B`, `C` and pin terms ride `alpha^(4f)` to `alpha^(4f + 3)`.
fn circuit_weights(alpha: F192, n: usize) -> Vec<F192> {
    primitives::field::powers(alpha.square().square(), n)
}

/// One circuit's witness in a batched lincheck, and the point its zerocheck claims are at.
#[derive(Clone, Copy)]
pub(crate) struct LincheckInput<'a> {
    /// The witness, instance-major, packed 64 bits a word.
    pub z: &'a [u64],

    /// The base-two logarithm of the witness's bits.
    pub m: usize,

    /// The base-two logarithm of the bits per instance.
    pub k_log: usize,

    /// The inner variables the skip stands for.
    pub k_skip: usize,

    /// The bits of an instance before its zero padding.
    pub useful_bits: usize,

    /// The circuit's matrices.
    pub circuit: &'a dyn LincheckCircuit,

    /// The zerocheck's point.
    pub x_ab: &'a QuirkyPoint,
}

/// One circuit's share of the batched product sumcheck.
struct CircuitProver {
    /// Its marginal and folded witness.
    sumcheck: ProductSumcheck,
    /// Its rounds: its inner variables past the skip.
    rounds: usize,
    /// Its running claim.
    running: F192,
    /// The challenges of the rounds since its last, multiplied.
    lift: F192,
    /// Its next round's `(q(1), q(inf))`.
    next: (F192, F192),
}

impl CircuitProver {
    /// The circuit's marginal and folded witness, and its first round.
    fn new(input: &LincheckInput<'_>, alpha: F192) -> Self {
        let LincheckInput {
            z,
            m,
            k_log,
            k_skip,
            useful_bits,
            circuit,
            x_ab,
        } = *input;
        let k = 1usize << k_log;
        assert!(m >= k_log);
        assert!(k_skip <= k_log, "the skip fits inside an instance");
        assert!(useful_bits <= k, "{useful_bits} useful bits in an instance of {k}");
        assert_eq!(circuit.n_cols(), k);
        assert_eq!(x_ab.x_inner_rest.len(), k_log - k_skip);
        assert_eq!(x_ab.x_outer.len(), m - k_log);

        // Phase 1: the batched marginal of `A` and `B`, through the circuit.
        let eq_inner =
            tracing::info_span!("Eq table").in_scope(|| build_quirky_eq_table(x_ab.z_skip, &x_ab.x_inner_rest, k_skip));
        let mut comb = tracing::info_span!("Fold circuit").in_scope(|| circuit.fold_alpha_batched(alpha, &eq_inner));

        // Phase 2: `C = I` at `alpha^2`, so its marginal is the row weights themselves.
        // That puts the `c` claim at the same point as `a` and `b`, for one pass over a length-k vector.
        let alpha_sq = alpha.square();
        for (c, e) in comb.iter_mut().zip(&eq_inner) {
            *c += alpha_sq * *e;
        }

        // Phase 3: the constant-wire pin at `alpha^3`, whose eq vector is one-hot.
        comb[circuit.const_pin_col()] += alpha_sq * alpha;

        // Phase 4: the witness folded at the outer half of the point.
        let z = tracing::info_span!("Partial fold")
            .in_scope(|| fold::partial_fold(z, k_log, useful_bits, &eq_table(&x_ab.x_outer)));

        // Phase 5: the only standalone round; every later one falls out of binding the one before.
        let sumcheck = ProductSumcheck::new(comb, z);
        let rounds = k_log - k_skip;
        let next = if rounds > 0 {
            sumcheck.round()
        } else {
            (F192::ZERO, F192::ZERO)
        };
        Self {
            running: sumcheck.claim(),
            sumcheck,
            rounds,
            lift: F192::ONE,
            next,
        }
    }

    /// The round's coefficients; `q(0) + q(1) = claim` lets the wire drop the linear one.
    fn message(&self) -> [F192; 3] {
        let (e1, einf) = self.next;
        let e0 = self.running + e1;
        [e0, e0 + e1 + einf, einf]
    }

    /// Bind round `t` at `r`.
    fn bind(&mut self, t: usize, r: F192) {
        self.running = primitives::multilinear::poly_eval(&self.message(), r);
        if t + 1 < self.rounds {
            self.next = self.sumcheck.bind_and_round(r);
        } else {
            self.sumcheck.bind_last(r);
        }
    }
}

/// The lincheck prover, for a batch of circuits under one `alpha` and one sumcheck (doc/leanvm Annex C).
///
/// - Circuit `f`'s identity takes the weight `alpha^(4f)`.
/// - Its product sumcheck binds its `k_log - k_skip` inner coordinates top first, every circuit from the first round.
/// - A circuit done before a round adds the line `X u`, `u` its final claim times the challenges since.
///
/// After the rounds, each circuit sends its folded witness, its `2^k_skip` slices.
/// Then it sends the value of its matrices' form.
/// The verifier leaves that value as a claim on the circuit.
pub(crate) fn prove(inputs: &[LincheckInput<'_>], ps: &mut ProverState) -> Vec<LincheckClaim> {
    // Phase 1: `alpha` batches each circuit's `a`, `b`, `c` checks and pin, and the circuits.
    let alpha = ps.sample();
    let weights = circuit_weights(alpha, inputs.len());
    let mut provers: Vec<CircuitProver> = inputs.iter().map(|input| CircuitProver::new(input, alpha)).collect();

    // Phase 2: the batched product sumcheck, a done circuit lifted by the variables it lacks.
    let span = tracing::info_span!("Sumcheck").entered();
    let n_rounds = provers.iter().map(|p| p.rounds).max().expect("a batch has a circuit");
    let mut r_rounds = Vec::with_capacity(n_rounds);
    for t in 0..n_rounds {
        let mut message = [F192::ZERO; 3];
        for (prover, &weight) in provers.iter().zip(&weights) {
            let own = if t < prover.rounds {
                prover.message()
            } else {
                [F192::ZERO, prover.lift * prover.running, F192::ZERO]
            };
            for (m, c) in message.iter_mut().zip(own) {
                *m += weight * c;
            }
        }
        ps.add_round_poly(&message, false);
        let r = ps.sample();
        r_rounds.push(r);
        for prover in &mut provers {
            if t < prover.rounds {
                prover.bind(t, r);
            } else {
                prover.lift *= r;
            }
        }
    }
    drop(span);

    // Phase 3: each circuit's slices, then its matrices' form: its terminal value less the identity's closed terms.
    let alpha_sq = alpha.square();
    let beta = alpha_sq * alpha;
    (provers.into_iter().zip(inputs))
        .map(|(prover, input)| {
            // The rounds bind the top bit first, so the claim's coordinates read them backwards.
            let claim = LincheckClaim {
                r_inner_rest: r_rounds[..prover.rounds].iter().rev().copied().collect(),
                s_hat_v: prover.sumcheck.into_z(),
            };
            let (domain, x_ab) = (SkipDomain::new(input.k_skip), input.x_ab);
            let vanishing = domain.vanishing(&mut Native, x_ab.z_skip);
            let mut closed = ClosedTerms::new(
                &mut Native,
                domain,
                alpha_sq,
                beta,
                x_ab.z_skip,
                vanishing,
                prover.rounds,
            );
            let value = closed.add_to(
                &mut Native,
                prover.running,
                input.circuit.const_pin_col(),
                &x_ab.x_inner_rest,
                &claim.r_inner_rest,
                &claim.s_hat_v,
            );
            ps.add_scalars(&claim.s_hat_v);
            ps.add_scalars(&[value]);
            claim
        })
        .collect()
}

/// Replay a batched lincheck up to the circuits' matrices.
///
/// The replay walks the transcript in lockstep with the prover, through the product sumcheck.
/// The batch's final claim is each circuit's terminal identity, times its weight.
/// A circuit's identity is also lifted by the challenges of the rounds it sat out.
/// A circuit's identity is its closed terms, plus the value of its matrices' form, which the prover sends.
///
/// That value is returned as a claim for whoever holds the circuit to settle.
/// Nothing is absorbed after the claims' challenges, so settling them later is the same check.
///
/// # Errors
///
/// A circuit narrower than the skip, a malformed stream, or a final claim the circuits' terms miss.
pub(crate) fn verify_deferred<V: Verifier>(
    domain: SkipDomain,
    zc: &ZerocheckReplay<V::E>,
    shapes: &[Shape],
    v: &mut V,
) -> Result<Vec<MatrixClaim<V::E>>, LincheckError> {
    let k_skip = domain.k_skip();
    if let Some(shape) = shapes.iter().find(|shape| shape.k_log < k_skip) {
        return Err(LincheckError::KSkipExceedsKLog {
            k_skip,
            k_log: shape.k_log,
        });
    }
    let rests: Vec<usize> = shapes.iter().map(|shape| shape.k_log - k_skip).collect();

    // Phase 1: the target the batched claims and pins set, circuit `f` at `alpha^(4f)`, its pin's target one.
    let alpha = v.sample();
    let alpha_sq = v.square(alpha);
    let beta = v.mul(alpha_sq, alpha);
    let alpha_4 = v.square(alpha_sq);
    let weights = v.powers(alpha_4, shapes.len());
    let mut running = v.zero();
    for (&[a, b, c], &weight) in zc.evals.iter().zip(&weights) {
        let own = v.mul_add(alpha, b, a);
        let own = v.mul_add(alpha_sq, c, own);
        let own = v.add(own, beta);
        running = v.mul_add(weight, own, running);
    }

    // Phase 2: the rounds; `q(1) = claim + q(0)` in characteristic 2, so it never rides the wire.
    let n_rounds = rests.iter().copied().max().expect("a batch has a circuit");
    let mut r_rounds = Vec::with_capacity(n_rounds);
    for _ in 0..n_rounds {
        let q = v.next_round_poly(3, running, None)?;
        let challenge = v.sample();
        running = v.poly_eval(&q, challenge);
        r_rounds.push(challenge);
    }

    // What a circuit of `rest` rounds waits on: the challenges of the rounds after its own.
    let mut waits = vec![v.one(); n_rounds + 1];
    for i in (0..n_rounds).rev() {
        waits[i] = v.mul(waits[i + 1], r_rounds[i]);
    }
    let mut closed = ClosedTerms::new(v, domain, alpha_sq, beta, zc.z, zc.vanishing, n_rounds);

    // Phase 3: each circuit's slices and form value, in circuit order.
    // A circuit's terminal value is its matrices' bilinear form plus its closed terms.
    let mut total = v.zero();
    let mut claims = Vec::with_capacity(shapes.len());
    for ((shape, &rest), &weight) in shapes.iter().zip(&rests).zip(&weights) {
        let z_partial = v.next_scalars(domain.size())?;
        let value = v.next_scalar()?;
        let r_inner_rest: Vec<V::E> = r_rounds[..rest].iter().rev().copied().collect();
        let x_inner_rest = &zc.mlv_challenges[..rest];
        let own = closed.add_to(v, value, shape.const_pin_col, x_inner_rest, &r_inner_rest, &z_partial);
        let lift = v.mul(weight, waits[rest]);
        total = v.mul_add(lift, own, total);
        claims.push(MatrixClaim {
            form: MatrixForm {
                alpha,
                z_skip: zc.z,
                x_inner_rest: x_inner_rest.to_vec(),
                r_inner_rest,
                s_hat_v: z_partial,
            },
            value,
        });
    }
    v.ensure_eq(total, running, || LincheckError::SumcheckMismatch)?;
    Ok(claims)
}

/// The terms of a circuit's terminal identity that its matrices do not fix, at one batch's challenges.
///
/// ```text
///     alpha^3 w_col[pin] + alpha^2 eq(x_inner_rest, r_inner_rest) <lambda(z_skip), s_hat_v>
/// ```
///
/// - `w_col[pin]` is the constant wire's slice times the eq weight of its inner index.
/// - The `C` term is `<eq_inner, w_col>`, by the tensor structure of both sides.
///
/// The skip weights' inverses at `z_skip` serve every circuit.
/// `eq(x_inner_rest, r_inner_rest)` serves every circuit of one inner length.
struct ClosedTerms<E> {
    domain: SkipDomain,
    alpha_sq: E,
    beta: E,
    inverses: Vec<E>,
    scale: E,
    eq_inner: Vec<Option<E>>,
}

impl<E: Copy> ClosedTerms<E> {
    /// The terms at the batch's `alpha^2`, `alpha^3` and skip challenge.
    ///
    /// The circuits have at most `max_rest` inner rounds.
    fn new<A: Arith<E = E>>(
        a: &mut A,
        domain: SkipDomain,
        alpha_sq: E,
        beta: E,
        z_skip: E,
        vanishing: E,
        max_rest: usize,
    ) -> Self {
        let inverses = domain.inverses(a, z_skip);
        let scale = domain.lagrange_scale(a, vanishing);
        Self {
            domain,
            alpha_sq,
            beta,
            inverses,
            scale,
            eq_inner: vec![None; max_rest + 1],
        }
    }

    /// `value` plus the closed terms of a circuit whose constant wire is column `pin`, at its claim.
    fn add_to<A: Arith<E = E>>(
        &mut self,
        a: &mut A,
        value: E,
        pin: usize,
        x_inner_rest: &[E],
        r_inner_rest: &[E],
        s_hat_v: &[E],
    ) -> E {
        // The pin: the constant wire's slice, at the eq weight of its inner index.
        let k_skip = self.domain.k_skip();
        let eq_pin = a.eq_bits(pin >> k_skip, r_inner_rest);
        let pin_term = a.mul(s_hat_v[pin & (self.domain.size() - 1)], eq_pin);
        let own = a.mul_add(self.beta, pin_term, value);

        // The `C` term: the slices' Lagrange sum at the skip challenge, times the inner eq.
        let slices = SkipDomain::lagrange_with(a, self.scale, &self.inverses, s_hat_v);
        let eq = *self.eq_inner[r_inner_rest.len()].get_or_insert_with(|| a.eq_eval(x_inner_rest, r_inner_rest));
        let c_term = a.mul(eq, slices);
        a.mul_add(self.alpha_sq, c_term, own)
    }
}

/// The share of a lincheck's terminal identity that only the circuit's matrices fix.
///
/// ```text
///     u^T (A_0 + alpha B_0) w,       u = quirky_eq(z_skip, x_inner_rest),   w = eq(r_inner_rest, .) (x) s_hat_v
/// ```
///
/// - `u` are the row weights at the inner half of the zerocheck point.
/// - `w` are the column weights of the output claim.
///
/// Its elements are values, or whatever a verifier holds them as.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixForm<E = F192> {
    /// The challenge batching the two matrices.
    pub alpha: E,

    /// The zerocheck's skip challenge, the first row coordinate.
    pub z_skip: E,

    /// The zerocheck's other inner coordinates, the rest of the row point.
    pub x_inner_rest: Vec<E>,

    /// The output claim's inner coordinates, the column point.
    pub r_inner_rest: Vec<E>,

    /// The output claim's `2^k_skip` bit slices.
    pub s_hat_v: Vec<E>,
}

impl<E: Copy> MatrixForm<E> {
    /// The same form, each element mapped by `f`.
    pub fn map<T>(&self, mut f: impl FnMut(E) -> T) -> MatrixForm<T> {
        MatrixForm {
            alpha: f(self.alpha),
            z_skip: f(self.z_skip),
            x_inner_rest: self.x_inner_rest.iter().map(|&x| f(x)).collect(),
            r_inner_rest: self.r_inner_rest.iter().map(|&x| f(x)).collect(),
            s_hat_v: self.s_hat_v.iter().map(|&x| f(x)).collect(),
        }
    }
}

impl MatrixForm {
    /// The form against a circuit's matrices.
    ///
    /// A circuit that walks its gates evaluates it in time linear in the circuit.
    /// Any other folds its matrices into the batched marginal, then takes one inner product.
    pub fn evaluate(&self, circuit: &dyn LincheckCircuit) -> F192 {
        let k_skip = self.s_hat_v.len().ilog2() as usize;
        let eq_inner = build_quirky_eq_table(self.z_skip, &self.x_inner_rest, k_skip);
        let w_col = outer_product(&eq_table(&self.r_inner_rest), &self.s_hat_v);
        circuit
            .bilinear_form(self.alpha, &eq_inner, &w_col)
            .unwrap_or_else(|| inner_product(&circuit.fold_alpha_batched(self.alpha, &eq_inner), &w_col))
    }
}

/// What the deferred replay leaves to the circuit: the terminal identity holds exactly when the form takes the value.
///
/// Its elements are values, or whatever a verifier holds them as.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixClaim<E = F192> {
    /// The form, at the replay's challenges.
    pub form: MatrixForm<E>,

    /// The value the form must take.
    pub value: E,
}

impl MatrixClaim {
    /// Settle the claim against a circuit's matrices.
    ///
    /// # Errors
    ///
    /// The circuit's width if it is not the form's, and a sumcheck mismatch when the form misses the value.
    pub fn check(&self, circuit: &dyn LincheckCircuit) -> Result<(), LincheckError> {
        // The form's column point and slices fix the circuit's width.
        let n_cols = self.form.s_hat_v.len() << self.form.r_inner_rest.len();
        if circuit.n_cols() != n_cols {
            return Err(LincheckError::BadNCols {
                expected: n_cols,
                got: circuit.n_cols(),
            });
        }
        // The terminal identity holds exactly when the form takes the claimed value.
        if self.form.evaluate(circuit) == self.value {
            Ok(())
        } else {
            Err(LincheckError::SumcheckMismatch)
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use fiat_shamir::transcript::{ProofTranscript, VerifierState};
    use primitives::test_util::Rng;

    use super::*;

    const LABEL: &[u8] = b"flock-test-v0";

    /// The constant-one column the tests pin; the witness carries a one there in every instance.
    const PIN_COL: usize = 0;

    /// Pack Boolean witness bits instance-major, 64 a word, low bit first.
    fn pack_z(bits: &[bool]) -> Vec<u64> {
        (bits.chunks(64))
            .map(|word| word.iter().rev().fold(0u64, |acc, &bit| acc << 1 | u64::from(bit)))
            .collect()
    }

    /// A sparse Boolean matrix by rows, the one place a matrix still exists.
    #[derive(Clone)]
    struct SparseMatrix {
        rows: Vec<Vec<usize>>,
    }

    impl SparseMatrix {
        /// `nnz` distinct random entries of a `k x k` matrix.
        fn random(k: usize, nnz: usize, rng: &mut Rng) -> Self {
            let mut rows = vec![Vec::new(); k];
            let mut seen = HashSet::new();
            while seen.len() < nnz {
                let (r, c) = (rng.next_u64() as usize % k, rng.next_u64() as usize % k);
                if seen.insert((r, c)) {
                    rows[r].push(c);
                }
            }
            Self { rows }
        }

        /// `I (x) M` applied to a witness of whole blocks.
        fn apply_blocks(&self, z: &[bool]) -> Vec<bool> {
            let k = self.rows.len();
            (z.chunks_exact(k))
                .flat_map(|block| {
                    self.rows
                        .iter()
                        .map(|row| row.iter().fold(false, |acc, &c| acc ^ block[c]))
                })
                .collect()
        }

        /// `M^T u`, the column marginal.
        fn marginal(&self, u: &[F192]) -> Vec<F192> {
            let mut out = vec![F192::ZERO; self.rows.len()];
            for (row, &w) in self.rows.iter().zip(u) {
                for &c in row {
                    out[c] += w;
                }
            }
            out
        }
    }

    /// A circuit over materialized matrices, by the naive row scatter.
    struct SparseCircuit {
        a_0: SparseMatrix,
        b_0: SparseMatrix,
    }

    impl LincheckCircuit for SparseCircuit {
        fn n_cols(&self) -> usize {
            self.a_0.rows.len()
        }

        fn const_pin_col(&self) -> usize {
            PIN_COL
        }

        fn fold_alpha_batched(&self, alpha: F192, eq_inner: &[F192]) -> Vec<F192> {
            let (a, b) = (self.a_0.marginal(eq_inner), self.b_0.marginal(eq_inner));
            a.iter().zip(&b).map(|(&x, &y)| x + alpha * y).collect()
        }
    }

    /// A random honest instance: matrices, a pinned witness, a point, and the true `a`, `b`, `c` claims.
    struct Fixture {
        m: usize,
        k_log: usize,
        k_skip: usize,
        circuit: SparseCircuit,
        z: Vec<bool>,
        x_ab: QuirkyPoint,
        evals: [F192; 3],
    }

    impl Fixture {
        fn new(m: usize, k_log: usize, k_skip: usize, nnz_per_row: usize, rng: &mut Rng) -> Self {
            let k = 1 << k_log;
            let circuit = SparseCircuit {
                a_0: SparseMatrix::random(k, nnz_per_row * k, rng),
                b_0: SparseMatrix::random(k, nnz_per_row * k, rng),
            };
            // The witness, its constant column one in every instance.
            let mut z = rng.bits(1 << m);
            for block in z.chunks_exact_mut(k) {
                block[PIN_COL] = true;
            }
            let x_ab = QuirkyPoint {
                z_skip: rng.ext(),
                x_inner_rest: rng.ext_vec(k_log - k_skip),
                x_outer: rng.ext_vec(m - k_log),
            };
            let (a, b) = (circuit.a_0.apply_blocks(&z), circuit.b_0.apply_blocks(&z));
            let eval = |f: &[bool]| quirky_eval(f, k_log, k_skip, &x_ab);
            let evals = [eval(&a), eval(&b), eval(&z)];
            Self {
                m,
                k_log,
                k_skip,
                circuit,
                z,
                x_ab,
                evals,
            }
        }

        fn prove(&self) -> (LincheckClaim, ProofTranscript) {
            let packed = pack_z(&self.z);
            let input = LincheckInput {
                z: &packed,
                m: self.m,
                k_log: self.k_log,
                k_skip: self.k_skip,
                useful_bits: 1 << self.k_log,
                circuit: &self.circuit,
                x_ab: &self.x_ab,
            };
            let mut ps = ProverState::from_label(LABEL);
            let claim = prove(&[input], &mut ps).pop().expect("one circuit");
            (claim, ps.into_proof())
        }

        /// The replay at the fixture's point, its matrix claim settled against the circuit.
        fn verify(&self, k_skip: usize, proof: &ProofTranscript) -> Result<LincheckClaim, LincheckError> {
            let domain = SkipDomain::new(k_skip);
            let zc = ZerocheckReplay {
                z: self.x_ab.z_skip,
                vanishing: domain.vanishing(&mut Native, self.x_ab.z_skip),
                mlv_challenges: [&self.x_ab.x_inner_rest[..], &self.x_ab.x_outer].concat(),
                evals: vec![self.evals],
            };
            let shape = Shape {
                k_log: self.k_log,
                const_pin_col: PIN_COL,
            };
            let mut vs = VerifierState::from_label(LABEL, proof);
            let matrices = verify_deferred(domain, &zc, &[shape], &mut vs)?
                .pop()
                .expect("one circuit");
            matrices.check(&self.circuit)?;
            Ok(LincheckClaim {
                r_inner_rest: matrices.form.r_inner_rest,
                s_hat_v: matrices.form.s_hat_v,
            })
        }
    }

    /// A Boolean vector's extension at a quirky point: skip Lagrange weights, then eq on the other coordinates.
    fn quirky_eval(f: &[bool], k_log: usize, k_skip: usize, point: &QuirkyPoint) -> F192 {
        let lambda = skip_lagrange_weights(k_skip, point.z_skip);
        let eq_rest = eq_table(&point.x_inner_rest);
        let eq_outer = eq_table(&point.x_outer);
        let mut acc = F192::ZERO;
        for (i, _) in f.iter().enumerate().filter(|&(_, &bit)| bit) {
            let i_skip = i & ((1 << k_skip) - 1);
            let i_rest = (i >> k_skip) & ((1 << (k_log - k_skip)) - 1);
            acc += lambda[i_skip] * eq_rest[i_rest] * eq_outer[i >> k_log];
        }
        acc
    }

    #[test]
    fn an_honest_proof_replays_to_the_witness_slices() {
        // Invariant: on an honest instance the replay accepts, agrees with the prover, and every slice is the truth.
        //
        // Fixture state, (m, k_log, k_skip): no skip, a partial skip, the whole instance skipped.
        for (m, k_log, k_skip) in [(10, 6, 0), (10, 6, 3), (10, 6, 6), (12, 7, 4), (14, 7, 6), (14, 7, 0)] {
            let mut rng = Rng::new(55 + (m * 100 + k_log * 10 + k_skip) as u64);
            let f = Fixture::new(m, k_log, k_skip, 2, &mut rng);
            let (claim, proof) = f.prove();
            let replayed = f
                .verify(k_skip, &proof)
                .unwrap_or_else(|e| panic!("m={m}, k_log={k_log}, k_skip={k_skip}: {e:?}"));
            assert_eq!(claim, replayed, "m={m}, k_log={k_log}, k_skip={k_skip}");

            // Slice `s` is bit `s` of every inner position of z, at `(r_inner_rest, x_outer)`.
            let eq_rest = eq_table(&replayed.r_inner_rest);
            let eq_outer = eq_table(&f.x_ab.x_outer);
            for (s, &slice) in replayed.s_hat_v.iter().enumerate() {
                let mut want = F192::ZERO;
                for (i_rest, &er) in eq_rest.iter().enumerate() {
                    for (i_outer, &eo) in eq_outer.iter().enumerate() {
                        if f.z[s + (i_rest << k_skip) + (i_outer << k_log)] {
                            want += er * eo;
                        }
                    }
                }
                assert_eq!(slice, want, "slice {s}, m={m}, k_log={k_log}, k_skip={k_skip}");
            }
        }
    }

    #[test]
    fn a_moved_slice_misses_the_terminal_identity() {
        // Invariant: every slice the sumcheck weights is pinned; moving one refuses the proof.
        //
        // Mutation: add 1 to one coordinate limb of a slice whose matrices' column is nonzero.
        //
        //     stream   [2 per round, k_log - k_skip rounds][64 slices][form value]
        let (m, k_log, k_skip) = (12, 6, 2);
        let mut rng = Rng::new(66);
        let f = Fixture::new(m, k_log, k_skip, 5, &mut rng);
        let (_, proof) = f.prove();
        let eq_inner = build_quirky_eq_table(f.x_ab.z_skip, &f.x_ab.x_inner_rest, k_skip);
        let (row_a, row_b) = (f.circuit.a_0.marginal(&eq_inner), f.circuit.b_0.marginal(&eq_inner));
        let column = (0..1 << k_log)
            .find(|&i| row_a[i] != F192::ZERO || row_b[i] != F192::ZERO)
            .expect("some column is nonzero");
        let word = 2 * (k_log - k_skip) + column % (1 << k_skip);
        for (limb, delta) in [("low", F192::ONE), ("middle", F192::new(0, 1, 0))] {
            let mut bad = proof.clone();
            bad.stream[word] += delta;
            assert!(
                matches!(f.verify(k_skip, &bad), Err(LincheckError::SumcheckMismatch)),
                "a {limb} limb moved"
            );
        }
    }

    #[test]
    fn a_malformed_proof_is_refused_on_its_shape() {
        let (m, k_log, k_skip) = (10, 6, 1);
        let mut rng = Rng::new(77);
        let f = Fixture::new(m, k_log, k_skip, 1, &mut rng);
        let (_, proof) = f.prove();

        // Mutation: drop the form value, so the replay runs out of words.
        let mut short = proof.clone();
        short.stream.pop();
        assert!(matches!(f.verify(k_skip, &short), Err(LincheckError::Transcript(_))));

        // Mutation: a skip wider than the instance.
        assert!(matches!(
            f.verify(k_log + 1, &proof),
            Err(LincheckError::KSkipExceedsKLog { .. })
        ));
    }
}
