//! Flock's batched reduction of packed witnesses in rows: one zerocheck, then one lincheck up to each circuit's matrices.
//!
//! The zerocheck's and the lincheck's final claims are equalities of wires; each circuit's matrix form is its claim.
//! The rows derive the claims the native replay leaves, and the deferred claims carry them out.
//! The one structural check of the native lincheck, a circuit's width, holds by the circuit's construction.

use super::{Rows, infallible};
use crate::arith::{Arith, Verifier};
use crate::cpu::Claim;
use crate::rec::circuit::Ew;
use ::flock::lincheck::MatrixForm;
use ::flock::reduction::Shape;
use ::flock::zerocheck::univariate_skip_optimized::{medium_challenges, small_challenges};
use ::flock::zerocheck::{K_SKIP, MIN_LOG_N};
use ::pcs::stack_open::SliceClaim;
use primitives::field::{F192, PHI_8_TABLE_192 as PHI_8_TABLE};
use primitives::multilinear::window_denominator;

/// The skip domain's size, and the zerocheck's first message's.
const ELL: usize = 1 << K_SKIP;

/// What one packed witness's reduction leaves: its claim on the witness, and its claim on the circuit's matrices.
pub(super) struct Reduction {
    /// The witness's bit slices at the lincheck's point, which the opening ring-switches.
    pub(super) slice: SliceClaim<Ew>,
    /// The value the matrices' bilinear form must take.
    pub(super) matrix: Claim<MatrixForm<Ew>, Ew>,
}

/// What the batched zerocheck leaves: its point, and each circuit's three evaluations, which the lincheck batches.
struct Zerocheck {
    z: Ew,
    /// The batch's challenges, circuit `f` taking its first `m_f - K_SKIP`.
    mlv_challenges: Vec<Ew>,
    /// Each circuit's `a`, `b` and `c` at its share of the point.
    evals: Vec<[Ew; 3]>,
    /// `V_S(z)`, which the lincheck's `C` terms reuse.
    vanishing: Ew,
}

/// The skip domain `S`, the first `ELL` nodes of the phi_8 table: an `F_2`-subspace of `K`, since phi_8 is linear on its index.
///
/// Its coset `Lambda = S + phi_8(ELL)` holds the zerocheck's first message.
pub(crate) struct SkipDomain;

impl Reduction {
    /// Replay the batched reduction of packed witnesses, circuit `f` of shape `circuits[f].0` with `2^circuits[f].1` instances.
    pub(super) fn replay(r: &mut Rows<'_, '_>, circuits: &[(Shape, usize)]) -> Vec<Self> {
        let log_ns: Vec<usize> = circuits.iter().map(|(shape, n)| shape.k_log + n).collect();
        let zc = r.scope("zerocheck", |r| Zerocheck::replay(r, &log_ns));
        let shapes: Vec<Shape> = circuits.iter().map(|&(shape, _)| shape).collect();
        let matrices = r.scope("lincheck", |r| zc.lincheck(r, &shapes));
        (matrices.into_iter().zip(&log_ns))
            .map(|(matrix, &m)| {
                let k = matrix.point.x_inner_rest.len();
                let mut suffix_point = matrix.point.r_inner_rest.clone();
                suffix_point.extend_from_slice(&zc.mlv_challenges[k..m - K_SKIP]);
                let slice = SliceClaim {
                    suffix_point,
                    s_hat_v: matrix.point.s_hat_v.clone(),
                };
                Self { slice, matrix }
            })
            .collect()
    }
}

impl Zerocheck {
    /// The batched zerocheck over cubes of `2^m_f` bits, as the native verifier replays it.
    fn replay(r: &mut Rows<'_, '_>, log_ns: &[usize]) -> Self {
        let m = log_ns.iter().copied().max().expect("a batch has a circuit");
        assert!(
            log_ns.iter().all(|&m| m >= MIN_LOG_N),
            "a log_n is below the zerocheck's floor {MIN_LOG_N}"
        );
        // The equality tail: the fixed inner coordinates, then the sampled outer ones; then the batching challenge.
        let outer = r.sample_vec(m - MIN_LOG_N);
        let lambda = r.sample();
        let lambdas = r.powers(lambda, log_ns.len());
        let fixed: Vec<Ew> = (small_challenges().into_iter().chain(medium_challenges()))
            .map(|c| r.constant(c))
            .collect();

        let round1 = infallible(r.next_scalars(ELL));
        let z = r.sample();
        let vanishing = SkipDomain::vanishing(r, z);
        let mut c_running = SkipDomain::first_round_at(r, z, vanishing, &round1);

        let mut mlv_challenges = Vec::with_capacity(m - K_SKIP);
        for &r_eq in fixed.iter().chain(&outer) {
            let g = infallible(r.next_round_poly(3, c_running, Some(r_eq)));
            let chi = r.sample();
            mlv_challenges.push(chi);
            c_running = r.poly_eval(&g, chi);
        }

        // The terminal identity: the running claim is `sum_f lambda^f (a_f b_f + c_f)`.
        let mut terminal = r.zero();
        let mut evals = Vec::with_capacity(log_ns.len());
        for &weight in &lambdas {
            let [a, b, c] = [(); 3].map(|()| infallible(r.next_scalar()));
            let value = r.mul_add(a, b, c);
            terminal = r.mul_add(weight, value, terminal);
            evals.push([a, b, c]);
        }
        infallible(r.ensure_eq(terminal, c_running, || "the zerocheck's terminal identity"));
        Self {
            z,
            mlv_challenges,
            evals,
            vanishing,
        }
    }

    /// The batched lincheck at this point, up to each circuit's matrices' bilinear form, whose value the prover sends.
    ///
    /// The batch's final claim is each circuit's form value and closed terms, times its weight and the challenges of the rounds it sat out.
    fn lincheck(&self, r: &mut Rows<'_, '_>, shapes: &[Shape]) -> Vec<Claim<MatrixForm<Ew>, Ew>> {
        let rests: Vec<usize> = shapes.iter().map(|s| s.k_log - K_SKIP).collect();

        // The target the alpha-batched claims and the constant-wire pins (beta = alpha^3) set, circuit `f` at `alpha^(4f)`.
        let alpha = r.sample();
        let alpha_sq = r.square(alpha);
        let beta = r.mul(alpha_sq, alpha);
        let alpha_4 = r.square(alpha_sq);
        let weights = r.powers(alpha_4, shapes.len());
        let mut running = r.zero();
        for (&[a, b, c], &weight) in self.evals.iter().zip(&weights) {
            let own = r.mul_add(alpha, b, a);
            let own = r.mul_add(alpha_sq, c, own);
            let own = r.add(own, beta);
            running = r.mul_add(weight, own, running);
        }

        let n_rounds = rests.iter().copied().max().expect("a batch has a circuit");
        let mut r_rounds = Vec::with_capacity(n_rounds);
        for _ in 0..n_rounds {
            let q = infallible(r.next_round_poly(3, running, None));
            let challenge = r.sample();
            running = r.poly_eval(&q, challenge);
            r_rounds.push(challenge);
        }
        // What a circuit of `rest` rounds waits on: the challenges of the rounds after its own.
        let mut waits = vec![r.one(); n_rounds + 1];
        for i in (0..n_rounds).rev() {
            waits[i] = r.mul(waits[i + 1], r_rounds[i]);
        }
        // The skip weights' inverses at `z`, which every circuit's `C` term shares.
        let inverses = SkipDomain::inverses(r, self.z);
        let scaled = r.mul_const(self.vanishing, window_denominator(ELL));
        // `eq(x_inner_rest, r_inner_rest)` for each length of the inner rest.
        let mut eq_inner = vec![None; n_rounds + 1];

        let mut total = r.zero();
        let mut claims = Vec::with_capacity(shapes.len());
        for ((shape, &rest), &weight) in shapes.iter().zip(&rests).zip(&weights) {
            let z_partial = infallible(r.next_scalars(ELL));
            let value = infallible(r.next_scalar());
            let r_inner_rest: Vec<Ew> = r_rounds[..rest].iter().rev().copied().collect();
            let x_inner_rest = &self.mlv_challenges[..rest];

            // The pin's `beta * w_col[pin]`: its slice times the eq weight of its inner index.
            let pin = shape.const_pin_col;
            let eq_pin = r.eq_bits(pin >> K_SKIP, &r_inner_rest);
            let pin_term = r.mul(z_partial[pin & (ELL - 1)], eq_pin);
            let own = r.mul_add(beta, pin_term, value);
            // The `C` term `alpha^2 * eq(x_inner_rest, r_inner_rest) * <lambda(z), z_partial>`.
            let slices = SkipDomain::lagrange_with(r, scaled, &inverses, &z_partial);
            let eq = *eq_inner[rest].get_or_insert_with(|| r.eq_eval(x_inner_rest, &r_inner_rest));
            let c_term = r.mul(eq, slices);
            let own = r.mul_add(alpha_sq, c_term, own);

            let lift = r.mul(weight, waits[rest]);
            total = r.mul_add(lift, own, total);
            claims.push(Claim {
                point: MatrixForm {
                    alpha,
                    z_skip: self.z,
                    x_inner_rest: x_inner_rest.to_vec(),
                    r_inner_rest,
                    s_hat_v: z_partial,
                },
                value,
            });
        }
        infallible(r.ensure_eq(total, running, || "the lincheck's final claim"));
        claims
    }
}

impl SkipDomain {
    /// The coefficients `c_j` of `V_S(X) = prod_{s in S} (X + s) = sum_j c_j X^(2^j)`, lowest first.
    ///
    /// Adding a basis element `a` to a subspace takes `V` to `V(X)^2 + V(a) V(X)`, since `V(X + a) = V(X) + V(a)`.
    fn vanishing_coefficients() -> [F192; K_SKIP + 1] {
        let mut c = [F192::ZERO; K_SKIP + 1];
        c[0] = F192::ONE;
        for j in 0..K_SKIP {
            let a = PHI_8_TABLE[1 << j];
            let at_a = Self::linearized(&c, a);
            for k in (0..=j + 1).rev() {
                let squared = if k == 0 { F192::ZERO } else { c[k - 1].square() };
                c[k] = squared + at_a * c[k];
            }
        }
        c
    }

    /// A linearized polynomial `sum_j c_j x^(2^j)` at `x`.
    fn linearized(c: &[F192], x: F192) -> F192 {
        let (mut power, mut acc) = (x, F192::ZERO);
        for &cj in c {
            acc += cj * power;
            power = power.square();
        }
        acc
    }

    /// `V_S(z)`: six squarings and six products by constants of `K`.
    pub(crate) fn vanishing<A: Arith>(a: &mut A, z: A::E) -> A::E {
        let c = Self::vanishing_coefficients();
        let mut powers = vec![z];
        for j in 0..K_SKIP {
            powers.push(a.square(powers[j]));
        }
        debug_assert_eq!(c[K_SKIP], F192::ONE, "the vanishing polynomial is monic");
        (c[..K_SKIP].iter().zip(&powers)).fold(powers[K_SKIP], |acc, (&cj, &p)| a.mul_const_add(p, cj, acc))
    }

    /// `1 / (z + node)` for each node.
    fn inverses_at<A: Arith>(a: &mut A, z: A::E, nodes: &[F192]) -> Vec<A::E> {
        (nodes.iter())
            .map(|&node| {
                let difference = a.add_const(z, node);
                a.inv(difference)
            })
            .collect()
    }

    /// `1 / (z + s_i)` over `S`, which [`Self::lagrange_with`] takes.
    fn inverses<A: Arith>(a: &mut A, z: A::E) -> Vec<A::E> {
        Self::inverses_at(a, z, &PHI_8_TABLE[..ELL])
    }

    /// `scale * sum_i values_i * inverses_i`.
    fn lagrange_with<A: Arith>(a: &mut A, scale: A::E, inverses: &[A::E], values: &[A::E]) -> A::E {
        assert_eq!(inverses.len(), values.len(), "a value per node");
        let zero = a.zero();
        let sum = (inverses.iter().zip(values)).fold(zero, |acc, (&h, &value)| a.mul_add(value, h, acc));
        a.mul(scale, sum)
    }

    /// The first round's message, known on `Lambda` and zero on `S`, interpolated at `z` over the window `S + Lambda`.
    ///
    /// Its value is `D_2ELL · V_S(z) · V_Lambda(z) · sum_i values_i / (z + lambda_i)`, with `V_Lambda(z) = V_S(z) + V_S(phi_8(ELL))`.
    fn first_round_at<A: Arith>(a: &mut A, z: A::E, vanishing: A::E, values: &[A::E]) -> A::E {
        let lambda = &PHI_8_TABLE[ELL..2 * ELL];
        let offset = Self::linearized(&Self::vanishing_coefficients(), lambda[0]);
        let on_lambda = a.add_const(vanishing, offset);
        let both = a.mul(vanishing, on_lambda);
        let scaled = a.mul_const(both, window_denominator(2 * ELL));
        let inverses = Self::inverses_at(a, z, lambda);
        Self::lagrange_with(a, scaled, &inverses, values)
    }

    /// `sum_i L_i(z) values_i` over `S`, `L_i` its Lagrange basis: `D_ELL · V_S(z) · sum_i values_i / (z + s_i)`.
    pub(crate) fn lagrange_at<A: Arith>(a: &mut A, z: A::E, vanishing: A::E, values: &[A::E]) -> A::E {
        let scaled = a.mul_const(vanishing, window_denominator(ELL));
        let inverses = Self::inverses(a, z);
        Self::lagrange_with(a, scaled, &inverses, values)
    }
}
