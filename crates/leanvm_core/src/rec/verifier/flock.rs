//! Flock's reduction of one packed witness in rows: the zerocheck, then the lincheck up to its circuit's matrices.
//!
//! Neither stage checks anything on its own: the zerocheck is a reduction, and the lincheck's terminal identity is the matrix claim.
//! The rows derive the claims the native replay leaves, and the deferred claims carry them out.
//! The one structural check of the native lincheck, the circuit's width, holds by the circuit's construction.

use super::{Rows, infallible};
use crate::arith::{Arith, Verifier};
use crate::cpu::Claim;
use crate::rec::circuit::Ew;
use ::flock::lincheck::MatrixForm;
use ::flock::reduction::{Shape, SliceClaim};
use ::flock::zerocheck::univariate_skip_optimized::{medium_challenges, small_challenges};
use ::flock::zerocheck::{K_SKIP, MIN_LOG_N};
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

/// What the zerocheck leaves: its point, and the three evaluations the lincheck batches.
struct Zerocheck {
    z: Ew,
    mlv_challenges: Vec<Ew>,
    a_eval: Ew,
    b_eval: Ew,
    c_eval: Ew,
    /// `V_S(z)`, which the lincheck's `C` term reuses.
    vanishing: Ew,
}

/// The skip domain `S`, the first `ELL` nodes of the phi_8 table: an `F_2`-subspace of `K`, since phi_8 is linear on its index.
///
/// Its coset `Lambda = S + phi_8(ELL)` holds the zerocheck's first message.
struct SkipDomain;

impl Reduction {
    /// Replay the reduction of a packed witness of `2^n_blocks_log` instances of the circuit `shape`.
    pub(super) fn replay(r: &mut Rows<'_, '_>, shape: Shape, n_blocks_log: usize) -> Self {
        let m = shape.k_log + n_blocks_log;
        let zc = r.scope("zerocheck", |r| Zerocheck::replay(r, m));
        let matrix = r.scope("lincheck", |r| zc.lincheck(r, shape));
        let x_outer = &zc.mlv_challenges[shape.k_log - K_SKIP..];
        let mut suffix_point = matrix.point.r_inner_rest.clone();
        suffix_point.extend_from_slice(x_outer);
        let slice = SliceClaim {
            suffix_point,
            s_hat_v: matrix.point.s_hat_v.clone(),
        };
        Self { slice, matrix }
    }
}

impl Zerocheck {
    /// The zerocheck over `{0,1}^m`, as the native verifier replays it.
    fn replay(r: &mut Rows<'_, '_>, m: usize) -> Self {
        assert!(m >= MIN_LOG_N, "log_n {m} is below the zerocheck's floor {MIN_LOG_N}");
        // The equality tail: the fixed inner coordinates, then the sampled outer ones.
        let outer = r.sample_vec(m - MIN_LOG_N);
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

        let a_eval = infallible(r.next_scalar());
        let b_eval = infallible(r.next_scalar());
        let c_eval = r.mul_add(a_eval, b_eval, c_running);
        Self {
            z,
            mlv_challenges,
            a_eval,
            b_eval,
            c_eval,
            vanishing,
        }
    }

    /// The lincheck at this point, up to the matrices' bilinear form: the claim's value is the identity's other terms.
    fn lincheck(&self, r: &mut Rows<'_, '_>, shape: Shape) -> Claim<MatrixForm<Ew>, Ew> {
        assert!(K_SKIP <= shape.k_log, "k_skip {K_SKIP} exceeds k_log {}", shape.k_log);
        let inner_rest_len = shape.k_log - K_SKIP;
        let x_inner_rest = &self.mlv_challenges[..inner_rest_len];

        // The target the alpha-batched claims and the constant-wire pin (beta = alpha^3) set.
        let alpha = r.sample();
        let alpha_sq = r.square(alpha);
        let beta = r.mul(alpha_sq, alpha);
        let target = r.mul_add(alpha, self.b_eval, self.a_eval);
        let target = r.mul_add(alpha_sq, self.c_eval, target);
        let mut running = r.add(target, beta);

        let mut r_rounds = Vec::with_capacity(inner_rest_len);
        for _ in 0..inner_rest_len {
            let q = infallible(r.next_round_poly(3, running, None));
            let challenge = r.sample();
            running = r.poly_eval(&q, challenge);
            r_rounds.push(challenge);
        }
        let z_partial = infallible(r.next_scalars(ELL));
        let r_inner_rest: Vec<Ew> = r_rounds.into_iter().rev().collect();

        // The pin's `beta * w_col[pin]`: its slice times the eq weight of its inner index.
        let pin = shape.const_pin_col;
        let eq_pin = r.eq_bits(pin >> K_SKIP, &r_inner_rest);
        let pin_term = r.mul(z_partial[pin & (ELL - 1)], eq_pin);
        let value = r.mul_add(beta, pin_term, running);
        // The `C` term `alpha^2 * eq(x_inner_rest, r_inner_rest) * <lambda(z), z_partial>`.
        let slices = SkipDomain::lagrange_at(r, self.z, self.vanishing, &z_partial);
        let eq_inner = r.eq_eval(x_inner_rest, &r_inner_rest);
        let c_term = r.mul(eq_inner, slices);
        let value = r.mul_add(alpha_sq, c_term, value);

        Claim {
            point: MatrixForm {
                alpha,
                z_skip: self.z,
                x_inner_rest: x_inner_rest.to_vec(),
                r_inner_rest,
                s_hat_v: z_partial,
            },
            value,
        }
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
    fn vanishing(r: &mut Rows<'_, '_>, z: Ew) -> Ew {
        let c = Self::vanishing_coefficients();
        let mut powers = vec![z];
        for j in 0..K_SKIP {
            powers.push(r.square(powers[j]));
        }
        debug_assert_eq!(c[K_SKIP], F192::ONE, "the vanishing polynomial is monic");
        (c[..K_SKIP].iter().zip(&powers)).fold(powers[K_SKIP], |acc, (&cj, &p)| r.mul_const_add(p, cj, acc))
    }

    /// `sum_i values_i / (z + nodes_i)`, each inverse a hint held to `(z + node)·h = 1`.
    ///
    /// A node of `K` costs three rows; the zero node two.
    fn inverse_sum(r: &mut Rows<'_, '_>, z: Ew, nodes: &[F192], values: &[Ew]) -> Ew {
        assert_eq!(nodes.len(), values.len(), "a value per node");
        let zero = r.zero();
        (nodes.iter().zip(values)).fold(zero, |acc, (&node, &value)| {
            let difference = r.b.e(z) + node;
            let h = r.b.free_e(if difference.is_zero() {
                F192::ZERO
            } else {
                difference.inv()
            });
            let node_h = r.mul_const(h, node);
            let unit = r.mul_add(z, h, node_h);
            r.b.eq_e_const(unit, F192::ONE);
            r.mul_add(value, h, acc)
        })
    }

    /// The first round's message, known on `Lambda` and zero on `S`, interpolated at `z` over the window `S + Lambda`.
    ///
    /// Its value is `D_2ELL · V_S(z) · V_Lambda(z) · sum_i values_i / (z + lambda_i)`, with `V_Lambda(z) = V_S(z) + V_S(phi_8(ELL))`.
    fn first_round_at(r: &mut Rows<'_, '_>, z: Ew, vanishing: Ew, values: &[Ew]) -> Ew {
        let lambda = &PHI_8_TABLE[ELL..2 * ELL];
        let offset = Self::linearized(&Self::vanishing_coefficients(), lambda[0]);
        let on_lambda = r.add_const(vanishing, offset);
        let sum = Self::inverse_sum(r, z, lambda, values);
        let both = r.mul(vanishing, on_lambda);
        let scaled = r.mul_const(both, window_denominator(2 * ELL));
        r.mul(scaled, sum)
    }

    /// `sum_i L_i(z) values_i` over `S`, `L_i` its Lagrange basis: `D_ELL · V_S(z) · sum_i values_i / (z + s_i)`.
    fn lagrange_at(r: &mut Rows<'_, '_>, z: Ew, vanishing: Ew, values: &[Ew]) -> Ew {
        let sum = Self::inverse_sum(r, z, &PHI_8_TABLE[..ELL], values);
        let scaled = r.mul_const(vanishing, window_denominator(ELL));
        r.mul(scaled, sum)
    }
}
