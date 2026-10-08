//! The univariate skip's domain, and the interpolations at the skip challenge that its verifiers and its prover share.

use primitives::PrimeCharacteristicRing;

use super::K_SKIP;
use fiat_shamir::arith::Arith;
use primitives::multilinear::window_denominator;
use primitives::{F192, PHI_8_TABLE_192};

/// The skip domain `S`, the first `2^k_skip` nodes of the phi_8 table: an `F_2`-subspace of `K`, since phi_8 is linear on its index.
///
/// Its coset `Lambda = S + phi_8(2^k_skip)` holds the zerocheck's first message.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SkipDomain {
    k_skip: usize,
}

impl SkipDomain {
    /// The domain the zerocheck skips and the lincheck interpolates over.
    pub const FLOCK: Self = Self { k_skip: K_SKIP };

    /// The domain of `2^k_skip` nodes.
    ///
    /// # Panics
    ///
    /// If `S` and `Lambda` do not fit the phi_8 table.
    pub(crate) const fn new(k_skip: usize) -> Self {
        assert!(k_skip < 8, "the window fits the phi_8 table");
        Self { k_skip }
    }

    /// The base-two logarithm of its size.
    pub(crate) const fn k_skip(self) -> usize {
        self.k_skip
    }

    /// Its size, and the zerocheck's first message's.
    pub(crate) const fn size(self) -> usize {
        1 << self.k_skip
    }

    /// The coefficients `c_j` of `V_S(X) = prod_{s in S} (X + s) = sum_j c_j X^(2^j)`, lowest first.
    ///
    /// Adding a basis element `a` to a subspace takes `V` to `V(X)^2 + V(a) V(X)`, since `V(X + a) = V(X) + V(a)`.
    fn vanishing_coefficients(self) -> Vec<F192> {
        let mut c = vec![F192::ZERO; self.k_skip + 1];
        c[0] = F192::ONE;
        for j in 0..self.k_skip {
            let a = PHI_8_TABLE_192[1 << j];
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

    /// `V_S(z)`: `k_skip` squarings and as many products by constants of `K`.
    pub fn vanishing<A: Arith>(self, a: &mut A, z: A::E) -> A::E {
        let c = self.vanishing_coefficients();
        let mut powers = vec![z];
        for j in 0..self.k_skip {
            powers.push(a.square(powers[j]));
        }
        debug_assert_eq!(c[self.k_skip], F192::ONE, "the vanishing polynomial is monic");
        (c[..self.k_skip].iter().zip(&powers)).fold(powers[self.k_skip], |acc, (&cj, &p)| a.mul_const_add(p, cj, acc))
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

    /// `1 / (z + s_i)` over `S`, which the Lagrange sum over `S` takes.
    pub(crate) fn inverses<A: Arith>(self, a: &mut A, z: A::E) -> Vec<A::E> {
        Self::inverses_at(a, z, &PHI_8_TABLE_192[..self.size()])
    }

    /// `scale * sum_i values_i * inverses_i`.
    pub(crate) fn lagrange_with<A: Arith>(a: &mut A, scale: A::E, inverses: &[A::E], values: &[A::E]) -> A::E {
        assert_eq!(inverses.len(), values.len(), "a value per node");
        let zero = a.zero();
        let sum = (inverses.iter().zip(values)).fold(zero, |acc, (&h, &value)| a.mul_add(value, h, acc));
        a.mul(scale, sum)
    }

    /// The first round's message, known on `Lambda` and zero on `S`, interpolated at `z` over the window `S + Lambda`.
    ///
    /// Its value is `D_2l · V_S(z) · V_Lambda(z) · sum_i values_i / (z + lambda_i)`, `l` the domain's size, with `V_Lambda(z) = V_S(z) + V_S(phi_8(l))`.
    pub(crate) fn first_round_at<A: Arith>(self, a: &mut A, z: A::E, vanishing: A::E, values: &[A::E]) -> A::E {
        let size = self.size();
        let lambda = &PHI_8_TABLE_192[size..2 * size];
        let offset = Self::linearized(&self.vanishing_coefficients(), lambda[0]);
        let on_lambda = a.add_const(vanishing, offset);
        let both = a.mul(vanishing, on_lambda);
        let scaled = a.mul_const(both, window_denominator(2 * size));
        let inverses = Self::inverses_at(a, z, lambda);
        Self::lagrange_with(a, scaled, &inverses, values)
    }

    /// `D_l · V_S(z)`, `l` the domain's size: the scale of the Lagrange sum over `S`.
    pub(crate) fn lagrange_scale<A: Arith>(self, a: &mut A, vanishing: A::E) -> A::E {
        a.mul_const(vanishing, window_denominator(self.size()))
    }

    /// `sum_i L_i(z) values_i` over `S`, `L_i` its Lagrange basis: `D_l · V_S(z) · sum_i values_i / (z + s_i)`.
    pub fn lagrange_at<A: Arith>(self, a: &mut A, z: A::E, vanishing: A::E, values: &[A::E]) -> A::E {
        let scaled = self.lagrange_scale(a, vanishing);
        let inverses = self.inverses(a, z);
        Self::lagrange_with(a, scaled, &inverses, values)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fiat_shamir::arith::Native;
    use primitives::PrimeCharacteristicRing;
    use primitives::multilinear::skip_lagrange_weights;
    use primitives::test_util::Rng;

    // The first round, known on `Lambda` and zero on `S`, is the whole window's interpolant, at random points.
    #[test]
    fn the_first_round_is_the_whole_windows_interpolant() {
        let mut rng = Rng::new(0x0C0B_14ED);
        for k_skip in 0..8 {
            let domain = SkipDomain::new(k_skip);
            let values = rng.ext_vec(domain.size());
            for z in rng.ext_vec(4) {
                let window = skip_lagrange_weights(k_skip + 1, z)[domain.size()..]
                    .iter()
                    .zip(&values)
                    .fold(F192::ZERO, |acc, (&w, &v)| acc + w * v);
                let vanishing = domain.vanishing(&mut Native, z);
                assert_eq!(
                    domain.first_round_at(&mut Native, z, vanishing, &values),
                    window,
                    "k_skip {k_skip}"
                );
            }
        }
    }

    // The vanishing polynomial and the Lagrange sum over `S` are the skip domain's, at random points.
    #[test]
    fn the_lagrange_sum_is_the_skip_domains() {
        let mut rng = Rng::new(0x5_1EB);
        for k_skip in 0..8 {
            let domain = SkipDomain::new(k_skip);
            let values = rng.ext_vec(domain.size());
            for z in rng.ext_vec(4) {
                let vanishing = (PHI_8_TABLE_192[..domain.size()].iter()).fold(F192::ONE, |acc, &s| acc * (z + s));
                assert_eq!(domain.vanishing(&mut Native, z), vanishing, "k_skip {k_skip}");
                let lagrange = (skip_lagrange_weights(k_skip, z).iter().zip(&values))
                    .fold(F192::ZERO, |acc, (&w, &v)| acc + w * v);
                assert_eq!(
                    domain.lagrange_at(&mut Native, z, vanishing, &values),
                    lagrange,
                    "k_skip {k_skip}"
                );
            }
        }
    }
}
