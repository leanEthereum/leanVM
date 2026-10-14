// CREDIT: https://github.com/succinctlabs/flock (the skip domain's Lagrange weights), MIT OR Apache-2.0.
//! The univariate skip's domain, and the interpolations at the skip challenge its verifiers and its prover share.

use fiat_shamir::arith::{Arith, Native};
use primitives::field::gf2_64::{portable::clmul, reduce};
use primitives::field::{F192, PHI8_TABLE};
use primitives::multilinear::eq_table;

use super::K_SKIP;
use crate::lincheck::outer_product;

/// The skip domain `S`: the first `2^k_skip` nodes of the phi_8 table.
///
/// It is a subspace over GF(2), since phi_8 is linear on its index.
/// Its coset `Lambda = S + phi_8(2^k_skip)` holds the zerocheck's first message.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SkipDomain {
    k_skip: usize,
    /// The coefficients `c_j` of `V_S(X) = prod_{s in S} (X + s) = sum_j c_j X^(2^j)`, lowest first, zero past `k_skip`.
    vanishing: [F192; 8],
    /// `V_S(phi_8(2^k_skip))`, by which the coset's vanishing polynomial `V_Lambda` exceeds `V_S`, `V_S` being linear.
    offset: F192,
}

impl SkipDomain {
    /// The domain the zerocheck skips and the lincheck interpolates over.
    pub const FLOCK: Self = Self::new(K_SKIP);

    /// The domain of `2^k_skip` nodes, its constants computed at compile time.
    ///
    /// # Panics
    ///
    /// If `S` and `Lambda` do not fit the phi_8 table.
    pub(crate) const fn new(k_skip: usize) -> Self {
        const ALL: [SkipDomain; 8] = {
            let mut all = [SkipDomain::compute(0); 8];
            let mut k = 1;
            while k < 8 {
                all[k] = SkipDomain::compute(k);
                k += 1;
            }
            all
        };
        assert!(k_skip < 8, "the window fits the phi_8 table");
        ALL[k_skip]
    }

    /// The domain of `2^k_skip` nodes, by the portable products.
    const fn compute(k_skip: usize) -> Self {
        // Adding a basis element `a` to a subspace takes `V` to `V(X)^2 + V(a) V(X)`, since `V(X + a) = V(X) + V(a)`.
        // The zero subspace's polynomial is `X`; the basis elements are `phi_8(2^j)`.
        let mut vanishing = [F192::ZERO; 8];
        vanishing[0] = F192::ONE;
        let mut j = 0;
        while j < k_skip {
            let at_a = linearized(&vanishing, PHI8_TABLE[1 << j]);
            // `V(X)^2` shifts every coefficient up a power; `V(a) V(X)` scales them in place.
            let mut k = j + 1;
            while k > 0 {
                vanishing[k] = plus(vanishing[k - 1].square_portable(), at_a.mul_portable(vanishing[k]));
                k -= 1;
            }
            vanishing[0] = at_a.mul_portable(vanishing[0]);
            j += 1;
        }
        let offset = linearized(&vanishing, PHI8_TABLE[1 << k_skip]);
        Self {
            k_skip,
            vanishing,
            offset,
        }
    }

    /// The base-two logarithm of its size.
    pub(crate) const fn k_skip(self) -> usize {
        self.k_skip
    }

    /// Its size, and the zerocheck's first message's.
    pub(crate) const fn size(self) -> usize {
        1 << self.k_skip
    }

    /// `V_S(z)`: `k_skip` squarings and as many products by constants of `K`.
    pub fn vanishing<A: Arith>(self, a: &mut A, z: A::E) -> A::E {
        let c = &self.vanishing;
        // `z^(2^j)` for every `j`, by squaring.
        let mut powers = vec![z];
        for j in 0..self.k_skip {
            powers.push(a.square(powers[j]));
        }
        debug_assert_eq!(c[self.k_skip], F192::ONE, "the vanishing polynomial is monic");
        (c[..self.k_skip].iter().zip(&powers)).fold(powers[self.k_skip], |acc, (&cj, &p)| a.mul_const_add(p, cj, acc))
    }

    /// `1 / (z + s_i)` over `S`, which the Lagrange sum over `S` takes.
    pub(crate) fn inverses<A: Arith>(self, a: &mut A, z: A::E) -> Vec<A::E> {
        inverses_at(a, z, &PHI8_TABLE[..self.size()])
    }

    /// The first round's message, known on `Lambda` and zero on `S`, interpolated at `z` over the window `S + Lambda`.
    ///
    /// Its value, `l` the domain's size:
    ///
    /// ```text
    ///     D_2l * V_S(z) * V_Lambda(z) * sum_i values_i / (z + lambda_i)        V_Lambda(z) = V_S(z) + V_S(phi_8(l))
    /// ```
    pub(crate) fn first_round_at<A: Arith>(self, a: &mut A, z: A::E, vanishing: A::E, values: &[A::E]) -> A::E {
        let size = self.size();
        // The coset's vanishing polynomial is the domain's shifted by a constant, `V_S` being linear.
        let lambda = &PHI8_TABLE[size..2 * size];
        let on_lambda = a.add_const(vanishing, self.offset);
        let both = a.mul(vanishing, on_lambda);
        let scaled = a.mul_const(both, window_denominator(2 * size));
        let inverses = inverses_at(a, z, lambda);
        lagrange_sum(a, scaled, &inverses, values)
    }

    /// `D_l * V_S(z)`, `l` the domain's size: the scale of the Lagrange sum over `S`.
    pub(crate) fn lagrange_scale<A: Arith>(self, a: &mut A, vanishing: A::E) -> A::E {
        a.mul_const(vanishing, window_denominator(self.size()))
    }

    /// `sum_i L_i(z) values_i` over `S`, `L_i` its Lagrange basis: `D_l * V_S(z) * sum_i values_i / (z + s_i)`.
    pub fn lagrange_at<A: Arith>(self, a: &mut A, z: A::E, vanishing: A::E, values: &[A::E]) -> A::E {
        let scaled = self.lagrange_scale(a, vanishing);
        let inverses = self.inverses(a, z);
        lagrange_sum(a, scaled, &inverses, values)
    }

    /// The Lagrange basis of `S` at `z`, `L_i(z) = D_l * prod_{k != i} (z + s_k)`, on `a`.
    pub(crate) fn lagrange_weights<A: Arith>(self, a: &mut A, z: A::E) -> Vec<A::E> {
        window_lagrange_weights(a, self.k_skip, z)
    }

    /// The eq table of a skip point's inner half: the Lagrange basis at `z_skip` on the low index bits.
    ///
    /// ```text
    ///     out[i_skip + i_rest 2^k_skip] = L_(i_skip)(z_skip) * eq(x_inner_rest, i_rest)
    /// ```
    pub fn inner_eq_table(self, z_skip: F192, x_inner_rest: &[F192]) -> Vec<F192> {
        outer_product(
            &mut Native,
            &eq_table(x_inner_rest),
            &self.lagrange_weights(&mut Native, z_skip),
        )
    }
}

/// A linearized polynomial `sum_j c_j x^(2^j)` at `x`, by the portable products.
const fn linearized(c: &[F192; 8], x: F192) -> F192 {
    let (mut power, mut acc, mut j) = (x, F192::ZERO, 0);
    while j < c.len() {
        acc = plus(acc, c[j].mul_portable(power));
        power = power.square_portable();
        j += 1;
    }
    acc
}

/// `a + b`, in a `const` context.
const fn plus(a: F192, b: F192) -> F192 {
    F192::new(a.c0 ^ b.c0, a.c1 ^ b.c1, a.c2 ^ b.c2)
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

/// `scale * sum_i values_i * inverses_i`: a Lagrange sum, given its nodes' inverses at the point.
pub(crate) fn lagrange_sum<A: Arith>(a: &mut A, scale: A::E, inverses: &[A::E], values: &[A::E]) -> A::E {
    assert_eq!(inverses.len(), values.len(), "a value per node");
    let zero = a.zero();
    let sum = (inverses.iter().zip(values)).fold(zero, |acc, (&h, &value)| a.mul_add(value, h, acc));
    a.mul(scale, sum)
}

/// The Lagrange basis of the first `2^log_size` nodes of the phi_8 table at `z`.
///
/// Prefix and suffix products of the differences give every weight.
///
/// No inverse is taken, so the weights are exact at a node too.
fn window_lagrange_weights<A: Arith>(a: &mut A, log_size: usize, z: A::E) -> Vec<A::E> {
    let n = 1 << log_size;
    let nodes = &PHI8_TABLE[..n];
    // Prefix products: weight `i` holds `prod_{k < i} (z + s_k)`.
    let denominator = a.constant(window_denominator(n));
    let mut weights = vec![denominator; n];
    for i in 1..n {
        let difference = a.add_const(z, nodes[i - 1]);
        weights[i] = a.mul(weights[i - 1], difference);
    }
    // Suffix products: weight `i` takes `prod_{k > i} (z + s_k)`.
    let mut suffix = a.add_const(z, nodes[n - 1]);
    for i in (1..n - 1).rev() {
        weights[i] = a.mul(weights[i], suffix);
        let difference = a.add_const(z, nodes[i]);
        suffix = a.mul(suffix, difference);
    }
    if n > 1 {
        weights[0] = a.mul(weights[0], suffix);
    }
    weights
}

/// `D_l = 1 / prod_{k != 0} phi_8(k)`: the barycentric weight of every node of an aligned window of `l` nodes.
///
/// One value serves the whole window:
///
/// ```text
///     prod_{k != i} (s_i + s_k) = prod_{k != i} phi_8(i ^ k) = prod_{j != 0} phi_8(j)
/// ```
///
/// - `phi_8` is GF(2)-linear on its index, so `s_i + s_k = phi_8(i ^ k)` and a coset's offset cancels.
/// - `k -> i ^ k` permutes the window's nonzero indices.
fn window_denominator(size: usize) -> F192 {
    debug_assert!(size.is_power_of_two() && size <= PHI8_TABLE.len());
    DENOMINATORS[size.trailing_zeros() as usize]
}

/// The barycentric weight of every window size, at compile time.
///
/// The nodes lie in `K`, so the product and its inverse stay there.
///
/// The inverse is Fermat's: `a^(2^64 - 2)`, by squarings.
const DENOMINATORS: [F192; 9] = {
    const fn mul(a: u64, b: u64) -> u64 {
        reduce(clmul(a, b))
    }
    let mut out = [F192::ZERO; 9];
    let mut log = 0;
    while log < out.len() {
        let mut product = 1;
        let mut k = 1;
        while k < 1 << log {
            product = mul(product, PHI8_TABLE[k].c0);
            k += 1;
        }
        let (mut inverse, mut bit) = (1, 1);
        while bit < 64 {
            product = mul(product, product);
            inverse = mul(inverse, product);
            bit += 1;
        }
        out[log] = F192::new(inverse, 0, 0);
        log += 1;
    }
    out
};

#[cfg(test)]
mod tests {
    use super::*;
    use fiat_shamir::arith::Portable;
    use primitives::test_util::Rng;

    /// `1 / prod_{k != i} (s_i + s_k)` over a window's nodes, by its definition.
    fn per_node_denominator(nodes: &[F192], i: usize) -> F192 {
        let others = nodes.iter().enumerate().filter(|&(k, _)| k != i);
        others.fold(F192::ONE, |acc, (_, &node)| acc * (nodes[i] + node)).inv()
    }

    #[test]
    fn every_aligned_window_shares_one_denominator() {
        // Invariant: every node of every aligned window of the phi_8 table has the same barycentric denominator.
        //
        // It holds only while the table is the image of a basis, which this pins.
        for log_size in 1..=8 {
            let size = 1usize << log_size;
            for base in (0..PHI8_TABLE.len()).step_by(size) {
                let nodes = &PHI8_TABLE[base..base + size];
                for i in 0..size {
                    assert_eq!(
                        per_node_denominator(nodes, i),
                        window_denominator(size),
                        "size {size}, base {base}, node {i}"
                    );
                }
            }
        }
    }

    #[test]
    fn the_lagrange_weights_are_the_definition() {
        // Invariant: `L_i(z) = prod_{k != i} (z + s_k) / (s_i + s_k)`, at random points and at every node.
        let mut rng = Rng::new(0xBA7C_E417);
        for log_size in 0..=8 {
            let nodes = &PHI8_TABLE[..1 << log_size];
            let points = rng.ext_vec(4).into_iter().chain(nodes.iter().copied());
            for z in points {
                let want: Vec<F192> = (0..nodes.len())
                    .map(|i| {
                        let others = nodes.iter().enumerate().filter(|&(k, _)| k != i);
                        others.fold(per_node_denominator(nodes, i), |acc, (_, &node)| acc * (z + node))
                    })
                    .collect();
                assert_eq!(
                    window_lagrange_weights(&mut Native, log_size, z),
                    want,
                    "log_size {log_size}"
                );
                assert_eq!(
                    window_lagrange_weights(&mut Portable, log_size, z),
                    want,
                    "log_size {log_size}"
                );
            }
        }
    }

    #[test]
    fn the_first_round_is_the_whole_windows_interpolant() {
        // Invariant: the first round, known on Lambda and zero on S, is the whole window's interpolant.
        //
        // Fixture state: every domain size, random values on Lambda, four random points each.
        let mut rng = Rng::new(0x0C0B_14ED);
        for k_skip in 0..8 {
            let domain = SkipDomain::new(k_skip);
            let values = rng.ext_vec(domain.size());
            for z in rng.ext_vec(4) {
                // The window's Lagrange weights at `z`, zero on S, so only Lambda's half counts.
                let window = window_lagrange_weights(&mut Native, k_skip + 1, z)[domain.size()..]
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

    #[test]
    fn the_lagrange_sum_is_the_skip_domains() {
        // Invariant: the vanishing polynomial and the Lagrange sum over S are the domain's, by their definitions.
        //
        // Fixture state: every domain size, four random points each.
        let mut rng = Rng::new(0x5_1EB);
        for k_skip in 0..8 {
            let domain = SkipDomain::new(k_skip);
            let values = rng.ext_vec(domain.size());
            for z in rng.ext_vec(4) {
                // `V_S(z)` as the product over the nodes.
                let vanishing = (PHI8_TABLE[..domain.size()].iter()).fold(F192::ONE, |acc, &s| acc * (z + s));
                assert_eq!(domain.vanishing(&mut Native, z), vanishing, "k_skip {k_skip}");
                let lagrange = (domain.lagrange_weights(&mut Native, z).iter().zip(&values))
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
