//! What both sides of the layer reduction compute.
//!
//! A [`Claim`] is a weighted sum of the bits of one state per segment. With `bit(y, j, i)` the
//! bit at position `j` of instance `i` of pack `y`, the claimed value is
//!
//! ```text
//!     sum over segments, packs y, positions j, instances i of
//!         eq(point, (y, segment)) * weights[j] * mu[i] * bit(y, j, i)
//! ```
//!
//! One layer turns a claim on the states after a round into a claim on the states before it.

use fiat_shamir::transcript::{Error, Receiver};
use primitives::field::F192;
use primitives::multilinear::{eq_table, poly_eval};

use crate::keccak::{BITS, LOCAL_VARS, along, iota_bit, linear_transpose};
use crate::rmfe::{EMBED_BITS, PACK, PROD_BITS, RMFE};
use crate::witness::Shape;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claim {
    pub value: F192,
    /// The weight of each instance of a pack.
    pub mu: [F192; PACK],
    /// A pack index, then a segment index.
    pub point: Vec<F192>,
    /// The weight of each bit position.
    pub weights: Vec<F192>,
}

/// The instance weights of a claim made at the polynomial point `s`: the value at `s` of each
/// unit vector's embedding.
pub fn mu_at(s: F192) -> [F192; PACK] {
    let mut powers = [F192::ONE; EMBED_BITS];
    for b in 1..EMBED_BITS {
        powers[b] = powers[b - 1] * s;
    }
    std::array::from_fn(|i| {
        (0..EMBED_BITS)
            .filter(|b| RMFE.emb[i] >> b & 1 == 1)
            .fold(F192::ZERO, |acc, b| acc + powers[b])
    })
}

/// The functional reading a `mu`-weighted sum of projected bits off the coefficients of a product.
pub fn functional(mu: &[F192; PACK]) -> [F192; PROD_BITS] {
    std::array::from_fn(|c| {
        (0..PACK)
            .filter(|&i| RMFE.proj[i] >> c & 1 == 1)
            .fold(F192::ZERO, |acc, i| acc + mu[i])
    })
}

pub fn sum(xs: &[F192]) -> F192 {
    xs.iter().fold(F192::ZERO, |acc, &x| acc + x)
}

pub fn dot(a: &[F192], b: &[F192]) -> F192 {
    a.iter().zip(b).fold(F192::ZERO, |acc, (&x, &y)| acc + x * y)
}

/// What `iota` adds to a claim on the states `step` layers below each segment's output.
pub fn iota_term(shape: Shape, step: usize, claim: &Claim) -> F192 {
    let segment_weights = eq_table(&claim.point[shape.pack_vars()..]);
    let mut acc = F192::ZERO;
    for segment in 0..shape.segments() {
        let round = shape.round(segment, step);
        let flipped = (0..64)
            .filter(|&z| iota_bit(round, z))
            .fold(F192::ZERO, |acc, z| acc + claim.weights[z]);
        acc += segment_weights[segment] * flipped;
    }
    acc * sum(&claim.mu)
}

/// The weights of the claim a layer leaves on the state before `chi`.
///
/// The layer ends with `t[k] = sum_j eq[j] * T[j + k]` for `k` in `0..3`, which `beta` batches
/// into one weighted sum of `T`.
pub fn chi_weights(eq: &[F192], beta: F192) -> Vec<F192> {
    let mut out = vec![F192::ZERO; BITS];
    for j in 0..BITS {
        out[j] += eq[j];
        out[along(j, 1)] += beta * eq[j];
        out[along(j, 2)] += beta.square() * eq[j];
    }
    out
}

/// The claim the layers start from, once its challenges are drawn: a random combination of the
/// output lanes as words, bit `z` of a word weighing `x^z`.
pub fn first_claim(shape: Shape, value: F192, r_low: &[F192], point: Vec<F192>, r_lane: &[F192]) -> Claim {
    let mu: [F192; PACK] = eq_table(r_low).try_into().expect("four low variables");
    assert_eq!(point.len(), shape.y_vars());
    let lanes = eq_table(r_lane);
    Claim {
        value,
        mu,
        point,
        weights: (0..BITS)
            .map(|j| lanes[j / 64] * F192::new(1 << (j % 64), 0, 0))
            .collect(),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifyError {
    Transcript(Error),
    /// The product polynomial does not carry the claimed value.
    Projection,
    /// The layer's final evaluations do not give the sumcheck's claim.
    Terminal,
    /// A reduction to the commitment ends on the wrong value.
    Opening,
}

impl From<Error> for VerifyError {
    fn from(e: Error) -> Self {
        Self::Transcript(e)
    }
}

/// Verify one layer: a claim on the states `step` layers below the outputs becomes a claim on the
/// states one layer further down.
pub fn verify_layer(vs: &mut impl Receiver, shape: Shape, step: usize, claim: &Claim) -> Result<Claim, VerifyError> {
    let product = vs.next_scalars(PROD_BITS)?;
    if dot(&functional(&claim.mu), &product) + iota_term(shape, step, claim) != claim.value {
        return Err(VerifyError::Projection);
    }
    let s = vs.sample();
    let mu = mu_at(s);
    let kappa = sum(&mu);
    let mut value = poly_eval(&product, s);

    let mut scale = F192::ONE;
    let mut point = Vec::with_capacity(claim.point.len());
    for &r in &claim.point {
        let h = vs.next_round_poly(3, value, Some(r))?;
        let rho = vs.sample();
        let eq = F192::ONE + r + rho;
        value = eq * poly_eval(&h, rho);
        scale *= eq;
        point.push(rho);
    }

    // The bit position: `sum_j w[j] (kappa T[j] + (kappa + T[j + 1]) T[j + 2])`, the weights
    // being one more multilinear factor.
    let mut local = Vec::with_capacity(LOCAL_VARS);
    for _ in 0..LOCAL_VARS {
        let h = vs.next_round_poly(4, value, None)?;
        let rho = vs.sample();
        value = poly_eval(&h, rho);
        local.push(rho);
    }
    let t = vs.next_scalars(3)?;
    let eq = eq_table(&local);
    if scale * dot(&eq, &claim.weights) * (kappa * t[0] + (kappa + t[1]) * t[2]) != value {
        return Err(VerifyError::Terminal);
    }
    let beta = vs.sample();
    Ok(Claim {
        value: t[0] + beta * (t[1] + beta * t[2]),
        mu,
        point,
        weights: linear_transpose(&chi_weights(&eq, beta)),
    })
}
