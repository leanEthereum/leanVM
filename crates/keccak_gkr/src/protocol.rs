//! The claims the layers pass along, and what forming the next one takes.
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

use primitives::field::F192;
use primitives::multilinear::eq_table;

use crate::keccak::{BITS, along};
use crate::rmfe::{EMBED_BITS, PACK, RMFE};
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

pub fn sum(xs: &[F192]) -> F192 {
    xs.iter().fold(F192::ZERO, |acc, &x| acc + x)
}

pub fn dot(a: &[F192], b: &[F192]) -> F192 {
    a.iter().zip(b).fold(F192::ZERO, |acc, (&x, &y)| acc + x * y)
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
