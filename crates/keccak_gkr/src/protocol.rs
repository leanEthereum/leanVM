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

use primitives::field::{F128, powers};
use primitives::multilinear::eq_table;

use crate::keccak::{BITS, along};
use crate::rmfe::{EMBED_BITS, PACK, RMFE};
use crate::witness::Shape;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claim {
    pub value: F128,
    /// The weight of each instance of a pack.
    pub mu: [F128; PACK],
    /// A pack index, then a segment index.
    pub point: Vec<F128>,
    /// The weight of each bit position.
    pub weights: Vec<F128>,
}

/// The instance weights of a claim made at the polynomial point `s`: the value at `s` of each
/// unit vector's embedding.
pub fn mu_at(s: F128) -> [F128; PACK] {
    let powers = powers(s, EMBED_BITS);
    std::array::from_fn(|i| {
        (0..EMBED_BITS)
            .filter(|b| RMFE.emb[i] >> b & 1 == 1)
            .map(|b| powers[b])
            .sum()
    })
}

pub fn dot(a: &[F128], b: &[F128]) -> F128 {
    a.iter().zip(b).map(|(&x, &y)| x * y).sum()
}

/// The weights of the claim a layer leaves on the state before `chi`.
///
/// The layer ends with `t[k] = sum_j eq[j] * T[j + k]` for `k` in `0..3`, which `beta` batches
/// into one weighted sum of `T`.
pub fn chi_weights(eq: &[F128], beta: F128) -> Vec<F128> {
    let mut out = vec![F128::ZERO; BITS];
    for j in 0..BITS {
        out[j] += eq[j];
        out[along(j, 1)] += beta * eq[j];
        out[along(j, 2)] += beta.square() * eq[j];
    }
    out
}

/// The claim the layers start from, once its challenges are drawn, valued at zero: a random
/// combination of the output lanes as words, bit `z` of a word weighing `x^z`.
pub fn first_claim(shape: Shape, r_low: &[F128], point: Vec<F128>, r_lane: &[F128]) -> Claim {
    let mu: [F128; PACK] = eq_table(r_low).try_into().expect("four low variables");
    assert_eq!(point.len(), shape.y_vars());
    let lanes = eq_table(r_lane);
    Claim {
        value: F128::ZERO,
        mu,
        point,
        weights: (0..BITS)
            .map(|j| lanes[j / 64] * F128::new(1 << (j % 64), 0, 0))
            .collect(),
    }
}
