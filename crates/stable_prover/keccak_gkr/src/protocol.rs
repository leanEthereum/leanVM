//! The claims the layers pass along (Annex C, `keccak:claims`): with `bit(y, j, i)` bit `j` of instance `i` of pack
//! `y`, in the state each segment's claim is on, a claim says
//!
//! ```text
//!     value = sum over segments m, packs y, positions j, instances i of
//!                 eq(point, (y, m)) * weights[j] * mu[i] * bit(y, j, i)
//! ```

use primitives::field::{F128, powers};
use primitives::multilinear::eq_table;
use verifier::keccak::{BITS, EMBED_BITS, PACK, RMFE_EMBED, along, linear_transpose};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claim {
    /// The weight of each instance of a pack.
    pub mu: [F128; PACK],
    /// A pack index, then a segment index.
    pub point: Vec<F128>,
    /// The weight of each bit position.
    pub weights: Vec<F128>,
}

/// The first claim's weights: on the outputs at the caller's `instance` point, a random combination
/// of the lanes as words, bit `z` of a word weighing `x^z`, at a random segment.
pub fn first_claim(instance: &[F128], segment: &[F128], r_lane: &[F128]) -> Claim {
    let lanes = eq_table(r_lane);
    Claim {
        mu: eq_table(&instance[..4]).try_into().expect("four low variables"),
        point: [&instance[4..], segment].concat(),
        weights: (0..BITS).map(|j| lanes[j / 64] * F128::new(1 << (j % 64), 0)).collect(),
    }
}

/// The instance weights of a claim made at the polynomial point `s`: each unit vector's embedding at `s`.
pub fn instance_weights(s: F128) -> [F128; PACK] {
    let powers = powers(s, EMBED_BITS);
    std::array::from_fn(|i| {
        (0..EMBED_BITS)
            .filter(|b| RMFE_EMBED[i] >> b & 1 == 1)
            .map(|b| powers[b])
            .sum()
    })
}

/// The position weights of the claim a layer leaves, whose bit-position sumcheck ended at `local`: on the state
/// before `chi`, `t[k] = sum_j eq(local, j) * u[j + k]` batched by `beta`, then moved through the linear map.
pub fn next_weights(local: &[F128], beta: F128) -> Vec<F128> {
    let eq = eq_table(local);
    let mut w = vec![F128::ZERO; BITS];
    for j in 0..BITS {
        w[j] += eq[j];
        w[along(j, 1)] += beta * eq[j];
        w[along(j, 2)] += beta.square() * eq[j];
    }
    linear_transpose(&w)
}
