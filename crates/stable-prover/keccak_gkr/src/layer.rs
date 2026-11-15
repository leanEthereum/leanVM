//! One layer: a claim on the states after a round becomes one on the states before it, in the order
//! `crates/verifier`'s `verify_layer` reads it (Annex C, `keccak:layer`):
//!
//! 1. the product polynomial `U` ([`product`]);
//! 2. its evaluation point `s`;
//! 3. a sumcheck over the pack and the segment: its first four rounds from one pass over the witness ([`skip`]),
//!    the others on a table of field elements that each round folds ([`table`]);
//! 4. a sumcheck over the bit position, on tables of 2048;
//! 5. `beta`, which batches what that leaves into one claim, which the linear map takes to the round's input.

use primitives::field::F128;
use primitives::multilinear::poly_eval;
use primitives::transcript::ProverState;
use verifier::PRODUCT_BITS;

use crate::keccak::{BITS, LOCAL_VARS, along};
use crate::open::fold;
use crate::protocol::{Claim, instance_weights, next_weights};
use crate::table::{Summand, Tables};
use crate::witness::Witness;
use crate::{product, skip, table};

/// Prove one layer: a claim on the states `step` layers below the outputs becomes one on the states a layer further
/// down. `tables` is the table step 3 folds, allocated once for every layer.
pub(crate) fn prove_layer(
    ps: &mut ProverState,
    witness: &Witness,
    step: usize,
    claim: &Claim,
    tables: &mut Tables,
) -> Claim {
    let layer = Layer::new(witness, step);

    // 1. The product polynomial.
    let (product, per_pack) = tracing::info_span!("Product").in_scope(|| product::polynomial(&layer, claim));
    ps.add_scalars(&product);

    // 2. `s`: the product polynomial has degree PRODUCT_BITS - 1.
    ps.grind(fiat_shamir::grinding_bits(PRODUCT_BITS as u128 - 1));
    let s = ps.sample();
    let mu = instance_weights(s);
    let kappa = mu.iter().sum();
    let mut sumcheck = Sumcheck {
        value: poly_eval(&product, s),
        scale: F128::ONE,
        point: Vec::with_capacity(claim.point.len()),
    };

    // 3. The pack and the segment.
    let sums = tracing::info_span!("Skip").in_scope(|| skip::sums(&layer, claim, s, &per_pack));
    skip::prove_rounds(ps, claim, sums, &mut sumcheck);
    let summand = Summand::new(claim, kappa);
    let values =
        tracing::info_span!("Tables").in_scope(|| table::fill(&layer, claim, &summand, &mu, &sumcheck.point, tables));
    let folded = tracing::info_span!("Tail")
        .in_scope(|| table::prove_rounds(ps, claim, &summand, values, tables, &mut sumcheck));

    // 4. The bit position.
    let (local, t) = prove_positions(ps, &claim.weights, folded, kappa, sumcheck.scale);
    ps.add_scalars(&t);

    // 5. `beta`: the next claim is quadratic in it.
    ps.grind(fiat_shamir::grinding_bits(2));
    let beta = ps.sample();
    Claim {
        mu,
        point: sumcheck.point,
        weights: next_weights(&local, beta),
    }
}

/// The states a layer's passes walk: a task per segment and block held by the witness, the blocks after the
/// written ones all standing for the padding block, which is walked once.
pub(crate) struct Layer<'a> {
    witness: &'a Witness,
    /// Per segment, the round whose `chi` its claim is on.
    rounds: Vec<usize>,
}

impl<'a> Layer<'a> {
    fn new(witness: &'a Witness, step: usize) -> Self {
        let shape = witness.shape;
        let rounds = (0..shape.segments()).map(|m| shape.round(m, step)).collect();
        Self { witness, rounds }
    }

    pub fn segments(&self) -> usize {
        self.rounds.len()
    }

    pub fn n_blocks(&self) -> usize {
        self.witness.shape.n_blocks()
    }

    /// The blocks holding inputs: every later one is the padding block.
    pub fn written(&self) -> usize {
        self.witness.written
    }

    pub fn n_tasks(&self) -> usize {
        self.segments() * self.witness.held()
    }

    /// Block `g` of segment `segment`'s state, sliced: the padding block for every `g` past the written ones.
    pub fn state(&self, segment: usize, g: usize) -> &'a [u64] {
        self.witness.layer(self.rounds[segment], g)
    }

    /// Task `held * segment + g`'s block.
    pub fn task(&self, task: usize) -> &'a [u64] {
        let held = self.witness.held();
        self.state(task / held, task % held)
    }

    /// Each task's weight in `eq`, a table over the blocks then the segment: the padding block's is the sum over
    /// the blocks it stands for.
    pub fn task_weights(&self, eq: &[F128]) -> Vec<F128> {
        let (n_blocks, written) = (self.n_blocks(), self.written());
        let eq = |segment: usize| &eq[n_blocks * segment..][..n_blocks];
        (0..self.segments())
            .flat_map(|m| {
                let padding = (written < n_blocks).then(|| eq(m)[written..].iter().sum());
                eq(m)[..written].iter().copied().chain(padding)
            })
            .collect()
    }
}

/// The sumcheck over the pack and the segment as it runs: the claim's `eq` factor on each bound variable has moved
/// into `scale`, and `value` is what the rounds still to come must sum to.
pub(crate) struct Sumcheck {
    pub value: F128,
    pub scale: F128,
    pub point: Vec<F128>,
}

impl Sumcheck {
    /// Send the next round, whose polynomial before `scale` and the `eq` factor on its variable has the values `zero`,
    /// `one` and `infinity` at `0`, `1` and infinity, and bind its variable, the claim's coordinate on which is `r`.
    /// Returns the challenge. Without `one`, `value = (1 + r) h(0) + r h(1) = c0 + r (c1 + c2)` gives the coefficient
    /// the other values do not, which needs `r` nonzero.
    pub fn round(&mut self, ps: &mut ProverState, zero: F128, one: Option<F128>, infinity: F128, r: F128) -> F128 {
        let (c0, c2) = (self.scale * zero, self.scale * infinity);
        let c1 = match one {
            Some(one) => self.scale * (zero + one + infinity),
            None => (self.value + c0) * r.inv() + c2,
        };
        let coeffs = [c0, c1, c2];
        ps.add_round_poly(&coeffs, true);
        let challenge = ps.sample();
        let eq = F128::ONE + r + challenge;
        self.value = eq * poly_eval(&coeffs, challenge);
        self.scale *= eq;
        self.point.push(challenge);
        challenge
    }
}

/// Step 4: the sumcheck of `scale * sum over j of w[j] (kappa T[j] + (kappa + T[j + 1]) T[j + 2])` over the bit
/// position, `T` being `folded`, the state at the bound pack and segment. Returns its point and `T`, `T[j + 1]` and
/// `T[j + 2]` there.
fn prove_positions(
    ps: &mut ProverState,
    weights: &[F128],
    folded: Vec<F128>,
    kappa: F128,
    scale: F128,
) -> (Vec<F128>, [F128; 3]) {
    let cube = 1 << LOCAL_VARS;
    let shift = |k: usize| -> Vec<F128> {
        (0..cube)
            .map(|j| if j < BITS { folded[along(j, k)] } else { F128::ZERO })
            .collect()
    };
    let mut t: [Vec<F128>; 3] = [0, 1, 2].map(shift);
    let mut w = weights.to_vec();
    w.resize(cube, F128::ZERO);
    let mut point = Vec::with_capacity(LOCAL_VARS);
    for _ in 0..LOCAL_VARS {
        ps.add_round_poly(&position_round(&w, &t, kappa).map(|c| scale * c), false);
        let challenge = ps.sample();
        point.push(challenge);
        w = fold(&w, 1, challenge);
        t = t.map(|v| fold(&v, 1, challenge));
    }
    (point, t.map(|v| v[0]))
}

/// The coefficients of a round of step 4 in the variable it binds, the lowest.
fn position_round(w: &[F128], t: &[Vec<F128>; 3], kappa: F128) -> [F128; 4] {
    let mut h = [F128::ZERO; 4];
    for i in 0..w.len() / 2 {
        // Each factor as `a + b X`.
        let line = |v: &[F128]| (v[2 * i], v[2 * i] + v[2 * i + 1]);
        let (w, t0, t1, t2) = (line(w), line(&t[0]), line(&t[1]), line(&t[2]));
        let u = (kappa + t1.0, t1.1);
        let a = [
            kappa * t0.0 + u.0 * t2.0,
            kappa * t0.1 + u.0 * t2.1 + u.1 * t2.0,
            u.1 * t2.1,
        ];
        h[0] += w.0 * a[0];
        h[1] += w.0 * a[1] + w.1 * a[0];
        h[2] += w.0 * a[2] + w.1 * a[1];
        h[3] += w.1 * a[2];
    }
    h
}
