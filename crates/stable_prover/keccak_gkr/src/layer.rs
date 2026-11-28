//! One layer: a claim on the states after a round becomes one on the states before it, in the order
//! `crates/verifier`'s `verify_layer` reads it (Annex C, `keccak:layer`):
//!
//! 1. the product polynomial `U` ([`product`]);
//! 2. its evaluation point `s`;
//! 3. a sumcheck over the pack and the segment: its first four rounds from one pass over the witness ([`skip`]),
//!    the others on a table of field elements that each round folds ([`table`]);
//! 4. a sumcheck over the bit position, on tables of 2048;
//! 5. `beta`, which batches what that leaves into one claim, which the linear map takes to the round's input.

use primitives::field::{F128, powers};
use primitives::multilinear::fold;
use primitives::transcript::ProverState;
use verifier::keccak::{BITS, LOCAL_BITS, PRODUCT_BITS};

use crate::kernels::{PACKS_LOG, along, eq_table, mul, poly_eval};
use crate::protocol::{Claim, instance_weights, next_weights};
use crate::skip::SKIP;
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
    let layer = Layer { witness, step };
    // The weights of a block's pairs of groups, by block then segment, and of the tasks: step 1 weighs a block by
    // them too, its packs' low variables being the skip's and the half.
    const { assert!(PACKS_LOG == SKIP + 1) };
    let eq = eq_table(&claim.point[PACKS_LOG..]);
    let tasks = layer.task_weights(&eq);

    // 1. The product polynomial.
    let (product, per_pack) = product::polynomial(&layer, claim, &tasks);
    ps.add_scalars(&product);

    // 2. `s`: the product polynomial has degree PRODUCT_BITS - 1.
    // Bad event, probability `2^-64`: `s` in `K` (which holds every proper subfield) has no power basis. A verifier
    // accepts any passing nonce, so the prover grinds on.
    let bits = fiat_shamir::grinding_bits(PRODUCT_BITS as u128 - 1);
    let s = ps.grind_sample(bits, |s| s.to_limbs()[1] != 0);
    let powers = powers(s, skip::COEFFS);
    let mu = instance_weights(&powers);
    let kappa = mu.iter().sum();
    let mut sumcheck = Sumcheck {
        value: poly_eval(&product, s),
        point: Vec::with_capacity(claim.point.len()),
    };

    // 3. The pack and the segment.
    let sums = skip::sums(&layer, claim, &powers, &tasks, &per_pack);
    skip::prove_rounds(ps, claim, sums, &mut sumcheck);
    let summand = Summand::new(claim, kappa);
    let values = table::fill(&layer, &summand, &mu, &sumcheck.point, &eq, tables);
    let folded = table::prove_rounds(ps, claim, &summand, values, tables, &mut sumcheck);

    // 4. The bit position.
    let (local, t) = prove_positions(ps, &claim.weights, folded, kappa);
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
    /// Layers below the outputs.
    step: usize,
}

impl<'a> Layer<'a> {
    pub fn segments(&self) -> usize {
        self.witness.shape.segments()
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

    /// Block `g` of segment `segment`'s state, sliced: the padding block for every `g` past the written ones. Out of
    /// line: one copy for every pass.
    #[inline(never)]
    pub fn state(&self, segment: usize, g: usize) -> &'a [u64] {
        self.witness.layer(self.witness.shape.round(segment, self.step), g)
    }

    /// Task `held * segment + g`'s block.
    pub fn task(&self, task: usize) -> &'a [u64] {
        let held = self.witness.held();
        self.state(task / held, task % held)
    }

    /// Each task's weight in `eq`, a table over the blocks then the segment: the padding block's is the sum over
    /// the blocks it stands for.
    pub fn task_weights(&self, eq: &[F128]) -> Vec<F128> {
        let (n_blocks, written, held) = (self.n_blocks(), self.written(), self.witness.held());
        let mut out = vec![F128::ZERO; self.n_tasks()];
        for (task, out) in out.iter_mut().enumerate() {
            let (segment, g) = (task / held, task % held);
            let end = if g < written { g + 1 } else { n_blocks };
            *out = eq[segment * n_blocks..][g..end].iter().sum();
        }
        out
    }
}

/// The normalized sumcheck over the pack and the segment: `value` is what the rounds still to come must sum to.
pub(crate) struct Sumcheck {
    pub value: F128,
    pub point: Vec<F128>,
}

impl Sumcheck {
    /// Send the next round, whose polynomial without the `eq` factor on its variable has the values `zero`,
    /// `one` and `infinity` at `0`, `1` and infinity, and bind its variable, the claim's coordinate on which is `r`.
    /// Returns the challenge. Without `one`, `value = (1 + r) h(0) + r h(1) = c0 + r (c1 + c2)` gives the coefficient
    /// the other values do not, which needs `r` nonzero. Out of line: one copy for both sumchecks.
    #[inline(never)]
    pub fn round(&mut self, ps: &mut ProverState, zero: F128, one: Option<F128>, infinity: F128, r: F128) -> F128 {
        let (c0, c2) = (zero, infinity);
        let c1 = match one {
            Some(one) => zero + one + infinity,
            None => mul(self.value + c0, r.inv()) + c2,
        };
        let coeffs = [c0, c1, c2];
        ps.add_round_poly(&coeffs, true);
        let challenge = ps.sample();
        self.value = poly_eval(&coeffs, challenge);
        self.point.push(challenge);
        challenge
    }
}

/// Step 4: the sumcheck of `sum over j of w[j] (kappa T[j] + (kappa + T[j + 1]) T[j + 2])` over the bit
/// position, `T` being `folded`, the state at the bound pack and segment. Returns its point and `T`, `T[j + 1]` and
/// `T[j + 2]` there.
fn prove_positions(ps: &mut ProverState, weights: &[F128], folded: Vec<F128>, kappa: F128) -> (Vec<F128>, [F128; 3]) {
    // Per position `j`, four in a row: `w`, then `T`, `T[j + 1]` and `T[j + 2]`, zero past the positions.
    let mut t = vec![F128::ZERO; 4 << LOCAL_BITS];
    for (j, t) in t.as_chunks_mut::<4>().0[..BITS].iter_mut().enumerate() {
        *t = [weights[j], folded[j], folded[along(j, 1)], folded[along(j, 2)]];
    }
    let mut point = Vec::with_capacity(LOCAL_BITS);
    for _ in 0..LOCAL_BITS {
        ps.add_round_poly(&position_round(&t, kappa), false);
        let challenge = ps.sample();
        point.push(challenge);
        t = fold(&t, 4, challenge);
    }
    (point, [t[1], t[2], t[3]])
}

/// The coefficients of a round of step 4 in the variable it binds, the lowest, from rows of `w` and the three shifts
/// of `T`.
fn position_round(t: &[F128], kappa: F128) -> [F128; 4] {
    let mut h = [F128::ZERO; 4];
    for pair in t.as_chunks::<8>().0 {
        // Each factor as `a + b X`.
        let line = |k: usize| [pair[k], pair[k] + pair[4 + k]];
        let t1 = line(2);
        // `kappa T[j] + (kappa + T[j + 1]) T[j + 2]`, then times the weight.
        let mut a = [F128::ZERO; 3];
        mul_add(&mut a, &[kappa], &line(1));
        mul_add(&mut a, &[kappa + t1[0], t1[1]], &line(3));
        mul_add(&mut h, &line(0), &a);
    }
    h
}

/// `acc += a * b`, polynomials with their constant coefficients first. Out of line: one copy for every product.
#[inline(never)]
fn mul_add(acc: &mut [F128], a: &[F128], b: &[F128]) {
    for (i, &a) in a.iter().enumerate() {
        for (acc, &b) in acc[i..].iter_mut().zip(b) {
            *acc += a * b;
        }
    }
}
