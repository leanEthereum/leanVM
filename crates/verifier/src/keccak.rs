//! Keccak, by GKR over its rounds: a claim on the permutation's output, `depth` layers down to openings of the
//! committed states.
//!
//! A claim is a weighted sum of the bits of one state per segment: the weight of bit `j` of instance `i` of pack `y`
//! in segment `m` is `eq(point, (y, m)) * weights[j] * mu[i]`. A pack is sixteen consecutive steps.

use crate::field::{E, ONE, ZERO};
use crate::hash::{KECCAK_PI, KECCAK_RC, KECCAK_RHO, ROUNDS, STATE_LANES};
use crate::layout::K_BITS;
use crate::multilinear::{dot, eq_kernel, log2_ceil, multilinear_eval, poly_eval};
use crate::transcript::{Transcript, sumcheck};
use crate::{VerifierError, require};

const PACK_BITS: usize = 4;
const PACK: usize = 1 << PACK_BITS;
const EMBED_BITS: usize = 24;
const PRODUCT_BITS: usize = 2 * EMBED_BITS - 1;
const BITS: usize = 64 * STATE_LANES;
const LOCAL_BITS: usize = 11; // a bit position is z + 64 * lane, in a cube of 2048
const LANE_BITS: usize = 5;

/// Sixteen bits embed in a binary polynomial of degree at most 23, and a product of two embeddings projects to the
/// AND of what they embed: each unit vector's embedding, and per bit of the projection the product coefficients it is
/// the parity of. Derived in `python-verifier/verifier.py`, `_rmfe`.
const RMFE_EMBED: [u32; PACK] = [
    0x40c50b, 0x7f79f2, 0x4b4e0a, 0x72740c, 0x5357da, 0x1d1c9e, 0x04be6e, 0x785246, 0x097cdc, 0x109e7e, 0x1f1454,
    0x213cfc, 0x4cfcc8, 0x775770, 0x187386, 0x818a16,
];
const RMFE_PROJECT: [u64; PACK] = [
    0x1,
    0x7fffffffffff,
    0x274e9d3a74e9,
    0x1d3a74e9d3a7,
    0x65cb972e5cb9,
    0x5cb972e5cb97,
    0x6690aec7cd21,
    0x5d8f9a42bb1f,
    0x73485763e690,
    0x3750967c6ea1,
    0x12cf8dd4259f,
    0x1ba84b3e3750,
    0x0ad0c9f715a1,
    0x064fb8ad0c9f,
    0x456864fb8ad0,
    0x400000000000,
];

/// A batch: `2^log_steps` permutations, a state committed every `depth` rounds.
#[derive(Clone, Copy, Debug)]
pub struct KeccakShape {
    pub log_steps: usize,
    pub depth: usize,
}

impl KeccakShape {
    fn segments(&self) -> usize {
        ROUNDS / self.depth
    }

    fn pack_bits(&self) -> usize {
        self.log_steps - PACK_BITS
    }

    /// The slot index of q_keccak: lane `l` of the state segment `m` starts from is slot `25 m + l`.
    pub fn slot_bits(&self) -> usize {
        log2_ceil((STATE_LANES * self.segments()) as u64)
    }
}

struct Claim {
    value: E,
    mu: Vec<E>,      // the weight of each instance of a pack
    point: Vec<E>,   // a pack index, then a segment index
    weights: Vec<E>, // the weight of each bit position
}

/// The position `k` columns along from `j`, in the same row and slice.
fn along(j: usize, k: usize) -> usize {
    let (lane, z) = (j / 64, j % 64);
    64 * ((lane % 5 + k) % 5 + 5 * (lane / 5)) + z
}

/// The transpose of theta, rho, pi on weight vectors: `<w, L(a)> = <L^T(w), a>`.
fn linear_transpose(w: &[E]) -> Vec<E> {
    let mut g = vec![ZERO; BITS]; // the weight each position of theta's output carries
    for lane in 0..STATE_LANES {
        for z in 0..64 {
            g[64 * lane + z] = w[64 * KECCAK_PI[lane] + (z + KECCAK_RHO[lane] as usize) % 64];
        }
    }
    let mut columns = vec![ZERO; 5 * 64];
    for (j, &weight) in g.iter().enumerate() {
        columns[64 * (j / 64 % 5) + j % 64] += weight;
    }
    (0..BITS)
        .map(|j| {
            let (x, z) = (j / 64 % 5, j % 64);
            g[j] + columns[64 * ((x + 1) % 5) + z] + columns[64 * ((x + 4) % 5) + (z + 1) % 64]
        })
        .collect()
}

/// The instance weights of a claim made at the polynomial point `s`: each unit vector's embedding at `s`.
fn instance_weights(s: E) -> Vec<E> {
    let mut powers = [ONE; EMBED_BITS];
    for b in 1..EMBED_BITS {
        powers[b] = powers[b - 1] * s;
    }
    RMFE_EMBED
        .iter()
        .map(|&e| E::sum((0..EMBED_BITS).filter(|b| e >> b & 1 == 1).map(|b| powers[b])))
        .collect()
}

/// A claim on the states `step` layers below the committed outputs becomes one on the states a layer further down.
fn verify_layer(
    transcript: &mut Transcript,
    shape: KeccakShape,
    step: usize,
    claim: &Claim,
) -> Result<Claim, VerifierError> {
    // 1] The product polynomial: the claim's weighted sum of the packs' unprojected chi.
    let product = transcript.next_scalars(PRODUCT_BITS)?;
    if transcript.checked() {
        let projected = E::sum((0..PRODUCT_BITS).map(|c| {
            let functional = E::sum(
                (0..PACK)
                    .filter(|&i| RMFE_PROJECT[i] >> c & 1 == 1)
                    .map(|i| claim.mu[i]),
            );
            functional * product[c]
        }));
        // iota flips known positions of lane 0 in every instance.
        let segments = eq_kernel(&claim.point[shape.pack_bits()..]);
        let mut iota = ZERO;
        for (segment, &weight) in segments.iter().enumerate().take(shape.segments()) {
            let constant = KECCAK_RC[shape.depth * (segment + 1) - step - 1];
            iota += weight * E::sum((0..64).filter(|z| constant >> z & 1 == 1).map(|z| claim.weights[z]));
        }
        require(
            projected + iota * E::sum(claim.mu.iter().copied()) == claim.value,
            VerifierError::KeccakProduct,
        )?;
    }

    // 2] At a random point a pack is one field element, and the polynomial's value a sumcheck claim.
    let s = transcript.sample();
    let mu = instance_weights(s);
    let kappa = E::sum(mu.iter().copied());
    let mut value = poly_eval(&product, s);

    // 3] The pack and the segment.
    let mut scale = ONE;
    let mut point = Vec::with_capacity(claim.point.len());
    for &r in &claim.point {
        let message = transcript.sumcheck_round_poly(3, value, Some(r))?;
        let challenge = transcript.sample();
        value = (ONE + r + challenge) * poly_eval(&message, challenge);
        scale *= ONE + r + challenge;
        point.push(challenge);
    }

    // 4] The bit position: `sum_j w[j] (kappa T[j] + (kappa + T[j + 1]) T[j + 2])`, the weights one more multilinear factor.
    let (local, value) = sumcheck(transcript, value, 4, &[None; LOCAL_BITS])?;
    let t = transcript.next_scalars(3)?;
    let eq = eq_kernel(&local);
    if transcript.checked() {
        require(
            scale * dot(&eq[..BITS], &claim.weights) * (kappa * t[0] + (kappa + t[1]) * t[2]) == value,
            VerifierError::KeccakLayer,
        )?;
    }

    // 5] `t[k] = sum_j eq[j] T[j + k]`: one claim on the state before chi, then on the round's input through the linear map.
    // Position `j` is `k` columns along from `along(j, 5 - k)`.
    let beta = transcript.sample();
    let weights: Vec<E> = (0..BITS)
        .map(|j| eq[j] + beta * (eq[along(j, 4)] + beta * eq[along(j, 3)]))
        .collect();
    Ok(Claim {
        value: t[0] + beta * (t[1] + beta * t[2]),
        mu,
        point,
        weights: linear_transpose(&weights),
    })
}

/// The weight a claim puts on each `(slot, z)`: its position weights on the slots of the states it speaks of, scaled
/// by the segment. `first` is the state segment 0 claims, and only the first `count` segments' states are committed.
fn slot_weights(shape: KeccakShape, claim: &Claim, first: usize, count: usize) -> Vec<[E; 64]> {
    let segments = eq_kernel(&claim.point[shape.pack_bits()..]);
    let mut rows = vec![[ZERO; 64]; 1 << shape.slot_bits()];
    for segment in 0..count {
        for j in 0..BITS {
            rows[STATE_LANES * (first + segment) + j / 64][j % 64] = segments[segment] * claim.weights[j];
        }
    }
    rows
}

/// A sumcheck over the slot: the point it ends on, the weight the claim puts on each slice there, and what is left to match.
fn open(
    transcript: &mut Transcript,
    shape: KeccakShape,
    claim: &Claim,
    first: usize,
    count: usize,
    value: E,
) -> Result<(Vec<E>, [E; 64], E), VerifierError> {
    let (slot, value) = sumcheck(transcript, value, 3, &vec![None; shape.slot_bits()])?;
    let mut rows = slot_weights(shape, claim, first, count);
    for &challenge in &slot {
        rows = rows
            .chunks(2)
            .map(|pair| std::array::from_fn(|z| pair[0][z] + challenge * (pair[0][z] + pair[1][z])))
            .collect();
    }
    Ok((slot, rows[0], value))
}

/// What the reduction leaves: the committed segment outputs as words at one point of q_keccak, if any segment's
/// output is committed, and the column's 64 slices at another.
pub struct KeccakOpenings {
    pub outputs: Option<(Vec<E>, E)>,
    pub inputs: (Vec<E>, Vec<E>),
}

/// The reduction: a random claim on every segment's output at `instance`, `depth` layers down to the committed inputs.
/// The last segment's output is the permutation's, claimed by `output`, its lanes as words at `instance`; the others
/// are committed.
pub fn verify_keccak(
    transcript: &mut Transcript,
    shape: KeccakShape,
    instance: &[E],
    output: &[E],
) -> Result<KeccakOpenings, VerifierError> {
    // `replay_unchecked` reaches this with a child's announced shape, where the contract is an error and
    // never a panic. The pack bound is what keeps `pack_bits` below from underflowing.
    require(
        instance.len() == shape.log_steps && output.len() == STATE_LANES && shape.log_steps >= PACK_BITS,
        VerifierError::AnnouncedTableSizes,
    )?;
    let segment = transcript.samples(log2_ceil(shape.segments() as u64));
    let point = [&instance[PACK_BITS..], &segment[..]].concat();
    // The first claim combines the output lanes as words: bit z of a word weighs x^z.
    let lanes = eq_kernel(&transcript.samples(LANE_BITS));
    let weights = (0..BITS).map(|j| lanes[j / 64] * E::new(1 << (j % 64), 0, 0)).collect();
    let last = eq_kernel(&segment)[shape.segments() - 1] * dot(&lanes[..STATE_LANES], output);
    let committed = if shape.segments() > 1 {
        transcript.next_scalar()?
    } else {
        ZERO
    };
    let first = Claim {
        value: committed + last,
        mu: eq_kernel(&instance[..PACK_BITS]),
        point,
        weights,
    };
    let mut claim = verify_layer(transcript, shape, 0, &first)?;
    for step in 1..shape.depth {
        claim = verify_layer(transcript, shape, step, &claim)?;
    }

    // The committed outputs, whose instance weights are an eq already: slice 0 holds the slot's weight, the others x^z times it.
    let mut outputs = None;
    if shape.segments() > 1 {
        let (slot, weights, value) = open(transcript, shape, &first, 1, shape.segments() - 1, committed)?;
        let word = transcript.next_scalar()?;
        if transcript.checked() {
            require(weights[0] * word == value, VerifierError::KeccakOutputOpening)?;
        }
        outputs = Some(([instance, &slot].concat(), word));
    }
    // The inputs: the instances of a pack first, then the slot.
    let (low, value) = sumcheck(transcript, claim.value, 3, &[None; PACK_BITS])?;
    let (slot, weights, value) = open(transcript, shape, &claim, 0, shape.segments(), value)?;
    let slices = transcript.next_scalars(K_BITS)?;
    if transcript.checked() {
        require(
            multilinear_eval(&claim.mu, &low)? * dot(&weights, &slices) == value,
            VerifierError::KeccakInputOpening,
        )?;
    }
    let point = [&low, &claim.point[..shape.pack_bits()], &slot].concat();
    Ok(KeccakOpenings {
        outputs,
        inputs: (point, slices),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn carryless(a: u64, b: u64) -> u64 {
        (0..64).filter(|i| b >> i & 1 == 1).fold(0, |acc, i| acc ^ a << i)
    }

    /// A product of two embeddings projects to the AND of the bits they embed.
    #[test]
    fn the_embedding_projects_products_to_and() {
        let embed = |a: u16| {
            (0..PACK)
                .filter(|i| a >> i & 1 == 1)
                .fold(0, |acc, i| acc ^ RMFE_EMBED[i] as u64)
        };
        let project = |p: u64| {
            (0..PACK).fold(0u16, |acc, i| {
                acc | (((p & RMFE_PROJECT[i]).count_ones() & 1) as u16) << i
            })
        };
        let mut x = 0x9E37_79B9_7F4A_7C15u64;
        for _ in 0..1000 {
            x = x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let (a, b) = ((x >> 16) as u16, (x >> 40) as u16);
            assert_eq!(project(carryless(embed(a), embed(b))), a & b, "{a:#x} {b:#x}");
        }
    }
}
