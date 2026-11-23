//! Phase 6: `KECCAK`'s validity, by GKR over its rounds (`NativeVm/Model/KeccakGkr.lean`). A
//! claim's 1600 bit weights live in the scratch (`KeccakScratch`), the rest of it on the stack.

use crate::buf::Buf;
use crate::data::{KECCAK_RC, KECCAK_RHO, RMFE_EMBED, RMFE_PROJECT};
use crate::field::{EW, ZERO, dot, eq_kernel, multilinear_eval, poly_eval, powers, sum_e};
use crate::layout::{LayoutW, OP_KECCAK, QKECCAK, QKECCAK_SLOT_BITS};
use crate::stack::{ClaimsW, POINT_CAP, push_claim};
use crate::tables::{TABLE_POINT_CAP, TableEvalW};
use crate::transcript::{TState, grinding_bits, require};

/// `keccakBits`.
const BITS: usize = 1600;
/// `keccakLocalBits`.
const LOCAL_BITS: usize = 11;
/// `keccakDepth`, `keccakSegments`, `keccakSegmentBits`, `keccakLaneBits`.
const DEPTH: usize = 12;
const SEGMENTS: usize = 2;
const SEGMENT_BITS: usize = 1;
const LANE_BITS: usize = 5;
/// `embedBits`, `productBits`.
const EMBED_BITS: usize = 24;
const PRODUCT_BITS: usize = 2 * EMBED_BITS - 1;
/// The instance weights: one per entry of `RMFE_EMBED`.
const MU: usize = RMFE_EMBED.len();
/// `kBits`.
const K_BITS: usize = 64;
/// `keccakOut`: the local column of output lane `0`.
const KECCAK_OUT: usize = 40;
/// A claim's point: the pack index (`logSteps - 4` coordinates) and the segment.
const CLAIM_POINT_CAP: usize = TABLE_POINT_CAP;
/// The slots of `q_keccak`.
const SLOTS: usize = 1 << QKECCAK_SLOT_BITS;

/// `keccakPi`.
#[inline(never)]
const fn keccak_pi(i: usize) -> usize {
    i / 5 + 5 * ((2 * (i % 5) + 3 * (i / 5)) % 5)
}

/// The phase's scratch (`scratchR`): the first claim's and the running claim's bit weights, a
/// layer's weights before the transpose, `linear_transpose`'s `g` and columns, the local equality
/// kernel, the slot weights.
#[repr(C)]
pub struct KeccakScratch {
    first_weights: [EW; BITS],
    weights: [EW; BITS],
    layer_weights: [EW; BITS],
    g: [EW; BITS],
    columns: [EW; 5 * 64],
    eq: [EW; 1 << LOCAL_BITS],
    rows: [[EW; 64]; SLOTS],
}

/// `KeccakClaimW` but its bit weights: the value, the instance weights, the point.
#[derive(Clone, Copy)]
#[repr(C)]
struct KeccakClaimW {
    value: EW,
    mu: Buf<EW, MU>,
    point: Buf<EW, CLAIM_POINT_CAP>,
}

/// `keccakOut` (`KeccakOutAt`): `q_keccak`'s point and its 64 slices, which ring switching takes.
#[repr(C)]
pub struct KeccakOutW {
    pub point: Buf<EW, POINT_CAP>,
    pub slices: [EW; K_BITS],
}

/// Bit `b` of a word (`testBitW`).
#[inline(always)]
fn test_bit(w: u64, b: usize) -> bool {
    b < 64 && (w >> b) & 1 == 1
}

/// `keccakAlong j k`: the position `k` columns along from `j`.
#[inline(always)]
fn along(j: usize, k: usize) -> usize {
    let (lane, z) = (j / 64, j % 64);
    64 * ((lane % 5 + k) % 5 + 5 * (lane / 5)) + z
}

/// `keccakLinearTranspose`: the transpose of θ, ρ, π on weight vectors, `w` into `out`.
#[inline(never)]
fn linear_transpose(w: &[EW; BITS], g: &mut [EW; BITS], columns: &mut [EW; 5 * 64], out: &mut [EW; BITS]) {
    for lane in 0..25 {
        let (pi, rho) = (keccak_pi(lane), KECCAK_RHO[lane] as usize);
        for z in 0..64 {
            g[64 * lane + z] = w[(64 * pi + (z + rho) % 64) % BITS];
        }
    }
    for x in 0..5 {
        for z in 0..64 {
            let mut sum = ZERO;
            for y in 0..5 {
                sum = sum + g[64 * (x + 5 * y) + z];
            }
            columns[64 * x + z] = sum;
        }
    }
    for lane in 0..25 {
        for z in 0..64 {
            out[64 * lane + z] =
                g[64 * lane + z] + columns[64 * ((lane % 5 + 1) % 5) + z] + columns[64 * ((lane % 5 + 4) % 5) + (z + 1) % 64];
        }
    }
}

/// `keccakInstanceWeights s`: each unit vector's embedding at `s`.
#[inline(never)]
fn instance_weights(s: EW) -> Buf<EW, MU> {
    let mut s_powers = [ZERO; EMBED_BITS];
    powers(s, &mut s_powers);
    let mut mu = Buf { len: MU, items: [ZERO; MU] };
    for (m, &e) in mu.items.iter_mut().zip(&RMFE_EMBED) {
        *m = s_powers.iter().enumerate().fold(ZERO, |acc, (b, &p)| if test_bit(e, b) { acc + p } else { acc });
    }
    mu
}

/// The equality kernel of a claim's segment coordinates, `claim.point.extract packBits`.
#[inline(always)]
fn segment_kernel(point: &[EW], pack_bits: usize, out: &mut [EW; 4]) -> Option<()> {
    eq_kernel(point.get(pack_bits..).unwrap_or(&[]), out).map(|_| ())
}

/// `verifyKeccakLayer logSteps step claim`, the claim's bit weights `scratch.weights`, replaced.
#[inline(never)]
fn verify_layer(t: &mut TState, log_steps: usize, step: usize, claim: &mut KeccakClaimW, scratch: &mut KeccakScratch) -> Option<()> {
    let pack_bits = log_steps.saturating_sub(4);
    let mut product = [ZERO; PRODUCT_BITS];
    t.read_scalars(&mut product)?;
    let mu = claim.mu.as_slice();
    let mut projected = ZERO;
    for (c, &p) in product.iter().enumerate() {
        let masked = mu.iter().zip(&RMFE_PROJECT).fold(ZERO, |acc, (&m, &mask)| if test_bit(mask, c) { acc + m } else { acc });
        projected = projected + masked * p;
    }
    let mut segments = [ZERO; 4];
    segment_kernel(claim.point.as_slice(), pack_bits, &mut segments)?;
    let mut iota = ZERO;
    for (segment, &weight) in segments.iter().enumerate().take(SEGMENTS) {
        let round = (DEPTH * (segment + 1)).checked_sub(step + 1);
        let constant = round.and_then(|r| KECCAK_RC.get(r).copied()).unwrap_or(0);
        let bits = scratch.weights[..64].iter().enumerate().fold(ZERO, |acc, (z, &w)| if test_bit(constant, z) { acc + w } else { acc });
        iota = iota + weight * bits;
    }
    require(projected + iota * sum_e(mu) == claim.value)?;
    t.grind(grinding_bits(PRODUCT_BITS as u64 - 1))?;
    let s = t.sample_challenge();
    let mu = instance_weights(s);
    let kappa = sum_e(mu.as_slice());
    let mut point = [ZERO; CLAIM_POINT_CAP];
    let old = claim.point.as_slice();
    let point = point.get_mut(..old.len())?;
    let value = t.sumcheck(poly_eval(&product, s), 3, |i| old.get(i).copied(), point)?;
    let mut local_point = [ZERO; LOCAL_BITS];
    let value = t.sumcheck_plain(value, 4, &mut local_point)?;
    let mut tv = [ZERO; 3];
    t.read_scalars(&mut tv)?;
    eq_kernel(&local_point, &mut scratch.eq)?;
    let eq = &scratch.eq;
    let [t0, t1, t2] = tv;
    require(dot(&eq[..BITS], &scratch.weights) * (kappa * t0 + (kappa + t1) * t2) == value)?;
    t.grind(grinding_bits(2))?;
    let beta = t.sample_challenge();
    for (j, w) in scratch.layer_weights.iter_mut().enumerate() {
        let at = |i: usize| eq.get(i).copied().unwrap_or(ZERO);
        *w = at(j) + beta * (at(along(j, 4)) + beta * at(along(j, 3)));
    }
    linear_transpose(&scratch.layer_weights, &mut scratch.g, &mut scratch.columns, &mut scratch.weights);
    claim.value = t0 + beta * (t1 + beta * t2);
    claim.mu = mu;
    claim.point.set(point)?;
    Some(())
}

/// `keccakSlotWeights logSteps claim first count`: the weight a claim (its point, its bit weights
/// `weights`) puts on each `(slot, z)`, into `rows`.
#[inline(never)]
fn slot_weights(log_steps: usize, point: &[EW], weights: &[EW; BITS], first: usize, count: usize, rows: &mut [[EW; 64]; SLOTS]) -> Option<()> {
    let mut segments = [ZERO; 4];
    segment_kernel(point, log_steps.saturating_sub(4), &mut segments)?;
    for row in rows.iter_mut() {
        *row = [ZERO; 64];
    }
    for segment in 0..count {
        let scale = segments.get(segment).copied().unwrap_or(ZERO);
        for (j, &w) in weights.iter().enumerate() {
            if let Some(row) = rows.get_mut(25 * (first + segment) + j / 64) {
                row[j % 64] = scale * w;
            }
        }
    }
    Some(())
}

/// `keccakOpen logSteps claim first count value`: a sumcheck over the slot into `slot`; the weight
/// on each slice there (`rows[0]` after the fold), and what is left to match.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn keccak_open(
    t: &mut TState,
    log_steps: usize,
    point: &[EW],
    weights: &[EW; BITS],
    first: usize,
    count: usize,
    value: EW,
    slot: &mut [EW; QKECCAK_SLOT_BITS],
    rows: &mut [[EW; 64]; SLOTS],
) -> Option<EW> {
    let value = t.sumcheck_plain(value, 3, slot)?;
    slot_weights(log_steps, point, weights, first, count, rows)?;
    let mut size = SLOTS;
    for &challenge in slot.iter() {
        for i in 0..size / 2 {
            let (lo, hi) = (rows[2 * i], rows[2 * i + 1]);
            for (k, out) in rows[i].iter_mut().enumerate() {
                *out = lo[k] + challenge * (lo[k] + hi[k]);
            }
        }
        size /= 2;
    }
    Some(value)
}

/// `keccakFirstClaim inst segment lanePoint output committed`, its bit weights into `weights`.
#[inline(never)]
fn first_claim(
    inst: &[EW],
    segment: &[EW; SEGMENT_BITS],
    lane_point: &[EW; LANE_BITS],
    output: &[EW; 25],
    committed: EW,
    weights: &mut [EW; BITS],
) -> Option<KeccakClaimW> {
    let mut lanes = [ZERO; 1 << LANE_BITS];
    eq_kernel(lane_point, &mut lanes)?;
    for (j, w) in weights.iter_mut().enumerate() {
        *w = lanes[(j / 64) % 32] * EW::of_k(1u64 << (j % 64));
    }
    let mut segments = [ZERO; 1 << SEGMENT_BITS];
    eq_kernel(segment, &mut segments)?;
    let last = segments[SEGMENTS - 1] * dot(&lanes[..25], output);
    let mut mu = Buf { len: 0, items: [ZERO; MU] };
    let low = inst.get(..4).unwrap_or(inst);
    let n = eq_kernel(low, &mut mu.items)?;
    mu.len = n;
    let mut point = Buf { len: 0, items: [ZERO; CLAIM_POINT_CAP] };
    point.set(inst.get(4..).unwrap_or(&[]))?;
    point.extend(segment)?;
    Some(KeccakClaimW { value: committed + last, mu, point })
}

/// `verifyKeccak logSteps inst output`: the committed outputs' column claim appended to `claims`,
/// `q_keccak`'s point and slices into `out`.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn verify_keccak(
    t: &mut TState,
    log_steps: usize,
    inst: &[EW],
    output: &[EW; 25],
    scratch: &mut KeccakScratch,
    claims: &mut ClaimsW,
    out: &mut KeccakOutW,
) -> Option<()> {
    let pack_bits = log_steps.saturating_sub(4);
    let r_low = inst.get(..4).unwrap_or(inst);
    let r_high = inst.get(4..).unwrap_or(&[]);
    t.grind(grinding_bits((SEGMENT_BITS + LANE_BITS) as u64))?;
    let mut segment = [ZERO; SEGMENT_BITS];
    t.sample_challenges(&mut segment);
    let mut lane_point = [ZERO; LANE_BITS];
    t.sample_challenges(&mut lane_point);
    let committed = t.read_scalar()?;
    let first = first_claim(inst, &segment, &lane_point, output, committed, &mut scratch.first_weights)?;
    // `keccakLayers`.
    let mut claim = first;
    scratch.weights = scratch.first_weights;
    for step in 0..DEPTH {
        verify_layer(t, log_steps, step, &mut claim, scratch)?;
    }
    let mut slot = [ZERO; QKECCAK_SLOT_BITS];
    let value = keccak_open(
        t,
        log_steps,
        first.point.as_slice(),
        &scratch.first_weights,
        1,
        SEGMENTS - 1,
        committed,
        &mut slot,
        &mut scratch.rows,
    )?;
    let word = t.read_scalar()?;
    require(scratch.rows[0][0] * word == value)?;
    let mut output_point = Buf { len: 0, items: [ZERO; POINT_CAP] };
    output_point.set(r_low)?;
    output_point.extend(r_high)?;
    output_point.extend(&slot)?;
    push_claim(claims, QKECCAK, output_point.as_slice(), word)?;
    let mut low = [ZERO; 4];
    let value = t.sumcheck_plain(claim.value, 3, &mut low)?;
    let value = keccak_open(
        t,
        log_steps,
        claim.point.as_slice(),
        &scratch.weights,
        0,
        SEGMENTS,
        value,
        &mut slot,
        &mut scratch.rows,
    )?;
    t.read_scalars(&mut out.slices)?;
    require(multilinear_eval(claim.mu.as_slice(), &low) * dot(&scratch.rows[0], &out.slices) == value)?;
    let point = claim.point.as_slice();
    out.point.set(&low)?;
    out.point.extend(point.get(..pack_bits).unwrap_or(point))?;
    out.point.extend(&slot)
}

/// **Phase 6** (`keccakPhase`): `KECCAK`'s point and output lanes into `verifyKeccak`.
#[inline(never)]
pub fn keccak_phase(
    t: &mut TState,
    layout: &LayoutW,
    evals: &[TableEvalW],
    scratch: &mut KeccakScratch,
    claims: &mut ClaimsW,
    out: &mut KeccakOutW,
) -> Option<()> {
    let e = evals.get(OP_KECCAK)?;
    let values = e.values.as_slice();
    // `values.getD (keccakOut + lane) 0`: the lanes there copied, the others zero.
    let mut output = [ZERO; 25];
    let present = values.len().saturating_sub(KECCAK_OUT).min(25);
    output.get_mut(..present)?.copy_from_slice(values.get(KECCAK_OUT..KECCAK_OUT + present)?);
    verify_keccak(t, layout.table_log_heights[OP_KECCAK], e.point.as_slice(), &output, scratch, claims, out)
}
