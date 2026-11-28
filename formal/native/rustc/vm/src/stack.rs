//! The claims the phases hand on (`NativeVm/Model/Claims.lean`) and phase 2, the stack's commitment
//! and its out-of-domain sample (`NativeVm/Model/Stack.lean`).

use crate::buf::Buf;
use crate::field::{EW, ONE, ZERO, eq_eval};
use crate::layout::{LayoutW, MAX_LOG_STACK, Placement, eq_above, stack_point};
use crate::transcript::TState;
use crate::whir::{Level, OOD_GRINDING_BITS, ladder};

/// `pointCap`: a column claim's point.
pub const POINT_CAP: usize = 36;
/// `claimCap`: every column claim.
pub const CLAIM_CAP: usize = 160;
/// `stackCap`: a point on the stack.
pub const STACK_CAP: usize = MAX_LOG_STACK;

/// `ColumnClaimW`: a global column, a point over its own variables, a value.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct ColumnClaimW {
    pub column: usize,
    pub point: Buf<EW, POINT_CAP>,
    pub value: EW,
}

/// The column claims (`ClaimsAt`), appended by phases 3 to 6.
pub type ClaimsW = Buf<ColumnClaimW, CLAIM_CAP>;

/// Append the claim `⟨column, point, value⟩`.
#[inline(never)]
pub fn push_claim(claims: &mut ClaimsW, column: usize, point: &[EW], value: EW) -> Option<()> {
    let slot = claims.items.get_mut(claims.len)?;
    slot.column = column;
    slot.point.set(point)?;
    slot.value = value;
    claims.len += 1;
    Some(())
}

/// `ringWeight r rPrime coefficients`: `Σ_k c_k Π_n (1 + r_n^(2^k) + r'_n)`, `r` squared in place.
#[inline(never)]
pub fn ring_weight(r: &[EW], r_prime: &[EW], coefficients: &[EW]) -> Option<EW> {
    let mut powers = [ZERO; POINT_CAP];
    let powers = powers.get_mut(..r.len())?;
    for (slot, &x) in powers.iter_mut().zip(r) {
        *slot = x;
    }
    let mut total = ZERO;
    for &c in coefficients {
        let product = powers.iter().zip(r_prime).fold(c, |p, (&v, &ch)| p * (ONE + v + ch));
        total = total + product;
        for v in powers.iter_mut() {
            *v = *v * *v;
        }
    }
    Some(total)
}

/// `StackWeight.eval` of `ColumnClaimW.onStack` (`eq (stackPoint placement c.point stackLog)`) at
/// `x`.
#[inline(never)]
pub fn column_weight(p: Placement, point: &[EW], stack_log: usize, x: &[EW]) -> Option<EW> {
    let mut z = [ZERO; POINT_CAP + STACK_CAP];
    let n = stack_point(p, point, stack_log, &mut z)?;
    Some(eq_eval(z.get(..n)?, x))
}

/// `StackWeight.eval` of `ringSwitchClaim`'s weight (`ring p r c`) at `x`.
#[inline(never)]
pub fn ring_claim_weight(p: Placement, r: &[EW], coefficients: &[EW], x: &[EW]) -> Option<EW> {
    let low = x.get(..p.variable_count).unwrap_or(x);
    Some(eq_above(p, x) * ring_weight(r, low, coefficients)?)
}

/// `EqClaimAt`: a stack claim `⟨.eq z, value⟩`.
#[repr(C)]
pub struct EqClaimW {
    pub z: Buf<EW, STACK_CAP>,
    pub value: EW,
}

/// `levelShape`: `2^(μ − fold + rate)` leaves of `width` words.
#[inline(always)]
pub fn level_shape(message_log_before: usize, level: &Level, width: u64) -> (u64, u64) {
    ((message_log_before.saturating_sub(level.fold) + level.log_inv_rate) as u64, width)
}

/// **`commitStack`**: the stack's root, read at level `0`'s shape.
#[inline(never)]
pub fn commit_stack(t: &mut TState, log_n: usize, log_inv_rate: usize) -> Option<()> {
    let (levels, n) = ladder(log_n, log_inv_rate)?;
    let level = levels.get(..n)?.first()?;
    let (height, width) = level_shape(log_n, level, 1u64 << level.fold);
    t.read_commitment(height, width)
}

/// **`readOod`**: the stack commitment's out-of-domain claim, into `out`.
#[inline(never)]
pub fn read_ood(t: &mut TState, stack_log: usize, out: &mut EqClaimW) -> Option<()> {
    t.grind(OOD_GRINDING_BITS)?;
    t.sample_challenges(out.z.resize(stack_log)?);
    out.value = t.read_scalar()?;
    Some(())
}

/// `ColumnClaimW.onStack`'s placement: `None` for a column with none.
#[inline(always)]
pub fn on_stack(c: &ColumnClaimW, layout: &LayoutW) -> Option<Placement> {
    layout.placements.get(c.column).and_then(|p| p.get())
}
