//! Phase 3a: the bus's GKR walk (`NativeVm/Model/Gkr.lean`).

use crate::buf::Buf;
use crate::field::{EW, ZERO, multilinear_eval, poly_eval, prod_e};
use crate::transcript::{TState, grinding_bits, require};

/// `nTrees`.
pub const N_TREES: usize = 3;
/// `busPointCap`: the GKR point, the push side's depth, below `64`.
pub const BUS_POINT_CAP: usize = 63;

/// `GkrStateW`: the three trees' values, at `point`.
#[repr(C)]
pub struct GkrStateW {
    pub values: [EW; N_TREES],
    pub point: Buf<EW, BUS_POINT_CAP>,
}

/// `gkrStep step last state`.
#[inline(never)]
fn gkr_step(t: &mut TState, step: usize, last: bool, s: &mut GkrStateW) -> Option<()> {
    t.grind(grinding_bits(N_TREES as u64 - 1))?;
    let combiner = t.sample_challenge();
    let claim = poly_eval(&s.values, combiner);
    let mut x = [ZERO; BUS_POINT_CAP];
    let point = s.point.as_slice();
    let x = x.get_mut(..point.len())?;
    let claim = t.sumcheck(claim, (1 << step) + 1, |i| point.get(i).copied(), x)?;
    let mut children = [[ZERO; 4]; N_TREES];
    for child in children.iter_mut() {
        t.read_scalars(child.get_mut(..1 << step)?)?;
    }
    let mut products = [ZERO; N_TREES];
    for (p, child) in products.iter_mut().zip(&children) {
        *p = prod_e(child.get(..1 << step)?);
    }
    require(claim == poly_eval(&products, combiner))?;
    t.grind(grinding_bits(if last { 2 * step as u64 } else { step as u64 }))?;
    let mut y = [ZERO; 2];
    let y = y.get_mut(..step)?;
    t.sample_challenges(y);
    for (v, child) in s.values.iter_mut().zip(&children) {
        *v = multilinear_eval(child.get(..1 << step)?, y);
    }
    // `y ++ x`.
    let (n, m) = (step, x.len());
    let slots = s.point.resize(n + m)?;
    let (head, tail) = slots.split_at_mut_checked(n)?;
    for (slot, &v) in head.iter_mut().zip(y.iter()) {
        *slot = v;
    }
    for (slot, &v) in tail.iter_mut().zip(x.iter()) {
        *slot = v;
    }
    Some(())
}

/// `gkrLayers`: one level when the remaining depth is odd, two otherwise.
#[inline(never)]
fn gkr_layers(t: &mut TState, depth: usize, s: &mut GkrStateW) -> Option<()> {
    let mut n = depth;
    while n > 0 {
        if n == 1 {
            gkr_step(t, 1, true, s)?;
            n = 0;
        } else {
            let m = n - 2;
            if m % 2 == 1 {
                gkr_step(t, 1, false, s)?;
                n = m + 1;
            } else {
                gkr_step(t, 2, m == 0, s)?;
                n = m;
            }
        }
    }
    Some(())
}

/// **`verifyGkrGrandProducts depth`**: the count root; the GKR point and the trees' values in `s`.
#[inline(never)]
pub fn verify_gkr_grand_products(t: &mut TState, depth: usize, s: &mut GkrStateW) -> Option<EW> {
    let shared = t.read_scalar()?;
    let count = t.read_scalar()?;
    s.values = [shared, shared, count];
    s.point.clear();
    gkr_layers(t, depth, s)?;
    Some(count)
}
