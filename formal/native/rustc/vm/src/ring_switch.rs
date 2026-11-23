//! Phase 7a: ring switching (`NativeVm/Model/RingSwitch.lean`).

use crate::field::{EW, GEN, ZERO, poly_eval};
use crate::transcript::TState;
use crate::whir::BATCH_GRINDING_BITS;

/// `ringMapWidth`.
const RING_MAP_WIDTH: usize = 8;
/// `ringCoeffCount`.
pub const RING_COEFF_COUNT: usize = RING_MAP_WIDTH * RING_MAP_WIDTH;

/// `RingAt`: the target and the coefficients (the point is `KeccakOutW`'s).
#[repr(C)]
pub struct RingW {
    pub target: EW,
    pub coefficients: [EW; RING_COEFF_COUNT],
}

/// `frobenius8 value p`: `value^(2^(8p))`.
#[inline(always)]
fn frobenius8(value: EW, p: usize) -> EW {
    EW::sq_iter(RING_MAP_WIDTH * p, value)
}

/// `ringPsi value g`: `Σ_b g_b v^(2^b)`.
#[inline(never)]
fn ring_psi(value: EW, g: &[EW]) -> EW {
    let (mut acc, mut power) = (ZERO, value);
    for &g_b in g {
        acc = acc + g_b * power;
        power = power * power;
    }
    acc
}

/// `ringTarget s f g`: `Σ_p f_p (Σ_i z_p^i Ψ(s_i))^(2^(8p))`, `p` from `7` down.
#[inline(never)]
fn ring_target(s: &[EW; 64], f: &[EW], g: &[EW]) -> EW {
    let images: [EW; 64] = core::array::from_fn(|i| ring_psi(s[i], g));
    let (mut acc, mut z) = (ZERO, GEN);
    for p in (0..RING_MAP_WIDTH).rev() {
        z = frobenius8(z, 1);
        acc = acc + f.get(p).copied().unwrap_or(ZERO) * frobenius8(poly_eval(&images, z), p);
    }
    acc
}

/// `ringCoefficients f g`: `c_(8p+b) = f_p · g_b^(2^(8p))`.
#[inline(never)]
fn ring_coefficients(f: &[EW], g: &[EW; RING_MAP_WIDTH], out: &mut [EW; RING_COEFF_COUNT]) {
    let mut g = *g;
    for (chunk, &f_p) in out.chunks_exact_mut(RING_MAP_WIDTH).zip(f) {
        for (c, &g_b) in chunk.iter_mut().zip(&g) {
            *c = f_p * g_b;
        }
        for g_b in g.iter_mut() {
            *g_b = frobenius8(*g_b, 1);
        }
    }
}

/// **Phase 7a** (`ringSwitch`): the target and the coefficients into `out`; the point is the
/// caller's.
#[inline(never)]
pub fn ring_switch(t: &mut TState, s: &[EW; 64], out: &mut RingW) -> Option<()> {
    t.grind(BATCH_GRINDING_BITS)?;
    let mut challenges = [ZERO; 2 * RING_MAP_WIDTH];
    t.sample_challenges(&mut challenges);
    let (f, g) = challenges.split_at(RING_MAP_WIDTH);
    let g: [EW; RING_MAP_WIDTH] = core::array::from_fn(|i| g.get(i).copied().unwrap_or(ZERO));
    ring_coefficients(f, &g, &mut out.coefficients);
    out.target = ring_target(s, f, &g);
    Some(())
}
