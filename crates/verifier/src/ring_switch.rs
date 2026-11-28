//! Ring switching: the 64 slice claims a reduction leaves become one claim on the committed columns (Annex annex:rs).

use crate::VerifierError;
use crate::field::{E, GEN, ONE, ZERO};
use crate::layout::K_BITS;
use crate::multilinear::{Placement, poly_eval};
use crate::transcript::Transcript;
use crate::whir::BATCH_GRINDING_BITS;

/// Phi's challenges come in two rows of this many: `f_p` then `g_b`.
const RING_MAP_WIDTH: usize = 8;

/// `value^(2^(8 p))`.
fn frobenius_8(value: E, p: usize) -> E {
    (0..RING_MAP_WIDTH * p).fold(value, |v, _| v.square())
}

/// The inner stage `Psi(v) = sum_b g_b v^(2^b)`; then `Phi(v) = sum_p f_p Psi(v)^(2^(8p))`.
fn ring_psi(value: E, g: &[E]) -> E {
    let mut psi = ZERO;
    let mut power = value;
    for &g_b in g {
        psi += g_b * power;
        power = power.square();
    }
    psi
}

/// `T = sum_i x^i Phi(s_i) = sum_p f_p (sum_i z_p^i Psi(s_i))^(2^(8p))`, with `z_p = x^(2^(64 - 8p))` in K, so each
/// slice takes `Psi` alone.
fn ring_target(s: &[E], f: &[E], g: &[E]) -> E {
    let images: Vec<E> = s.iter().map(|&value| ring_psi(value, g)).collect();
    let mut target = ZERO;
    let mut z = GEN;
    for p in (0..RING_MAP_WIDTH).rev() {
        z = frobenius_8(z, 1);
        target += f[p] * frobenius_8(poly_eval(&images, z), p);
    }
    target
}

/// The same map as a Frobenius sum, `Phi(v) = sum_k c_k v^(2^k)` for k < 64: `c_(8p+b) = f_p g_b^(2^(8p))`.
fn ring_coefficients(f: &[E], g: &[E]) -> Vec<E> {
    let mut coefficients = Vec::with_capacity(K_BITS);
    let mut powers = g.to_vec();
    for &f_p in f {
        coefficients.extend(powers.iter().map(|&g_b| f_p * g_b));
        powers.iter_mut().for_each(|g_b| *g_b = frobenius_8(*g_b, 1));
    }
    coefficients
}

/// The Frobenius powers `x^(2^k)` for `k < 64`.
fn frobenius(mut x: E) -> Vec<E> {
    (0..K_BITS)
        .map(|_| {
            let power = x;
            x = x.square();
            power
        })
        .collect()
}

/// The pieces at one point: the point's Frobenius powers, coordinate by coordinate, and each piece's placement and
/// the Frobenius powers of its scale. The pointer columns of one table share their table's row point.
struct PointGroup {
    point: Vec<Vec<E>>,
    pieces: Vec<(Option<Placement>, Vec<E>)>,
}

/// The weight `W(u) = sum_p Phi(scale_p eq(r_p, u))`, extended and evaluated by the opening at `x`:
/// `sum_k c_k prod_n (1 + r_n^(2^k) + x_n) sum_p above_p(x) scale_p^(2^k)`, the product shared by the pieces at
/// one point.
fn ring_weight(groups: &[PointGroup], x: &[E], coefficients: &[E]) -> E {
    E::sum(groups.iter().map(|group| {
        let n = group.point.len();
        let aboves: Vec<E> = group
            .pieces
            .iter()
            .map(|(placement, _)| placement.map_or(ONE, |placement| placement.eq_above(x)))
            .collect();
        E::sum(coefficients.iter().enumerate().map(|(k, &c)| {
            let product = group
                .point
                .iter()
                .zip(&x[..n])
                .fold(c, |acc, (powers, &x)| acc * (ONE + powers[k] + x));
            let scales = E::sum(
                group
                    .pieces
                    .iter()
                    .zip(&aboves)
                    .map(|((_, powers), &above)| above * powers[k]),
            );
            product * scales
        }))
    }))
}

/// One piece of a ring-switched claim: the slices of the column at `placement` (the whole stack for `None`) at
/// `point`, scaled by `scale`. A column is one piece.
pub struct RingPiece {
    pub placement: Option<Placement>,
    pub point: Vec<E>,
    pub scale: E,
}

/// The 64 claims `s[i] = sum_p scale_p z_p(i, point_p)` on the bit slices of the pieces' columns.
pub struct RingClaim {
    pub pieces: Vec<RingPiece>,
    pub slices: Vec<E>,
}

/// A claim on the stack: its weight at a stack point, and its value.
pub type RingStackClaim = (Box<dyn Fn(&[E]) -> E>, E);

/// The claims' 64 slices become one dense claim `sum_u W(u) column(u) = target`.
///
/// Draw Phi once they are all fixed, then, for several claims, `rho`: claim `j` joins as `rho^j` times itself, its
/// slices and its pieces' scales. Phi is not `E`-linear, so `rho` scales inside it. Take the target `T = sum_i x^i
/// Phi(s_i)` against the MLE-friendly weight `W = sum_p Phi(scale_p eq(point_p, .))` on each piece's placement.
///
/// One grind covers the map's challenges, `rho` and the stacked opening's batching challenge, one packed draw, which
/// returns the batching challenge too.
pub fn ring_switch(claims: Vec<RingClaim>, transcript: &mut Transcript) -> Result<(RingStackClaim, E), VerifierError> {
    transcript.grind_check(BATCH_GRINDING_BITS)?;
    let merging = claims.len() > 1;
    let challenges = transcript.samples_packed(2 * RING_MAP_WIDTH + usize::from(merging) + 1);
    let (f, rest) = challenges.split_at(RING_MAP_WIDTH);
    let (g, rest) = rest.split_at(RING_MAP_WIDTH);
    let (rho, batching) = if merging { (rest[0], rest[1]) } else { (ONE, rest[0]) };
    let mut slices = vec![ZERO; K_BITS];
    let mut groups: Vec<PointGroup> = Vec::new();
    let mut points: Vec<Vec<E>> = Vec::new();
    let mut rho_j = ONE;
    for claim in claims {
        for (sum, &s) in slices.iter_mut().zip(&claim.slices) {
            *sum += rho_j * s;
        }
        for piece in claim.pieces {
            let scale = frobenius(rho_j * piece.scale);
            match points.iter().position(|p| *p == piece.point) {
                Some(g) => groups[g].pieces.push((piece.placement, scale)),
                None => {
                    groups.push(PointGroup {
                        point: piece.point.iter().map(|&r| frobenius(r)).collect(),
                        pieces: vec![(piece.placement, scale)],
                    });
                    points.push(piece.point);
                }
            }
        }
        rho_j *= rho;
    }
    let target = ring_target(&slices, f, g);
    let coefficients = ring_coefficients(f, g);
    let weight = move |x: &[E]| ring_weight(&groups, x, &coefficients);
    Ok(((Box::new(weight), target), batching))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The target and the coefficients against `sum_i x^i sum_k c_k s_i^(2^k)`, with `c_k` from the two stages
    /// written out.
    #[test]
    fn target_and_coefficients_expand_the_map() {
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            E::new(state, state.rotate_left(29))
        };
        let challenges: Vec<E> = (0..2 * RING_MAP_WIDTH).map(|_| next()).collect();
        let (f, g) = challenges.split_at(RING_MAP_WIDTH);
        let coefficients = ring_coefficients(f, g);
        let phi = |value: E| -> E {
            let psi = ring_psi(value, g);
            E::sum((0..RING_MAP_WIDTH).map(|p| f[p] * frobenius_8(psi, p)))
        };
        let s: Vec<E> = (0..K_BITS).map(|_| next()).collect();
        let mut expanded = Vec::new();
        for &value in &s {
            let mut power = value;
            let mut image = ZERO;
            for &c in &coefficients {
                image += c * power;
                power = power.square();
            }
            assert_eq!(phi(value), image);
            expanded.push(image);
        }
        assert_eq!(ring_target(&s, f, g), poly_eval(&expanded, GEN));
    }
}
