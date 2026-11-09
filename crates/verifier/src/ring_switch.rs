//! Ring switching: the 64 slice claims a reduction leaves become one claim on the committed column.

use crate::VerifierError;
use crate::field::{E, GEN, ONE, ZERO};
use crate::layout::K_BITS;
use crate::multilinear::poly_eval;
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

/// The weight `W(u) = Phi(eq(r, u))`, extended and evaluated by the opening at
/// `r_prime`: `sum_k c_k prod_n (1 + r_n^(2^k) + r'_n)`.
fn ring_weight(r: &[E], r_prime: &[E], coefficients: &[E]) -> E {
    assert_eq!(r.len(), r_prime.len());
    let mut total = ZERO;
    let mut frobenius = r.to_vec();
    for &c in coefficients {
        let mut product = c;
        for (value, &challenge) in frobenius.iter_mut().zip(r_prime) {
            product *= ONE + *value + challenge;
            *value = value.square();
        }
        total += product;
    }
    total
}

/// The 64 claims s\[i\] = z(i, point) become the one dense claim `sum_u W(u) qkeccak(u) = target`.
///
/// Draw Phi once they are fixed, then take the target `T = sum_i x^i Phi(s_i)` against the
/// MLE-friendly weight `W(u) = Phi(eq(point, u))`. Returns the target and W as a closure.
///
/// One grind covers the map's challenges and the stacked opening's batching challenge, drawn next.
pub fn ring_switch(
    point: Vec<E>,
    s: &[E],
    transcript: &mut Transcript,
) -> Result<(E, impl Fn(&[E]) -> E + use<>), VerifierError> {
    transcript.grind_check(BATCH_GRINDING_BITS)?;
    let challenges = transcript.samples(2 * RING_MAP_WIDTH);
    let (f, g) = challenges.split_at(RING_MAP_WIDTH);
    let coefficients = ring_coefficients(f, g);
    let target = ring_target(s, f, g);
    Ok((target, move |r_prime: &[E]| ring_weight(&point, r_prime, &coefficients)))
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
