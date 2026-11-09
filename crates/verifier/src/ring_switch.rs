//! Ring switching: the 64 slice claims a reduction leaves become one claim on the committed column.

use crate::field::{E, GEN, ONE, ZERO};
use crate::layout::K_BITS;
use crate::multilinear::poly_eval;
use crate::transcript::Transcript;

/// Phi's challenges come in two rows of this many: `f_a` then `g_b`.
const RING_MAP_WIDTH: usize = 8;

/// The drawn map in two stages: `Psi(v) = sum_a f_a v^(2^(8a))`, then `Phi(v) = sum_b g_b Psi(v)^(2^b)`.
fn ring_map(value: E, f: &[E], g: &[E]) -> E {
    let mut psi = ZERO;
    let mut power = value;
    for &f_a in f {
        psi += f_a * power;
        power = (0..RING_MAP_WIDTH).fold(power, |v, _| v.square());
    }
    let mut phi = ZERO;
    for &g_b in g {
        phi += g_b * psi;
        psi = psi.square();
    }
    phi
}

/// The same map as a Frobenius sum, `Phi(v) = sum_k c_k v^(2^k)` for k < 64: `c_(8a+b) = g_b f_a^(2^b)`.
fn ring_coefficients(f: &[E], g: &[E]) -> Vec<E> {
    let mut coefficients = Vec::with_capacity(K_BITS);
    for &f_a in f {
        let mut power = f_a;
        for &g_b in g {
            coefficients.push(g_b * power);
            power = power.square();
        }
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
pub fn ring_switch(point: Vec<E>, s: &[E], transcript: &mut Transcript) -> (E, impl Fn(&[E]) -> E + use<>) {
    let challenges = transcript.samples(2 * RING_MAP_WIDTH);
    let (f, g) = challenges.split_at(RING_MAP_WIDTH);
    let coefficients = ring_coefficients(f, g);
    let images: Vec<E> = s.iter().map(|&value| ring_map(value, f, g)).collect();
    let target = poly_eval(&images, GEN);
    (target, move |r_prime: &[E]| ring_weight(&point, r_prime, &coefficients))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn coefficients_expand_the_map() {
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
        let value = next();
        let mut power = value;
        let mut expanded = ZERO;
        for &c in &coefficients {
            expanded += c * power;
            power = power.square();
        }
        assert_eq!(ring_map(value, f, g), expanded);
    }
}
