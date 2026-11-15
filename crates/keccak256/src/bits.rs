//! Keccak-f\[1600\] one bit position at a time, as `keccak_gkr` proves it.
//!
//! Position `j = z + 64 * (x + 5 * y)` is bit `z` of lane `x + 5 * y`. A round is the linear map `theta, rho, pi`,
//! then `chi`, then `iota`.

use crate::{PI, RC, RHO, ROUNDS, STATE_LANES};

/// The five positions of a row and slice, which `chi` mixes.
#[inline(always)]
pub fn row_positions(row: usize, z: usize) -> [usize; 5] {
    std::array::from_fn(|x| 64 * (x + 5 * row) + z)
}

/// Whether `iota` flips position `z` of lane 0 in round `round`, counted from 1.
#[inline]
pub fn iota_bit(round: usize, z: usize) -> bool {
    debug_assert!((1..=ROUNDS).contains(&round));
    RC[round - 1] >> z & 1 == 1
}

/// `pi(rho(theta(a)))`, over any XOR group.
pub fn linear<T: Copy + Default>(a: &[T], out: &mut [T], xor: impl Fn(T, T) -> T) {
    let mut c = [T::default(); 5 * 64];
    for x in 0..5 {
        for z in 0..64 {
            c[64 * x + z] = (1..5).fold(a[64 * x + z], |acc, y| xor(acc, a[64 * (x + 5 * y) + z]));
        }
    }
    let mut d = [T::default(); 5 * 64];
    for x in 0..5 {
        for z in 0..64 {
            d[64 * x + z] = xor(c[64 * ((x + 4) % 5) + z], c[64 * ((x + 1) % 5) + (z + 63) % 64]);
        }
    }
    for lane in 0..STATE_LANES {
        let rot = RHO[lane] as usize;
        for z in 0..64 {
            out[64 * PI[lane] + (z + rot) % 64] = xor(a[64 * lane + z], d[64 * (lane % 5) + z]);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::keccak_f;
    use verifier::E;
    use verifier::keccak::{BITS, along, linear_transpose};

    /// A linear congruential generator's next word.
    fn next(x: &mut u64) -> u64 {
        *x = x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        *x
    }

    #[test]
    fn a_round_matches_the_permutation() {
        let mut x = 3;
        let lanes: [u64; STATE_LANES] = std::array::from_fn(|_| next(&mut x));
        let mut bits: Vec<bool> = (0..BITS).map(|j| lanes[j / 64] >> (j % 64) & 1 == 1).collect();
        for round in 1..=ROUNDS {
            let mut u = vec![false; BITS];
            linear(&bits, &mut u, |a, b| a ^ b);
            for j in 0..BITS {
                bits[j] = u[j] ^ (!u[along(j, 1)] & u[along(j, 2)]) ^ (j < 64 && iota_bit(round, j));
            }
        }
        let mut expected = lanes;
        keccak_f(&mut expected);
        for j in 0..BITS {
            assert_eq!(bits[j], expected[j / 64] >> (j % 64) & 1 == 1, "position {j}");
        }
    }

    /// The verifier's `linear_transpose` is the adjoint of [`linear`].
    #[test]
    fn the_transpose_is_the_adjoint() {
        let mut x = 5;
        let a: Vec<bool> = (0..BITS).map(|_| next(&mut x) >> 63 == 1).collect();
        let w: Vec<E> = (0..BITS).map(|_| E::new(next(&mut x), next(&mut x))).collect();
        let mut u = vec![false; BITS];
        linear(&a, &mut u, |a, b| a ^ b);
        let dot = |w: &[E], a: &[bool]| E::sum(w.iter().zip(a).filter(|&(_, &a)| a).map(|(&w, _)| w));
        assert_eq!(dot(&w, &u), dot(&linear_transpose(&w), &a));
    }
}
