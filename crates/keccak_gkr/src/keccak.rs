//! Keccak-f\[1600\] as the protocol sees it: one bit position at a time.
//!
//! Position `j = z + 64 * (x + 5 * y)` is bit `z` of lane `x + 5 * y`. A round is the linear map
//! `theta, rho, pi`, then `chi`, then `iota`.

use primitives::field::F192;
pub use primitives::hash::STATE_LANES as LANES;
use primitives::hash::{PI, RC, RHO, ROUNDS};

pub const BITS: usize = 1600;
/// Variables of the cube the positions embed in, low ones first: `z`, then the lane.
pub const LOCAL_VARS: usize = 11;
/// Variables of the lane alone.
pub const LANE_VARS: usize = 5;

/// The position `k` columns along from `j`, in the same row and slice.
#[inline(always)]
pub const fn along(j: usize, k: usize) -> usize {
    let (lane, z) = (j / 64, j % 64);
    64 * ((lane % 5 + k) % 5 + 5 * (lane / 5)) + z
}

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
    let mut c = [T::default(); 320];
    for x in 0..5 {
        for z in 0..64 {
            c[64 * x + z] = (1..5).fold(a[64 * x + z], |acc, y| xor(acc, a[64 * (x + 5 * y) + z]));
        }
    }
    let mut d = [T::default(); 320];
    for x in 0..5 {
        for z in 0..64 {
            d[64 * x + z] = xor(c[64 * ((x + 4) % 5) + z], c[64 * ((x + 1) % 5) + (z + 63) % 64]);
        }
    }
    for lane in 0..LANES {
        let rot = RHO[lane] as usize;
        for z in 0..64 {
            out[64 * PI[lane] + (z + rot) % 64] = xor(a[64 * lane + z], d[64 * (lane % 5) + z]);
        }
    }
}

/// The transpose of [`linear`] on weight vectors: `<w, linear(a)> = <linear_transpose(w), a>`.
pub fn linear_transpose(w: &[F192]) -> Vec<F192> {
    assert_eq!(w.len(), BITS);
    // The weight each position of `theta`'s output carries.
    let mut g = vec![F192::ZERO; BITS];
    for lane in 0..LANES {
        let rot = RHO[lane] as usize;
        for z in 0..64 {
            g[64 * lane + z] = w[64 * PI[lane] + (z + rot) % 64];
        }
    }
    let mut columns = vec![F192::ZERO; 320];
    for lane in 0..LANES {
        for z in 0..64 {
            columns[64 * (lane % 5) + z] += g[64 * lane + z];
        }
    }
    let mut out = g;
    for lane in 0..LANES {
        let x = lane % 5;
        for z in 0..64 {
            out[64 * lane + z] += columns[64 * ((x + 1) % 5) + z] + columns[64 * ((x + 4) % 5) + (z + 1) % 64];
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    #[test]
    fn a_round_matches_the_permutation() {
        let mut rng = Rng::new(3);
        let lanes: [u64; LANES] = std::array::from_fn(|_| rng.next_u64());
        let mut bits: Vec<bool> = (0..BITS).map(|j| lanes[j / 64] >> (j % 64) & 1 == 1).collect();
        for round in 1..=ROUNDS {
            let mut u = vec![false; BITS];
            linear(&bits, &mut u, |a, b| a ^ b);
            for j in 0..BITS {
                bits[j] = u[j] ^ (!u[along(j, 1)] & u[along(j, 2)]) ^ (j < 64 && iota_bit(round, j));
            }
        }
        let mut expected = lanes;
        primitives::hash::keccak_f(&mut expected);
        for j in 0..BITS {
            assert_eq!(bits[j], expected[j / 64] >> (j % 64) & 1 == 1, "position {j}");
        }
    }

    #[test]
    fn the_transpose_is_the_adjoint() {
        let mut rng = Rng::new(5);
        let a: Vec<bool> = (0..BITS).map(|_| rng.next_u64() & 1 == 1).collect();
        let w = rng.ext_vec(BITS);
        let mut u = vec![false; BITS];
        linear(&a, &mut u, |a, b| a ^ b);
        let dot = |w: &[F192], a: &[bool]| {
            w.iter()
                .zip(a)
                .fold(F192::ZERO, |s, (&w, &a)| if a { s + w } else { s })
        };
        assert_eq!(dot(&w, &u), dot(&linear_transpose(&w), &a));
    }
}
