//! Field elements as binary polynomials at the layer's point `s`. A weight written so times a
//! product of two embeddings is a carry-less product, and the sum of many such is evaluated at `s`
//! once.

use primitives::field::{F128, powers};

use crate::kernels::byte_sums;

/// Coefficients a polynomial [`AtS::eval`] reads may have: a weight's 128 and a product's 47.
const COEFFS: usize = 192;

pub(crate) struct AtS {
    /// Per bit of an element, a polynomial of degree below 128 whose value at `s` is that bit.
    unit: Vec<u128>,
    /// Per byte of a polynomial, the value at `s` of each of its 256 values.
    bytes: Vec<[F128; 256]>,
}

impl AtS {
    pub fn new(s: F128) -> Self {
        // Gauss-Jordan on the powers of `s` below 128, each tagged with its exponent: the reduced
        // rows are the unit vectors, tagged with their polynomials.
        let powers = powers(s, COEFFS);
        let mut rows: Vec<(u128, u128)> = (0..128).map(|i| (u128::from(powers[i]), 1u128 << i)).collect();
        for k in 0..128 {
            let pivot = (k..128)
                .find(|&r| rows[r].0 >> k & 1 == 1)
                .expect("the challenge lies in no proper subfield");
            rows.swap(k, pivot);
            let (value, tag) = rows[k];
            for (r, row) in rows.iter_mut().enumerate() {
                if r != k && row.0 >> k & 1 == 1 {
                    *row = (row.0 ^ value, row.1 ^ tag);
                }
            }
        }
        Self {
            unit: rows.iter().map(|row| row.1).collect(),
            bytes: powers.as_chunks::<8>().0.iter().map(byte_sums).collect(),
        }
    }

    /// The polynomial of degree below 128 whose value at `s` is `w`, its two words as an element's
    /// limbs.
    pub fn poly(&self, w: F128) -> F128 {
        let w = u128::from(w);
        F128::from((0..128).filter(|k| w >> k & 1 == 1).fold(0, |p, k| p ^ self.unit[k]))
    }

    /// `low + x^64 high` at `s`, for the two partial products of a weight's words.
    pub fn eval(&self, [low, high]: [u128; 2]) -> F128 {
        let words = [low as u64, (low >> 64) as u64 ^ high as u64, (high >> 64) as u64];
        let mut acc = F128::ZERO;
        for (w, bytes) in words.iter().zip(self.bytes.as_chunks::<8>().0) {
            for (b, table) in bytes.iter().enumerate() {
                acc += table[(w >> (8 * b)) as usize & 0xff];
            }
        }
        acc
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::field::gf2_64::mul_wide;
    use primitives::test_rng::Rng;

    #[test]
    fn polynomials_take_their_values_at_s() {
        let mut rng = Rng::new(41);
        let s = rng.ext();
        let at = AtS::new(s);
        let eval = |words: &[u64]| -> F128 {
            let powers = powers(s, 64 * words.len());
            (0..64 * words.len())
                .filter(|&i| words[i / 64] >> (i % 64) & 1 == 1)
                .map(|i| powers[i])
                .sum()
        };
        for _ in 0..20 {
            let w = rng.ext();
            let p = at.poly(w).to_limbs();
            assert_eq!(eval(&p), w);
            let product = rng.next_u64() >> 17;
            let partial = [mul_wide(product, p[0]), mul_wide(product, p[1])];
            assert_eq!(at.eval(partial), w * eval(&[product]));
        }
    }
}
