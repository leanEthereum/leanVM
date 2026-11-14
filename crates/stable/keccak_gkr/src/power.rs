//! The field in the power basis of a challenge `s`: an element is its 128 coefficients on
//! `1, s, ..., s^127`, and a product is a carry-less one reduced modulo the minimal polynomial
//! of `s`.
//!
//! The rounds after the bit-level ones stay in this basis. Their tables come out of carry-less
//! sums already in it, and moving every entry to the standard basis would cost more than
//! reducing by a dense modulus does.
//!
//! A table row is laid out by word: word `k` of entry `j` at `k * width + j`.

use primitives::field::F128;

use crate::basis::{PolyEval, PowerBasis, add_mul};

pub type Element = [u64; 2];

pub struct PowerField {
    pub basis: PowerBasis,
    /// `s^128`, the modulus without its leading term.
    modulus: Element,
    /// `floor(x^256 / modulus)` without its leading term, for Barrett's reduction.
    barrett: Element,
    eval: PolyEval,
}

/// The carry-less product of two elements, four words.
#[inline(always)]
fn mul_wide2(a: &Element, b: &Element) -> [u64; 4] {
    let mut out = [0u64; 4];
    add_mul(&mut out, a, b);
    out
}

impl PowerField {
    /// `None` when `s` lies in a proper subfield.
    pub fn new(s: F128) -> Option<Self> {
        let basis = PowerBasis::new(s)?;
        let mut power = F128::ONE;
        for _ in 0..128 {
            power *= s;
        }
        let modulus = basis.to_poly(power);
        // Long division of `x^256` by `x^128 + modulus`.
        let mut dividend = [0u64; 5];
        dividend[4] = 1;
        let mut barrett = [0u64; 2];
        for bit in (128..=256).rev() {
            if dividend[bit / 64] >> (bit % 64) & 1 == 1 {
                let shift = bit - 128;
                if shift < 128 {
                    barrett[shift / 64] |= 1 << (shift % 64);
                }
                dividend[bit / 64] ^= 1 << (bit % 64);
                for b in (0..128).filter(|b| modulus[b / 64] >> (b % 64) & 1 == 1) {
                    dividend[(b + shift) / 64] ^= 1 << ((b + shift) % 64);
                }
            }
        }
        Some(Self {
            basis,
            modulus,
            barrett,
            eval: PolyEval::new(s, 16),
        })
    }

    pub fn to_poly(&self, a: F128) -> Element {
        self.basis.to_poly(a)
    }

    pub fn to_field(&self, a: &Element) -> F128 {
        self.eval.eval(a)
    }

    /// A polynomial of at most 256 coefficients, modulo the minimal polynomial.
    #[inline(always)]
    pub fn reduce(&self, p: &[u64; 4]) -> Element {
        let high: Element = [p[2], p[3]];
        // The quotient: `high`, plus the top half of `high * barrett`.
        let t = mul_wide2(&high, &self.barrett);
        let q: Element = [high[0] ^ t[2], high[1] ^ t[3]];
        let r = mul_wide2(&q, &self.modulus);
        [p[0] ^ r[0], p[1] ^ r[1]]
    }

    #[inline(always)]
    pub fn mul(&self, a: &Element, b: &Element) -> Element {
        self.reduce(&mul_wide2(a, b))
    }

    /// `sum of a[j] * b[j]` and `sum of (a[j] + a'[j]) * (b[j] + b'[j])` over two pairs of rows,
    /// unreduced.
    pub fn dot_pair(&self, a: [&[u64]; 2], b: [&[u64]; 2], width: usize) -> ([u64; 4], [u64; 4]) {
        let (mut zero, mut infinity) = ([0u64; 4], [0u64; 4]);
        for j in 0..width {
            let (a0, a1, b0, b1) = (
                get(a[0], width, j),
                get(a[1], width, j),
                get(b[0], width, j),
                get(b[1], width, j),
            );
            let da = [a0[0] ^ a1[0], a0[1] ^ a1[1]];
            let db = [b0[0] ^ b1[0], b0[1] ^ b1[1]];
            add_mul(&mut zero, &a0, &b0);
            add_mul(&mut infinity, &da, &db);
        }
        (zero, infinity)
    }

    /// `dst[j] = lo[j] + challenge * (lo[j] + hi[j])`.
    pub fn fold_row(&self, dst: &mut [u64], lo: &[u64], hi: &[u64], challenge: &Element, width: usize) {
        for j in 0..width {
            let (l, h) = (get(lo, width, j), get(hi, width, j));
            let folded = self.mul(challenge, &[l[0] ^ h[0], l[1] ^ h[1]]);
            set(dst, width, j, &[l[0] ^ folded[0], l[1] ^ folded[1]]);
        }
    }

    /// `dst[j] = wide[j]` reduced, for a row of three-word polynomials laid out by word.
    pub fn reduce_row(&self, dst: &mut [u64], wide: &[u64], width: usize) {
        for j in 0..width {
            let p = [wide[j], wide[width + j], wide[2 * width + j], 0];
            set(dst, width, j, &self.reduce(&p));
        }
    }

    /// `dst[j] = a[j] * b[j] + c[j]`.
    pub fn mul_row(&self, dst: &mut [u64], a: &[u64], b: &[u64], c: &[u64], width: usize) {
        for j in 0..width {
            let (p, c) = (self.mul(&get(a, width, j), &get(b, width, j)), get(c, width, j));
            set(dst, width, j, &[p[0] ^ c[0], p[1] ^ c[1]]);
        }
    }
}

/// Entry `j` of a row.
#[inline(always)]
pub fn get(row: &[u64], width: usize, j: usize) -> Element {
    [row[j], row[width + j]]
}

#[inline(always)]
pub fn set(row: &mut [u64], width: usize, j: usize, value: &Element) {
    for k in 0..2 {
        row[k * width + j] = value[k];
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    #[test]
    fn arithmetic_matches_the_standard_basis() {
        let mut rng = Rng::new(41);
        let s = rng.ext();
        let field = PowerField::new(s).unwrap();
        let width = 16;
        let elements = |rng: &mut Rng| -> (Vec<F128>, Vec<u64>) {
            let values = rng.ext_vec(width);
            let mut row = vec![0u64; 2 * width];
            for (j, &v) in values.iter().enumerate() {
                set(&mut row, width, j, &field.to_poly(v));
            }
            (values, row)
        };
        let ((a0, ra0), (a1, ra1), (b0, rb0), (b1, rb1)) = (
            elements(&mut rng),
            elements(&mut rng),
            elements(&mut rng),
            elements(&mut rng),
        );
        assert_eq!(
            field.to_field(&field.mul(&get(&ra0, width, 3), &get(&rb0, width, 5))),
            a0[3] * b0[5]
        );

        let (zero, infinity) = field.dot_pair([&ra0, &ra1], [&rb0, &rb1], width);
        let expected = (0..width).map(|j| a0[j] * b0[j]).sum();
        assert_eq!(field.to_field(&field.reduce(&zero)), expected);
        let expected = (0..width).map(|j| (a0[j] + a1[j]) * (b0[j] + b1[j])).sum();
        assert_eq!(field.to_field(&field.reduce(&infinity)), expected);

        let challenge = rng.ext();
        let mut row = vec![0u64; 2 * width];
        field.fold_row(&mut row, &ra0, &ra1, &field.to_poly(challenge), width);
        for j in 0..width {
            assert_eq!(
                field.to_field(&get(&row, width, j)),
                primitives::multilinear::interp(a0[j], a1[j], challenge)
            );
        }
        let wide: Vec<u64> = (0..3 * width).map(|_| rng.next_u64()).collect();
        field.reduce_row(&mut row, &wide, width);
        let eval = PolyEval::new(s, 24);
        for j in 0..width {
            let p = [wide[j], wide[width + j], wide[2 * width + j]];
            assert_eq!(field.to_field(&get(&row, width, j)), eval.eval(&p));
        }
        field.mul_row(&mut row, &ra0, &rb0, &rb1, width);
        for j in 0..width {
            assert_eq!(field.to_field(&get(&row, width, j)), a0[j] * b0[j] + b1[j]);
        }
    }
}
