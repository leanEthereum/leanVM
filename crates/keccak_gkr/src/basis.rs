//! A field element as a binary polynomial in a challenge `s`, and back.
//!
//! In the power basis of `s`, a sum of bits weighted by powers of `s` is the bits themselves, and
//! multiplying it by a weight is a carry-less product. So the prover moves its weights into that
//! basis once, accumulates unreduced polynomials in `s`, and evaluates each total at `s` at the end.

use primitives::field::gf2_64::mul_wide;
use primitives::field::{F192, powers};

fn xor3(a: &mut [u64; 3], b: &[u64; 3]) {
    for (x, y) in a.iter_mut().zip(b) {
        *x ^= y;
    }
}

/// The map from a field element to its coefficients on `1, s, ..., s^191`.
pub struct PowerBasis {
    tables: Vec<[[u64; 3]; 256]>,
}

impl PowerBasis {
    /// `None` when `s` lies in a proper subfield, where its powers do not span the field.
    pub fn new(s: F192) -> Option<Self> {
        // Column `b` holds a combination of powers, as its bits beside its coefficients. Column
        // operations keep that so, and bring the bits to the identity: column `r` then holds the
        // coefficients of the element whose only bit is `r`.
        let mut columns = vec![([0u64; 3], [0u64; 3]); 192];
        let mut power = F192::ONE;
        for (b, column) in columns.iter_mut().enumerate() {
            *column = (power.to_limbs(), [0; 3]);
            column.1[b / 64] = 1 << (b % 64);
            power *= s;
        }
        for r in 0..192 {
            let pivot = (r..192).find(|&b| columns[b].0[r / 64] >> (r % 64) & 1 == 1)?;
            columns.swap(r, pivot);
            let (pa, pi) = columns[r];
            // Masked rather than branched on: whether a column has the bit is a coin flip.
            for (b, column) in columns.iter_mut().enumerate() {
                let mask = 0u64.wrapping_sub(column.0[r / 64] >> (r % 64) & u64::from(b != r));
                for k in 0..3 {
                    column.0[k] ^= pa[k] & mask;
                    column.1[k] ^= pi[k] & mask;
                }
            }
        }
        let tables = (0..24)
            .map(|k| {
                let mut t = [[0u64; 3]; 256];
                for byte in 1..256usize {
                    let low = byte.trailing_zeros() as usize;
                    t[byte] = t[byte & (byte - 1)];
                    xor3(&mut t[byte], &columns[8 * k + low].1);
                }
                t
            })
            .collect();
        Some(Self { tables })
    }

    pub fn to_poly(&self, a: F192) -> [u64; 3] {
        let a = a.to_limbs();
        // Its length hidden, the lookups keep bounds checks, which stop the compiler turning them
        // into AVX-512 gathers that lose to scalar loads.
        let flat: &[[u64; 3]] = std::hint::black_box(self.tables.as_flattened());
        let mut p = [0u64; 3];
        for k in 0..24 {
            xor3(&mut p, &flat[256 * k + ((a[k / 8] >> (8 * (k % 8))) as usize & 0xff)]);
        }
        p
    }
}

/// The sum of every subset of eight weights, indexed by the byte whose bits pick it.
pub fn byte_sums(weights: &[F192; 8]) -> [F192; 256] {
    let mut t = [F192::ZERO; 256];
    for (bit, &w) in weights.iter().enumerate() {
        for byte in 1usize << bit..2 << bit {
            t[byte] = t[byte - (1 << bit)] + w;
        }
    }
    t
}

/// Evaluation at `s` of binary polynomials of at most `8 * n_bytes` coefficients.
pub struct PolyEval {
    tables: Vec<[F192; 256]>,
}

impl PolyEval {
    pub fn new(s: F192, n_bytes: usize) -> Self {
        Self {
            tables: powers(s, 8 * n_bytes)
                .as_chunks::<8>()
                .0
                .iter()
                .map(byte_sums)
                .collect(),
        }
    }

    #[inline]
    pub fn eval(&self, words: &[u64]) -> F192 {
        // Hidden, as in `PowerBasis::to_poly`, so the lookups are not gathers.
        let flat: &[F192] = std::hint::black_box(self.tables.as_flattened());
        let mut acc = F192::ZERO;
        for k in 0..self.tables.len() {
            acc += flat[256 * k + ((words[k / 8] >> (8 * (k % 8))) as usize & 0xff)];
        }
        acc
    }
}

/// The polynomial whose word `i` starts `acc[i]`.
#[inline(always)]
pub fn carry<const N: usize, const M: usize>(acc: &[u128; N]) -> [u64; M] {
    let mut out = [0u64; M];
    for (i, &x) in acc.iter().enumerate() {
        out[i] ^= x as u64;
        out[i + 1] ^= (x >> 64) as u64;
    }
    out
}

/// `acc += a * b`, on binary polynomials.
#[inline(always)]
pub fn add_mul<const A: usize, const B: usize, const N: usize>(acc: &mut [u64; N], a: &[u64; A], b: &[u64; B]) {
    for (i, &a) in a.iter().enumerate() {
        for (k, &b) in b.iter().enumerate() {
            let p = mul_wide(a, b);
            acc[i + k] ^= p as u64;
            acc[i + k + 1] ^= (p >> 64) as u64;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    #[test]
    fn power_basis_round_trips_and_products_are_carryless() {
        let mut rng = Rng::new(11);
        let s = rng.ext();
        let basis = PowerBasis::new(s).expect("a generic element");
        let eval = PolyEval::new(s, 40);
        for _ in 0..50 {
            let (a, b) = (rng.ext(), rng.next_u64());
            let pa = basis.to_poly(a);
            assert_eq!(eval.eval(&[pa[0], pa[1], pa[2], 0, 0]), a);
            let acc: [u128; 3] = std::array::from_fn(|k| mul_wide(pa[k], b));
            let product: [u64; 4] = carry(&acc);
            let pb = eval.eval(&[b, 0, 0, 0, 0]);
            assert_eq!(eval.eval(&[product[0], product[1], product[2], product[3], 0]), a * pb);
        }
        assert!(PowerBasis::new(F192::ONE).is_none());
    }
}
