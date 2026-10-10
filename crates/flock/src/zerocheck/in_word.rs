//! Zerocheck rounds over the six variables inside a packed word, as ordinary multilinear rounds.
//!
//! Round `i` has `rho_0..rho_{i-1}` bound. A word splits into chunks of `2^i` bits, a pair of them per value `u` of the later in-word variables:
//!
//! ```text
//!     bit index in the word = j + 2^i * (X + 2 u),      j < 2^i,  u < 2^(5 - i)
//!     f(rho, X, u)          = sum_j eq(rho, j) * bit
//! ```
//!
//! A chunk folds through byte tables of subset sums, as [`super::bit_fold`] does for whole rows.
//! The round polynomial is the one the word rounds send, with the eq weights of every later variable:
//!
//! ```text
//!     G(X) = sum_w eq(r_rest, w) sum_u eq(r_in, u) * (a(rho, X, u) b(rho, X, u) + c(rho, X, u))
//! ```

use primitives::field::{F192, F192Unreduced};

use crate::zerocheck::univariate_skip::build_eq;

/// Eq variables in the per-task half of the split table over the words.
const EQ_LO_VARS: usize = 10;

const ODD: u64 = 0xAAAA_AAAA_AAAA_AAAA;

type ByteTable = [F192; 256];

/// The subset sums of eight weights: entry `v` sums the weights of the set bits of `v`.
fn subset_sums(weights: &[F192]) -> ByteTable {
    let mut sums = [F192::ZERO; 256];
    for v in 1..256usize {
        let low = v.trailing_zeros() as usize;
        sums[v] = sums[v & (v - 1)] + weights.get(low).copied().unwrap_or(F192::ZERO);
    }
    sums
}

/// One table per byte of a chunk whose bits carry `weights`.
fn byte_tables(weights: &[F192]) -> Vec<ByteTable> {
    weights.chunks(8).map(subset_sums).collect()
}

#[inline(always)]
fn fold(tables: &[ByteTable], chunk: u64) -> F192 {
    tables
        .iter()
        .enumerate()
        .fold(F192::ZERO, |acc, (k, t)| acc + t[(chunk >> (8 * k)) as usize & 0xff])
}

/// Sum `per_word`'s two values over the words, each weighted by `eq(r_rest, word)`.
fn sum_words(n_words: usize, r_rest: &[F192], per_word: impl Fn(usize) -> (F192, F192) + Sync) -> (F192, F192) {
    assert_eq!(n_words, 1 << r_rest.len());
    let n_lo = r_rest.len().min(EQ_LO_VARS);
    let (eq_lo, eq_hi) = (build_eq(&r_rest[..n_lo]), build_eq(&r_rest[n_lo..]));
    parallel::map_reduce(
        eq_hi.len(),
        || (F192::ZERO, F192::ZERO),
        |hi| {
            let mut acc = (F192Unreduced::ZERO, F192Unreduced::ZERO);
            for (lo, &eq) in eq_lo.iter().enumerate() {
                let (s1, s_inf) = per_word(hi << n_lo | lo);
                acc.0 ^= eq.mul_unreduced(s1);
                acc.1 ^= eq.mul_unreduced(s_inf);
            }
            (eq_hi[hi] * acc.0.reduce(), eq_hi[hi] * acc.1.reduce())
        },
        |x, y| (x.0 + y.0, x.1 + y.1),
    )
}

/// Round `rho.len()`'s `(G(1), G(inf))`.
///
/// `r_in` holds the eq challenges of the later in-word variables and `r_rest` those of the word variables.
pub fn round(a: &[u64], b: &[u64], c: &[u64], rho: &[F192], r_in: &[F192], r_rest: &[F192]) -> (F192, F192) {
    let i = rho.len();
    assert_eq!(i + 1 + r_in.len(), 6, "a word holds six variables");
    assert!(a.len() == b.len() && a.len() == c.len());
    let eq_u = build_eq(r_in);

    if i == 0 {
        // On bits the product is an AND, and the leading coefficient that of the two XORed halves.
        let weights: Vec<F192> = (0..64).map(|bit| eq_u[bit / 2]).collect();
        let tables = byte_tables(&weights);
        return sum_words(a.len(), r_rest, |w| {
            let (a, b, c) = (a[w], b[w], c[w]);
            let one = ((a & b) ^ c) & ODD;
            let inf = ((a ^ (a << 1)) & (b ^ (b << 1))) & ODD;
            (fold(&tables, one), fold(&tables, inf))
        });
    }

    let width = 1usize << i;
    let mask = (1u64 << width) - 1;
    let eq_rho = build_eq(rho);
    if width <= JOINT_WIDTH {
        return joint_round(a, b, c, &eq_rho, &eq_u, r_rest);
    }
    let plain = byte_tables(&eq_rho);
    // The eq weight of `u` rides the `a` and `c` tables, so a term costs one product.
    let scaled: Vec<Vec<ByteTable>> = eq_u
        .iter()
        .map(|&e| byte_tables(&eq_rho.iter().map(|&x| e * x).collect::<Vec<_>>()))
        .collect();
    sum_words(a.len(), r_rest, |w| {
        let (a, b, c) = (a[w], b[w], c[w]);
        let mut one = F192Unreduced::ZERO;
        let mut inf = F192Unreduced::ZERO;
        for (u, scaled) in scaled.iter().enumerate() {
            let lo = 2 * u * width;
            let hi = lo + width;
            let (a0, a1) = ((a >> lo) & mask, (a >> hi) & mask);
            let (b0, b1) = ((b >> lo) & mask, (b >> hi) & mask);
            one ^= fold(scaled, a1).mul_unreduced(fold(&plain, b1));
            one ^= F192Unreduced::from(fold(scaled, (c >> hi) & mask));
            inf ^= fold(scaled, a0 ^ a1).mul_unreduced(fold(&plain, b0 ^ b1));
        }
        (one.reduce(), inf.reduce())
    })
}

/// Widest chunk whose whole term is tabulated: three chunks index `2^(3 * 4)` entries per `u`.
const JOINT_WIDTH: usize = 4;

/// A round on chunks narrow enough to tabulate each `u`'s whole term, so a word costs lookups and no product.
fn joint_round(a: &[u64], b: &[u64], c: &[u64], eq_rho: &[F192], eq_u: &[F192], r_rest: &[F192]) -> (F192, F192) {
    let width = eq_rho.len();
    let mask = (1u64 << width) - 1;
    let values = subset_sums(eq_rho);
    let n = 1usize << width;
    // `one[u][a | b << width | c << 2 width]` and `inf[u][a | b << width]`, the eq weight of `u` included.
    let one: Vec<Vec<F192>> = eq_u
        .iter()
        .map(|&e| {
            (0..n * n * n)
                .map(|idx| e * (values[idx % n] * values[idx / n % n] + values[idx / (n * n)]))
                .collect()
        })
        .collect();
    let inf: Vec<Vec<F192>> = eq_u
        .iter()
        .map(|&e| (0..n * n).map(|idx| e * values[idx % n] * values[idx / n]).collect())
        .collect();
    sum_words(a.len(), r_rest, |w| {
        let (a, b, c) = (a[w], b[w], c[w]);
        let (da, db) = (a ^ (a >> width), b ^ (b >> width));
        let mut acc = (F192::ZERO, F192::ZERO);
        for (u, (one, inf)) in one.iter().zip(&inf).enumerate() {
            let lo = 2 * u * width;
            let hi = lo + width;
            let chunk = |x: u64, at: usize| ((x >> at) & mask) as usize;
            acc.0 += one[chunk(a, hi) | chunk(b, hi) << width | chunk(c, hi) << (2 * width)];
            acc.1 += inf[chunk(da, lo) | chunk(db, lo) << width];
        }
        acc
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    /// The round polynomial from its definition, over tables of field elements.
    fn naive(tables: &[Vec<F192>; 3], r_later: &[F192]) -> (F192, F192) {
        let eq = build_eq(r_later);
        let [a, b, c] = tables;
        eq.iter()
            .enumerate()
            .fold((F192::ZERO, F192::ZERO), |(one, inf), (x, &e)| {
                (
                    one + e * (a[2 * x + 1] * b[2 * x + 1] + c[2 * x + 1]),
                    inf + e * (a[2 * x] + a[2 * x + 1]) * (b[2 * x] + b[2 * x + 1]),
                )
            })
    }

    #[test]
    fn rounds_match_naive() {
        let mut rng = Rng::new(0x1A_30D);
        let n_words = 1usize << 3;
        let words: [Vec<u64>; 3] = std::array::from_fn(|_| (0..n_words).map(|_| rng.next_u64()).collect());
        let mut tables = words.clone().map(|w| {
            (0..64 * n_words)
                .map(|bit| F192::new((w[bit / 64] >> (bit % 64)) & 1, 0, 0))
                .collect::<Vec<_>>()
        });
        let r = rng.ext_vec(6 + 3);
        let mut rho = Vec::new();
        for i in 0..6 {
            let got = round(&words[0], &words[1], &words[2], &rho, &r[i + 1..6], &r[6..]);
            assert_eq!(got, naive(&tables, &r[i + 1..]), "round {i}");
            let chi = rng.ext();
            for t in &mut tables {
                *t = t.chunks(2).map(|p| p[0] + chi * (p[0] + p[1])).collect();
            }
            rho.push(chi);
        }
    }
}
