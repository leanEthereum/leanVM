//! A lookup array's read counts, carried in the exponent (§sec:lookup).
//!
//! Entry `j` of a lookup array is read `m_j` times, and the array pushes its tuple's leaf `L_j` to the power `m_j`.
//! The count is a committed `K` word whose low 32 bits are the binary digits of `m_j`, so the push is one leaf per digit:
//!
//! ```text
//!   leaf (j, b) = 1 + m_{j,b} · (L_j^(2^b) + 1)        b < 32, at index 32 j + b
//! ```
//!
//! A digit is Boolean because it is a bit of a committed word, which the opening reaches through ring switching.
//! A count is an integer, never a field element, so a count off by two is seen where a fractional sum in characteristic 2 would not see it.
//!
//! Those leaves' share of the GKR claim at `(ζ_b, ζ_j)` is `1 + X`, and one sumcheck over the entries proves `X`:
//!
//! ```text
//!   X = Σ_j eq(ζ_j, j) · Σ_b eq(ζ_b, b) · m_{j,b} · (L_j^(2^b) + 1)
//! ```
//!
//! It ends on the count column's 64 bit slices at a point `r`, and on `L^(2^b)` there, which is public.
//! Squaring is additive in characteristic 2, so `L_j^(2^b) = β^(2^b) + Σ_i w_i^(2^b) · σ_{j,i}^(2^b)`.
//! A coordinate's `σ^(2^b)` at `r` is its bit slices at `r`, bit `k` weighed by `(x^k)^(2^b)`.

use crate::leaf::{Block, Coord};
use fiat_shamir::transcript::{Challenger, ProverState, Receiver, Transmitter, VerifierState};
use primitives::field::{F64, F192, F192Unreduced};
use primitives::multilinear::{eq_table, poly_eval};

/// `log2` of the digits a read count has.
pub const LOG_COUNT_BITS: usize = 5;
/// The digits a read count has: an entry is read fewer than `2^32` times.
pub const COUNT_BITS: usize = 1 << LOG_COUNT_BITS;
/// The bits of a committed word, each of which has a slice at the sumcheck's point.
const WORD_BITS: usize = 64;

/// What the count sumcheck leaves on the count column: the MLE of each of its 64 bit slices at `point`.
///
/// The opening binds the slices to the committed column by ring switching.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CountClaim {
    /// The committed column holding the counts.
    pub col: usize,
    pub point: Vec<F192>,
    pub slices: Vec<F192>,
}

/// Why a count sumcheck rejects.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Error {
    /// The proof stream is malformed.
    #[error(transparent)]
    Transcript(#[from] fiat_shamir::transcript::Error),
    /// The sumcheck does not end where the count bits and the public leaves put it.
    #[error("the read counts' sumcheck does not end at their bits")]
    Terminal,
}

/// Prove the count leaves' share `X` of the leaf claim at `zeta`, the block's low point.
///
/// `leaves` holds each entry's leaf `L_j` and `counts` its count word.
/// Sends `X`, the sumcheck, then the 64 slices, and returns `X` with the claim on the counts.
pub(crate) fn prove(
    col: usize,
    leaves: &[F192],
    counts: &[F64],
    zeta: &[F192],
    ps: &mut ProverState,
) -> (F192, CountClaim) {
    let len = counts.len();
    let n = crate::log2_strict_usize(len);
    assert_eq!(leaves.len(), len);
    assert_eq!(zeta.len(), LOG_COUNT_BITS + n);
    let (zeta_digits, zeta_rows) = zeta.split_at(LOG_COUNT_BITS);
    let digit_weights = eq_table(zeta_digits);
    let used = counts.iter().fold(0, |acc, c| acc | c.0);
    assert_eq!(used >> COUNT_BITS, 0, "a read count has more than {COUNT_BITS} digits");

    // Why: a digit no entry has contributes nothing, its column being zero, so only the digits in use get a table.
    let digits: Vec<usize> = (0..COUNT_BITS).filter(|&b| used >> b & 1 == 1).collect();
    let mut m = Vec::with_capacity(digits.len() * len);
    let mut p = Vec::with_capacity(digits.len() * len);
    let mut power = leaves.to_vec();
    let mut at = 0;
    for &b in &digits {
        while at < b {
            parallel::for_each_mut(&mut power, |_, l| *l = l.square());
            at += 1;
        }
        m.extend(counts.iter().map(|c| F192::from(F64(c.0 >> b & 1))));
        p.extend(power.iter().map(|&l| digit_weights[b] * (l + F192::ONE)));
    }

    let eq_rows = eq_table(zeta_rows);
    let excess = (0..digits.len()).fold(F192::ZERO, |acc, k| {
        let (m, p) = (&m[k * len..(k + 1) * len], &p[k * len..(k + 1) * len]);
        (0..len).fold(acc, |acc, j| acc + eq_rows[j] * m[j] * p[j])
    });
    ps.add_scalar(excess);

    let mut point = Vec::with_capacity(n);
    let mut half = len;
    for round in 0..n {
        half /= 2;
        let eq_rest = eq_table(&zeta_rows[round + 1..]);
        let (m_ref, p_ref) = (&m, &p);
        let sums = parallel::map_reduce(
            digits.len(),
            || [F192Unreduced::ZERO; 3],
            |k| {
                let (m, p) = (&m_ref[k * len..], &p_ref[k * len..]);
                let mut acc = [F192Unreduced::ZERO; 3];
                for (y, &e) in eq_rest.iter().enumerate() {
                    let (m0, p0) = (m[2 * y], p[2 * y]);
                    let (dm, dp) = (m0 + m[2 * y + 1], p0 + p[2 * y + 1]);
                    let (em0, edm) = (e * m0, e * dm);
                    acc[0] ^= em0.mul_unreduced(p0);
                    acc[1] ^= em0.mul_unreduced(dp) ^ edm.mul_unreduced(p0);
                    acc[2] ^= edm.mul_unreduced(dp);
                }
                acc
            },
            |a, b| std::array::from_fn(|i| a[i] ^ b[i]),
        );
        ps.add_round_poly(&sums.map(F192Unreduced::reduce), true);
        let r = ps.sample();
        point.push(r);
        let fold = |t: &mut [F192]| {
            for y in 0..half {
                t[y] = t[2 * y] + r * (t[2 * y] + t[2 * y + 1]);
            }
        };
        parallel::chunks_mut2(&mut m, &mut p, len, |_, m, p| {
            fold(m);
            fold(p);
        });
    }

    let slices = ::pcs::ring_switch::fold_1b_rows(counts, &eq_table(&point));
    debug_assert!(
        digits.iter().enumerate().all(|(k, &b)| slices[b] == m[k * len]),
        "the folded digits are the count column's bit slices"
    );
    ps.add_scalars(&slices);
    (excess, CountClaim { col, point, slices })
}

/// Verify the count leaves' share `X` of the leaf claim at `zeta`, the low point of `block`, whose fingerprint is `(w, β)`.
///
/// Returns `X` with the claim on the counts, which the opening settles.
pub(crate) fn verify(
    block: &Block,
    col: usize,
    zeta: &[F192],
    w: &[F192],
    beta: F192,
    vs: &mut VerifierState,
) -> Result<(F192, CountClaim), Error> {
    let n = block.kappa;
    assert_eq!(zeta.len(), LOG_COUNT_BITS + n);
    let (zeta_digits, zeta_rows) = zeta.split_at(LOG_COUNT_BITS);
    let excess = vs.next_scalar()?;
    let mut claim = excess;
    let mut point = Vec::with_capacity(n);
    for &z in zeta_rows {
        let round = vs.next_round_poly(3, claim, Some(z))?;
        let r = vs.sample();
        claim = poly_eval(&round, r);
        point.push(r);
    }
    let slices = vs.next_scalars(WORD_BITS)?;

    let powers = frobenius_leaves(block, w, beta, &point);
    let digit_weights = eq_table(zeta_digits);
    let terminal = (0..COUNT_BITS).fold(F192::ZERO, |acc, b| {
        acc + digit_weights[b] * slices[b] * (powers[b] + F192::ONE)
    });
    if claim != terminal {
        return Err(Error::Terminal);
    }
    Ok((excess, CountClaim { col, point, slices }))
}

/// `L^(2^b)` at `point` for every digit `b`: the MLE over the block's rows of each leaf squared `b` times.
fn frobenius_leaves(block: &Block, w: &[F192], beta: F192, point: &[F192]) -> [F192; COUNT_BITS] {
    let eq = eq_table(point);
    // Coordinate `i`'s bit slices at `point`: `slices[k]` is the MLE of its bit `k`.
    let slices: Vec<Vec<F192>> = block
        .coords
        .iter()
        .map(|c| match c {
            Coord::Const(v) => (0..WORD_BITS).map(|k| F192::from(F64(v.0 >> k & 1))).collect(),
            Coord::IntIndex { base, shift } => (0..WORD_BITS)
                .map(|k| {
                    let row = k.checked_sub(*shift as usize).and_then(|t| point.get(t));
                    F192::from(F64(base.0 >> k & 1)) + row.copied().unwrap_or(F192::ZERO)
                })
                .collect(),
            Coord::Public(vals) => ::pcs::ring_switch::fold_1b_rows(vals, &eq),
            _ => unreachable!("a lookup's entries are public"),
        })
        .collect();

    let mut out = [F192::ZERO; COUNT_BITS];
    let (mut beta_pow, mut w_pow, mut x_pow) = (beta, w.to_vec(), F64(2));
    for slot in &mut out {
        // `(x^k)^(2^b) = (x^(2^b))^k`, the image of bit `k` under `b` squarings.
        let mut basis = [F64::ONE; WORD_BITS];
        for k in 1..WORD_BITS {
            basis[k] = basis[k - 1] * x_pow;
        }
        *slot = slices.iter().zip(&w_pow).fold(beta_pow, |acc, (s, &wi)| {
            let squared = s.iter().zip(basis).fold(F192::ZERO, |sum, (&v, k)| sum + v.mul_base(k));
            acc + wi * squared
        });
        beta_pow = beta_pow.square();
        w_pow.iter_mut().for_each(|wi| *wi = wi.square());
        x_pow = x_pow.square();
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::leaf::{build_leaves, fingerprint_weights, layout, tuple_leaves};
    use std::sync::Arc;

    #[test]
    fn the_counts_reduce_to_their_bits() {
        // Invariant: the sumcheck proves the digit leaves' share of the leaf claim, and ends on the committed counts' bits.
        //
        // Fixture state: eight entries read 3, 0, 1, 2, 5, 0, 7 and 1 times, their tuples a constant, an address and a public word.
        // Mutation: the slices sent at the end are those of counts reading entry 0 twice more, as a prover committing them would send.
        let words: Vec<F64> = (0..8u64)
            .map(|i| F64(0x9e37_79b9_7f4a_7c15u64.wrapping_mul(i + 1)))
            .collect();
        let coords = vec![
            Coord::Const(F64(4)),
            Coord::IntIndex {
                base: F64(0x1000_0000),
                shift: 2,
            },
            Coord::Public(Arc::new(words)),
        ];
        let block = Block::lookup(3, coords, 0);
        let counts: Vec<F64> = [3, 0, 1, 2, 5, 0, 7, 1].map(F64).to_vec();
        let cols: [&[F64]; 1] = [&counts];
        let alphas: Vec<F192> = (0..4).map(|i| F192::new(3 + i, 5 * i + 1, 7)).collect();
        let (w, beta) = (fingerprint_weights(&alphas), F192::new(11, 13, 17));
        let zeta: Vec<F192> = (0..8).map(|i| F192::new(19 + i, 23, 29 * i + 1)).collect();

        let leaves = build_leaves(
            std::slice::from_ref(&block),
            &layout(std::slice::from_ref(&block)),
            &cols,
            &w,
            beta,
        );
        let share = eq_table(&zeta)
            .iter()
            .zip(leaves.iter())
            .fold(F192::ZERO, |acc, (&e, &l)| acc + e * l);
        let mut ps = ProverState::from_label(b"read-counts");
        let entries = tuple_leaves(&block, &cols, &w, beta);
        let (excess, claim) = prove(0, &entries, &counts, &zeta, &mut ps);
        assert_eq!(
            F192::ONE + excess,
            share,
            "the excess is the digit leaves' share, less their mass"
        );

        let mut proof = ps.into_proof();
        let mut vs = VerifierState::from_label(b"read-counts", &proof);
        assert_eq!(verify(&block, 0, &zeta, &w, beta, &mut vs), Ok((excess, claim.clone())));

        let mut forged = counts.clone();
        forged[0] = F64(5);
        let slices = ::pcs::ring_switch::fold_1b_rows(&forged, &eq_table(&claim.point));
        let at = proof.stream.len() - WORD_BITS;
        proof.stream[at..].copy_from_slice(&slices);
        let mut vs = VerifierState::from_label(b"read-counts", &proof);
        assert_eq!(verify(&block, 0, &zeta, &w, beta, &mut vs), Err(Error::Terminal));
    }
}
