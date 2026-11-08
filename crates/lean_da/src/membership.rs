//! Reed-Solomon membership on an additive domain.
//!
//! For an additive domain `D` of size `m`, `Σ_{x∈D} h(x) = 0` when
//! `deg(h) <= m-2`. Pairing codewords and comparing dimensions therefore gives
//! `RS_k(D)^⊥ = RS_{m-k}(D)`. At rate 1/2 the code is self-dual.
//!
//! The check uses `L(X) = ∏_{j < log2(k)} (1 + z^(2^j) · Vhat_j(X))` for one challenge `z`,
//! where `Vhat_j = X_{2^j}` is the normalized subspace polynomial of degree `2^j`.
//! Expanding this product gives every novel-basis polynomial below `k`, `X_i` with
//! weight `z^i`, so `L` is a codeword.
//!
//! For a fixed invalid row `w`, `⟨L,w⟩ = Σ_i z^i ⟨X_i,w⟩` is a nonzero polynomial in `z`
//! of degree below `k`. A uniform challenge accepts it with probability at most
//! `(k-1)/2^192`. The verifier crate derives `z` from the root, outside the SNARK, and the
//! statement binds it; the guest builds `L` from `z` and checks the inner products.

use pcs::ntt::AdditiveNttF64;
use primitives::field::F64;

use crate::{DA_LOG_K, LOG_M};

/// `Vhat_j` at the domain point whose bits above `j` are `y`'s, `Σ_l bit_l(y) · β_(j+1+l)`:
/// the NTT's twiddles. `Vhat_j(β_j) = 1` and the bits below `j` vanish, so `Vhat_j` at point
/// `i` is `bit_j(i)` plus this at `i >> (j + 1)`: the factors the guest builds `L` from.
pub fn subspace_above() -> impl Fn(usize, usize) -> F64 {
    let ntt = AdditiveNttF64::standard(LOG_M);
    move |j, y| {
        assert!(j <= DA_LOG_K && y >> (DA_LOG_K - j) == 0, "bits above {j} only");
        ntt.twiddle(DA_LOG_K - j, y)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BLOB_SYMBOLS, CODEWORD_SYMBOLS, encode_rows};
    use primitives::field::{F192, powers};
    use rand::{Rng, SeedableRng, rngs::StdRng};

    /// `L` over the whole domain as the guest builds it: at each point, the product of its factors.
    fn dual_codeword(z: F192) -> Vec<F192> {
        let vhat = subspace_above();
        let z_powers: Vec<F192> = std::iter::successors(Some(z), |&p| Some(p * p))
            .take(DA_LOG_K)
            .collect();
        (0..CODEWORD_SYMBOLS)
            .map(|i| {
                (0..DA_LOG_K)
                    .map(|j| {
                        let at = F64((i >> j) as u64 & 1) + vhat(j, i >> (j + 1));
                        F192::ONE + z_powers[j].mul_base(at)
                    })
                    .product()
            })
            .collect()
    }

    /// Test every row against the vector of a random challenge.
    fn check_membership(z: F192, codewords: &[u64]) -> bool {
        let dual = dual_codeword(z);
        codewords.chunks(CODEWORD_SYMBOLS).all(|row| {
            let residual = dual.iter().zip(row).map(|(&l, &w)| l.mul_base(F64(w))).sum::<F192>();
            residual == F192::ZERO
        })
    }

    fn random_challenge(rng: &mut StdRng) -> F192 {
        F192::new(rng.random(), rng.random(), rng.random())
    }

    fn random_rows(rng: &mut StdRng, n: usize) -> Vec<u64> {
        (0..n).map(|_| rng.random()).collect()
    }

    /// The claim the whole check rests on: over an F_2-subspace domain at rate
    /// 1/2 the code is self-dual, so any two codewords are orthogonal. If this
    /// fails, `check_membership` is testing the wrong relation.
    #[test]
    fn code_is_self_dual() {
        let mut rng = StdRng::seed_from_u64(3);
        for _ in 0..4 {
            let a = encode_rows(&random_rows(&mut rng, BLOB_SYMBOLS));
            let b = encode_rows(&random_rows(&mut rng, BLOB_SYMBOLS));
            let dot = a.iter().zip(&b).map(|(&x, &y)| F64(x) * F64(y)).sum::<F64>();
            assert_eq!(dot, F64::ZERO);
        }
    }

    /// The product form, with the factors [`subspace_above`] gives, is the codeword whose
    /// novel-basis coefficients are `z^i` below `k`, in the codewords' domain order.
    #[test]
    fn dual_codeword_has_the_powers_of_z_as_coefficients() {
        let z = random_challenge(&mut StdRng::seed_from_u64(5));
        let dual = dual_codeword(z);
        let want = powers(z, BLOB_SYMBOLS);
        let ntt = AdditiveNttF64::standard(LOG_M);
        for limb in 0..3 {
            let mut coefficients: Vec<F64> = dual.iter().map(|v| F64(v.to_limbs()[limb])).collect();
            ntt.inverse_transform(&mut coefficients);
            let (low, high) = coefficients.split_at(BLOB_SYMBOLS);
            assert!(low.iter().zip(&want).all(|(c, w)| c.0 == w.to_limbs()[limb]));
            assert!(high.iter().all(|&c| c == F64::ZERO));
        }
    }

    /// An honestly encoded payload passes, and flipping a single symbol of a single
    /// row fails. That single flip is the case the check exists for: it is exactly
    /// what a builder would do to make a row unrecoverable while still answering
    /// every sample consistently.
    #[test]
    fn membership_accepts_codewords_and_rejects_a_flipped_symbol() {
        let n_rows = 5;
        let mut rng = StdRng::seed_from_u64(11);
        let rows = random_rows(&mut rng, n_rows * BLOB_SYMBOLS);
        let codewords = encode_rows(&rows);
        let z = random_challenge(&mut rng);

        assert!(check_membership(z, &codewords));

        for &position in &[0usize, 1, BLOB_SYMBOLS - 1, BLOB_SYMBOLS, CODEWORD_SYMBOLS - 1] {
            let mut corrupted = codewords.clone();
            corrupted[3 * CODEWORD_SYMBOLS + position] ^= 1;
            assert!(
                !check_membership(z, &corrupted),
                "a flip at {position} passed the membership check"
            );
        }
    }

    /// A row that is a codeword of the wrong degree (the full domain rather than
    /// the degree bound) must fail: rate is what the check enforces, and a
    /// rate-1 "codeword" is what an unrecoverable payload looks like.
    #[test]
    fn membership_rejects_a_full_degree_row() {
        let n_rows = 2;
        let mut rng = StdRng::seed_from_u64(13);
        let rows = random_rows(&mut rng, n_rows * BLOB_SYMBOLS);
        let mut codewords = encode_rows(&rows);
        let ntt = AdditiveNttF64::standard(LOG_M);
        let mut full = random_rows(&mut rng, CODEWORD_SYMBOLS);
        ntt.encode_interleaved_in_place(primitives::cast_slice_mut::<u64, F64>(&mut full), 1, 0);
        codewords[..CODEWORD_SYMBOLS].copy_from_slice(&full);

        assert!(!check_membership(random_challenge(&mut rng), &codewords));
    }
}
