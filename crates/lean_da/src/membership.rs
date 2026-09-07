//! Reed-Solomon membership on an additive domain.
//!
//! For an additive domain `D` of size `m`, `Σ_{x∈D} h(x) = 0` when
//! `deg(h) <= m-2`. Pairing codewords and comparing dimensions therefore gives
//! `RS_k(D)^⊥ = RS_{m-k}(D)`. At rate 1/2 the code is self-dual.
//!
//! The check uses `L(X) = ∏_{j < log2(k)} (1 + z_j · Vhat_j(X))`, where
//! `Vhat_j = X_{2^j}` is the normalized subspace polynomial of degree `2^j`.
//! Expanding this product gives every novel-basis coefficient below `k` with
//! tensor weights `⊗_j(1, z_j)`, so `L` is a codeword.
//!
//! For a fixed invalid row `w`, `⟨L,w⟩` is a nonzero multilinear polynomial in
//! `z`. Fresh independent uniform challenges accept it with probability at most
//! `log2(k)/2^192`. The external verifier derives the vector from the commitment.
//! The guest binds its hinted vector by hashing it and checks the inner products.

use fiat_shamir::FiatShamirState;
use fiat_shamir::merkle::hash_to_scalars;
use pcs::ntt::AdditiveNttF64;
use primitives::field::{F64, F192, F192BaseUnreduced};

use crate::{CODEWORD_SYMBOLS, DA_LOG_K, DaCommitment, LOG_M, row_count};

/// Transcript label, so a membership challenge can never be replayed as any other
/// challenge in the stack.
const LABEL: &[u8] = b"leanDA/rs-membership/v1";

/// `z_0 … z_{log k - 1}`, bound to the commitment.
///
/// The matrix root binds both commitment branches. The vector hash is not observed,
/// avoiding a circular dependency between the challenges and the vector.
pub fn membership_challenges(root: &[u8; 32]) -> Vec<F192> {
    let mut fs = FiatShamirState::from_label(LABEL);
    for scalar in hash_to_scalars(root) {
        fs.observe(scalar);
    }
    fs.sample_vec(DA_LOG_K)
}

/// The test vector deterministically derived from a matrix root.
pub fn membership_vector(root: &[u8; 32]) -> Vec<F192> {
    dual_codeword(&membership_challenges(root))
}

/// BLAKE2s of the vector's three little-endian 64-bit limbs per entry, in domain order.
pub fn vector_digest(vector: &[F192]) -> [u8; 32] {
    assert_eq!(vector.len(), CODEWORD_SYMBOLS);
    let bytes: Vec<u8> = vector
        .iter()
        .flat_map(|v| [v.c0, v.c1, v.c2].into_iter().flat_map(u64::to_le_bytes))
        .collect();
    primitives::hash::hash(&bytes)
}

/// `L` over the whole domain: the tensor `⊗_j (1, z_j)` encoded as a codeword.
///
/// The additive NTT's twiddles are `K`-valued and the transform is `K`-linear, so
/// an `E`-valued transform is three `K`-transforms on the limbs. `F192` is
/// `repr(C)` over three `u64`, which is exactly the interleaved layout
/// [`AdditiveNttF64::encode_interleaved_in_place`] wants for `num_ntts = 3`.
pub fn dual_codeword(z: &[F192]) -> Vec<F192> {
    assert_eq!(z.len(), DA_LOG_K, "one challenge per novel-basis variable");
    let m = CODEWORD_SYMBOLS;

    let mut buffer = vec![F192::ZERO; m];
    buffer[0] = F192::ONE;
    for (j, &zj) in z.iter().enumerate() {
        let (low, high) = buffer[..1 << (j + 1)].split_at_mut(1 << j);
        for (h, &l) in high.iter_mut().zip(low.iter()) {
            *h = l * zj;
        }
    }

    // SAFETY: `F192` is `repr(C)` over three `u64` and `F64` is `repr(transparent)`
    // over `u64`, so the buffer is `3m` limb-interleaved `F64` words with no padding.
    let limbs = unsafe { core::slice::from_raw_parts_mut(buffer.as_mut_ptr().cast::<F64>(), 3 * m) };
    AdditiveNttF64::standard(LOG_M).encode_interleaved_in_place(limbs, 3, 1);
    buffer
}

/// `⟨L, w_i⟩` for every row, which the caller checks against zero. Rows are `K`
/// valued and `L` is `E` valued, so a term is one `mul_base` (three PMULL), and the
/// whole row accumulates unreduced.
pub fn row_residuals(codewords: &[u64], dual: &[F192]) -> Vec<F192> {
    let n_rows = row_count(codewords.len(), CODEWORD_SYMBOLS);
    assert_eq!(dual.len(), CODEWORD_SYMBOLS, "the dual codeword spans the domain");
    let m = CODEWORD_SYMBOLS;
    parallel::map_collect(n_rows, |i| {
        let row = &codewords[i * m..(i + 1) * m];
        let mut acc = F192BaseUnreduced::ZERO;
        for (&l, &w) in dual.iter().zip(row) {
            acc ^= l.mul_base_unreduced(F64(w));
        }
        acc.reduce()
    })
}

/// Draw challenges from the commitment and test every row for membership.
/// The caller must separately bind `codewords` to the commitment.
#[tracing::instrument(name = "RS membership", skip_all)]
pub fn check_membership(commitment: &DaCommitment, codewords: &[u64]) -> bool {
    let dual = membership_vector(&commitment.root);
    row_residuals(codewords, &dual).iter().all(|&r| r == F192::ZERO)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BLOB_SYMBOLS;
    use crate::encode_rows;
    use rand::{Rng, SeedableRng, rngs::StdRng};

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
            let dot = a.iter().zip(&b).fold(F64::ZERO, |acc, (&x, &y)| acc + F64(x) * F64(y));
            assert_eq!(dot, F64::ZERO);
        }
    }

    /// `dual_codeword` runs one interleaved transform over the three `F192` limbs
    /// in place, which leans on `F192` being `repr(C)` over three `u64`. A scalar
    /// transform of each limb must give the same codeword.
    #[test]
    fn dual_codeword_matches_limbwise_transform() {
        let mut rng = StdRng::seed_from_u64(5);
        let z: Vec<F192> = (0..DA_LOG_K)
            .map(|_| F192::new(rng.random(), rng.random(), rng.random()))
            .collect();
        let dual = dual_codeword(&z);

        let mut tensor = vec![F192::ZERO; BLOB_SYMBOLS];
        tensor[0] = F192::ONE;
        for (j, &zj) in z.iter().enumerate() {
            let (low, high) = tensor[..1 << (j + 1)].split_at_mut(1 << j);
            for (h, &l) in high.iter_mut().zip(low.iter()) {
                *h = l * zj;
            }
        }
        let ntt = AdditiveNttF64::standard(LOG_M);
        for limb in 0..3 {
            let mut encoded = vec![F64::ZERO; CODEWORD_SYMBOLS];
            for (out, c) in encoded.iter_mut().zip(&tensor) {
                *out = F64([c.c0, c.c1, c.c2][limb]);
            }
            ntt.forward_transform_scalar(&mut encoded);
            for (x, (&got, &want)) in dual.iter().zip(&encoded).enumerate() {
                assert_eq!(F64([got.c0, got.c1, got.c2][limb]), want, "limb {limb} at {x}");
            }
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
        let (commitment, _) = crate::commit_codewords(codewords.clone());

        assert!(check_membership(&commitment, &codewords));

        for &position in &[0usize, 1, BLOB_SYMBOLS - 1, BLOB_SYMBOLS, CODEWORD_SYMBOLS - 1] {
            let mut corrupted = codewords.clone();
            let index = 3 * CODEWORD_SYMBOLS + position;
            corrupted[index] ^= 1;
            let (corrupted_commitment, _) = crate::commit_codewords(corrupted.clone());
            assert!(
                !check_membership(&corrupted_commitment, &corrupted),
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
        ntt.forward_transform_scalar(crate::encode::as_field_mut(&mut full));
        codewords[..CODEWORD_SYMBOLS].copy_from_slice(&full);
        let (commitment, _) = crate::commit_codewords(codewords.clone());

        assert!(!check_membership(&commitment, &codewords));
    }
}
