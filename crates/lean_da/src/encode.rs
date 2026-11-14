//! Systematic Reed-Solomon encoding at rate 1/2.
//!
//! An inverse additive NTT interpolates each payload row into novel-basis
//! coefficients. Encoding these on the full domain preserves the payload in
//! the first half of the codeword and adds redundancy in the second half.
//! The domain and the basis lie in `K`, so each limb of the symbols is a
//! `K`-codeword of its own: the transforms run on the two limbs as two lanes.

use pcs::ntt::AdditiveNttF64;
use primitives::field::F64;
use primitives::{cast_slice_mut, filled_vec};

use crate::{BLOB_SYMBOLS, Blob, Codeword, LOG_BLOB_SYMBOLS, LOG_CODEWORD_SYMBOLS};

/// Encode each blob into its codeword, the blob unchanged in its first half.
///
/// Padding rows are not materialized, being zero codewords.
#[tracing::instrument(name = "Encoding", skip_all)]
pub(crate) fn encode_rows(blobs: &[Blob]) -> Vec<Codeword> {
    let interpolation = AdditiveNttF64::standard(LOG_BLOB_SYMBOLS);
    let ntt = AdditiveNttF64::standard(LOG_CODEWORD_SYMBOLS);
    let mut limbs = vec![F64::ZERO; 2 * BLOB_SYMBOLS];

    // One row at a time: the transform dispatches internally at any row worth
    // encoding, and the pool panics on a nested dispatch, so the row loop must stay
    // sequential and let the NTT own the parallelism.
    // SAFETY: each codeword is written in full, the coefficients then zeros, before the transform reads it.
    unsafe {
        filled_vec(blobs.len(), |codewords: &mut [Codeword]| {
            for (blob, codeword) in blobs.iter().zip(codewords) {
                let (c0, c1) = limbs.split_at_mut(BLOB_SYMBOLS);
                for ((&symbol, l0), l1) in blob.iter().zip(&mut *c0).zip(&mut *c1) {
                    (*l0, *l1) = (F64(symbol as u64), F64((symbol >> 64) as u64));
                }
                interpolation.inverse_transform(c0);
                interpolation.inverse_transform(c1);
                // A symbol's words in memory are its limbs, low first (little-endian, `commit::as_bytes`).
                let words = cast_slice_mut::<u128, F64>(codeword);
                let (low, high) = words.split_at_mut(2 * BLOB_SYMBOLS);
                for ((pair, &l0), &l1) in low.as_chunks_mut::<2>().0.iter_mut().zip(&*c0).zip(&*c1) {
                    *pair = [l0, l1];
                }
                high.fill(F64::ZERO);
                ntt.encode_interleaved_in_place(words, 2, 1);
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn symbols(n: usize, seed: u128) -> Vec<u128> {
        (0..n as u128)
            .map(|i| 0x9E37_79B9_7F4A_7C15_F39C_C060_5CED_C835u128.wrapping_mul(i + seed))
            .collect()
    }

    /// The payload is the codeword's first half, and each limb is a codeword of its own: its
    /// novel-basis coefficients vanish from `k` on.
    #[test]
    fn encoding_preserves_payload_and_degree_bound() {
        let payload = symbols(3 * BLOB_SYMBOLS, 1);
        let blobs = payload.as_chunks::<BLOB_SYMBOLS>().0;
        let codewords = encode_rows(blobs);
        let ntt = AdditiveNttF64::standard(LOG_CODEWORD_SYMBOLS);
        for (row, codeword) in blobs.iter().zip(&codewords) {
            assert_eq!(&codeword[..BLOB_SYMBOLS], row);
            for shift in [0, 64] {
                let mut limb: Vec<F64> = codeword.iter().map(|&s| F64((s >> shift) as u64)).collect();
                ntt.inverse_transform(&mut limb);
                assert!(limb[BLOB_SYMBOLS..].iter().all(|&x| x == F64::ZERO));
            }
        }
    }

    /// Encoding commutes with XOR of payloads.
    #[test]
    fn encoding_is_linear() {
        let n = 2 * BLOB_SYMBOLS;
        let (a, b) = (symbols(n, 1), symbols(n, 7));
        let sum: Vec<u128> = a.iter().zip(&b).map(|(&x, &y)| x ^ y).collect();

        let encode = |v: &[u128]| encode_rows(v.as_chunks().0);
        let (ca, cb, cs) = (encode(&a), encode(&b), encode(&sum));
        for ((&x, &y), &z) in ca.as_flattened().iter().zip(cb.as_flattened()).zip(cs.as_flattened()) {
            assert_eq!(x ^ y, z);
        }
    }
}
