//! Systematic Reed-Solomon encoding at rate 1/2.
//!
//! An inverse additive NTT interpolates each payload row into novel-basis
//! coefficients. Encoding these on the full domain preserves the payload in
//! the first half of the codeword and adds redundancy in the second half.

use pcs::ntt::AdditiveNttF64;
use primitives::field::F64;

use crate::{BLOB_SYMBOLS, CODEWORD_SYMBOLS, DA_LOG_K, LOG_M, row_count};

/// Encode `n` rows of `k` symbols into `n` codewords of `m` symbols, row-major.
///
/// `rows` is the payload, `n_rows · k` long. The returned buffer is `n_rows · m`
/// long, with each payload row unchanged in its codeword's first half.
/// Symbols are little-endian 64-bit words; every bit pattern is valid.
/// Padding rows are not materialized, being zero codewords.
#[tracing::instrument(name = "Encoding", skip_all)]
pub fn encode_rows(rows: &[u64]) -> Vec<u64> {
    let n_rows = row_count(rows.len(), BLOB_SYMBOLS);
    let (k, m) = (BLOB_SYMBOLS, CODEWORD_SYMBOLS);
    let interpolation = AdditiveNttF64::standard(DA_LOG_K);
    let ntt = AdditiveNttF64::standard(LOG_M);

    // One row at a time: the transform dispatches internally at any row worth
    // encoding, and the pool panics on a nested dispatch, so the row loop must stay
    // sequential and let the NTT own the parallelism.
    let mut codewords = vec![0; n_rows * m];
    for (i, codeword) in codewords.chunks_exact_mut(m).enumerate() {
        codeword[..k].copy_from_slice(&rows[i * k..(i + 1) * k]);
        let codeword = as_field_mut(codeword);
        interpolation.inverse_transform(&mut codeword[..k]);
        ntt.encode_interleaved_in_place(codeword, 1, 1);
    }
    codewords
}

/// Borrow native symbols as field elements without allocating or copying.
pub(crate) fn as_field_mut(data: &mut [u64]) -> &mut [F64] {
    // SAFETY: F64 is repr(transparent) over u64, with every bit pattern valid.
    unsafe { core::slice::from_raw_parts_mut(data.as_mut_ptr().cast::<F64>(), data.len()) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encoding_preserves_payload_and_degree_bound() {
        let payload: Vec<u64> = (0..3 * BLOB_SYMBOLS)
            .map(|i| 0x9E37_79B9_7F4A_7C15u64.wrapping_mul(i as u64 + 1))
            .collect();
        let mut codewords = encode_rows(&payload);
        let ntt = AdditiveNttF64::standard(LOG_M);
        for (row, codeword) in payload
            .as_chunks::<BLOB_SYMBOLS>()
            .0
            .iter()
            .zip(codewords.as_chunks_mut::<CODEWORD_SYMBOLS>().0.iter_mut())
        {
            assert_eq!(&codeword[..BLOB_SYMBOLS], row);
            ntt.inverse_transform(as_field_mut(codeword));
            assert!(codeword[BLOB_SYMBOLS..].iter().all(|&x| x == 0));
        }
    }

    /// Encoding commutes with XOR of payloads.
    #[test]
    fn encoding_is_linear() {
        let n = 2 * BLOB_SYMBOLS;
        let a: Vec<u64> = (0..n)
            .map(|i| 0x9E37_79B9_7F4A_7C15u64.wrapping_mul(i as u64 + 1))
            .collect();
        let b: Vec<u64> = (0..n)
            .map(|i| 0xBF58_476D_1CE4_E5B9u64.wrapping_mul(i as u64 + 3))
            .collect();
        let sum: Vec<u64> = a.iter().zip(&b).map(|(&x, &y)| x ^ y).collect();

        let (ca, cb, cs) = (encode_rows(&a), encode_rows(&b), encode_rows(&sum));
        for ((&x, &y), &z) in ca.iter().zip(&cb).zip(&cs) {
            assert_eq!(x ^ y, z);
        }
    }
}
