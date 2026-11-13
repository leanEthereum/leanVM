//! Systematic Reed-Solomon encoding at rate 1/2.
//!
//! An inverse additive NTT interpolates each payload row into novel-basis
//! coefficients. Encoding these on the full domain preserves the payload in
//! the first half of the codeword and adds redundancy in the second half.

use pcs::ntt::AdditiveNttF64;
use primitives::field::F64;
use primitives::{cast_slice_mut, filled_vec};

use crate::{BLOB_SYMBOLS, Blob, Codeword, LOG_BLOB_SYMBOLS, LOG_CODEWORD_SYMBOLS};

/// Encode each blob into its codeword, the blob unchanged in its first half.
///
/// Symbols are little-endian 64-bit words; every bit pattern is valid. Padding rows are not
/// materialized, being zero codewords.
#[tracing::instrument(name = "Encoding", skip_all)]
pub(crate) fn encode_rows(blobs: &[Blob]) -> Vec<Codeword> {
    let interpolation = AdditiveNttF64::standard(LOG_BLOB_SYMBOLS);
    let ntt = AdditiveNttF64::standard(LOG_CODEWORD_SYMBOLS);

    // One row at a time: the transform dispatches internally at any row worth
    // encoding, and the pool panics on a nested dispatch, so the row loop must stay
    // sequential and let the NTT own the parallelism.
    // SAFETY: each codeword is written in full, the blob then zeros, before the transforms read it.
    unsafe {
        filled_vec(blobs.len(), |codewords: &mut [Codeword]| {
            for (blob, codeword) in blobs.iter().zip(codewords) {
                let (low, high) = codeword.split_at_mut(BLOB_SYMBOLS);
                low.copy_from_slice(blob);
                high.fill(0);
                let codeword = cast_slice_mut::<u64, F64>(codeword);
                interpolation.inverse_transform(&mut codeword[..BLOB_SYMBOLS]);
                ntt.encode_interleaved_in_place(codeword, 1, 1);
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encoding_preserves_payload_and_degree_bound() {
        let payload: Vec<u64> = (0..3 * BLOB_SYMBOLS)
            .map(|i| 0x9E37_79B9_7F4A_7C15u64.wrapping_mul(i as u64 + 1))
            .collect();
        let blobs = payload.as_chunks::<BLOB_SYMBOLS>().0;
        let mut codewords = encode_rows(blobs);
        let ntt = AdditiveNttF64::standard(LOG_CODEWORD_SYMBOLS);
        for (row, codeword) in blobs.iter().zip(&mut codewords) {
            assert_eq!(&codeword[..BLOB_SYMBOLS], row);
            ntt.inverse_transform(cast_slice_mut::<u64, F64>(codeword));
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

        let encode = |v: &[u64]| encode_rows(v.as_chunks().0);
        let (ca, cb, cs) = (encode(&a), encode(&b), encode(&sum));
        for ((&x, &y), &z) in ca.as_flattened().iter().zip(cb.as_flattened()).zip(cs.as_flattened()) {
            assert_eq!(x ^ y, z);
        }
    }
}
