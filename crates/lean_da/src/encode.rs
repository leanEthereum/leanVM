//! Systematic Reed-Solomon encoding at rate one half, by the stable prover's additive NTT (Annex D).

use pcs::ntt::AdditiveNttF64;
use primitives::cast_slice_mut;
use primitives::field::F64;

use crate::{BLOB_SYMBOLS, Blob, CODEWORD_SYMBOLS, LOG_BLOB_SYMBOLS, LOG_CODEWORD_SYMBOLS, Symbol};

/// Each blob's codeword, end to end, the blob unchanged in its first half: its novel-basis coefficients, interpolated
/// on the payload's domain, evaluated on the domain twice its size. A symbol's words in memory are its limbs, low first,
/// so its two limbs are the transforms' two lanes.
pub fn encode_rows(blobs: &[Blob]) -> Vec<Symbol> {
    let interpolation = AdditiveNttF64::standard(LOG_BLOB_SYMBOLS);
    let ntt = AdditiveNttF64::standard(LOG_CODEWORD_SYMBOLS);
    let mut codewords = vec![0; blobs.len() * CODEWORD_SYMBOLS];
    for (blob, codeword) in blobs.iter().zip(codewords.as_chunks_mut::<CODEWORD_SYMBOLS>().0) {
        codeword[..BLOB_SYMBOLS].copy_from_slice(blob);
        let words = cast_slice_mut::<Symbol, F64>(codeword);
        interpolation.inverse_transform(&mut words[..2 * BLOB_SYMBOLS], 2);
        ntt.encode_interleaved_in_place(words, 2, 1);
    }
    codewords
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The payload is the codeword's first half, and each limb is a codeword of its own: its novel-basis coefficients
    /// vanish from `BLOB_SYMBOLS` on.
    #[test]
    fn encoding_preserves_payload_and_degree_bound() {
        let blob: Blob =
            std::array::from_fn(|i| 0x9E37_79B9_7F4A_7C15_F39C_C060_5CED_C835u128.wrapping_mul(i as u128 + 1));
        let mut codeword = encode_rows(&[blob]);
        assert_eq!(codeword[..BLOB_SYMBOLS], blob);
        let words = cast_slice_mut::<Symbol, F64>(&mut codeword);
        AdditiveNttF64::standard(LOG_CODEWORD_SYMBOLS).inverse_transform(words, 2);
        assert!(words[2 * BLOB_SYMBOLS..].iter().all(|&word| word == F64::ZERO));
    }
}
