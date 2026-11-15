//! Systematic Reed-Solomon encoding at rate one half, by the additive NTT on the novel basis (Annex D).
//!
//! The domain and the basis lie in `K`, so each limb of a symbol is a `K`-codeword of its own: its payload is
//! interpolated into novel-basis coefficients, which are evaluated on the domain twice its size, the payload's domain
//! being that domain's first half.

use verifier::K;

use crate::{BLOB_SYMBOLS, Blob, CODEWORD_SYMBOLS, LOG_CODEWORD_SYMBOLS};

/// Each blob's codeword, end to end.
pub(crate) fn encode_rows(blobs: &[Blob]) -> Vec<u128> {
    let twiddles = twiddles();
    let mut codewords = vec![0u128; blobs.len() * CODEWORD_SYMBOLS];
    let mut limb = vec![K(0); CODEWORD_SYMBOLS];
    for (blob, codeword) in blobs.iter().zip(codewords.chunks_exact_mut(CODEWORD_SYMBOLS)) {
        for shift in [0, 64] {
            for (x, &symbol) in limb.iter_mut().zip(blob) {
                *x = K((symbol >> shift) as u64);
            }
            encode_limb(&mut limb, &twiddles);
            for (symbol, x) in codeword.iter_mut().zip(&limb) {
                *symbol |= (x.0 as u128) << shift;
            }
        }
    }
    codewords
}

/// The codeword of the payload in `limb`'s first half, in place.
fn encode_limb(limb: &mut [K], twiddles: &[Vec<K>]) {
    let (payload, rest) = limb.split_at_mut(BLOB_SYMBOLS);
    interpolate(payload, twiddles);
    rest.fill(K(0));
    evaluate(limb, twiddles);
}

/// Novel-basis coefficients from values on the domain of `data.len()` points: [`evaluate`]'s butterflies, inverted,
/// in reverse.
fn interpolate(data: &mut [K], twiddles: &[Vec<K>]) {
    for i in 0..data.len().ilog2() as usize {
        for (block, &t) in data.chunks_exact_mut(2 << i).zip(&twiddles[i]) {
            let (top, bot) = block.split_at_mut(1 << i);
            for (u, v) in top.iter_mut().zip(bot) {
                *v = *v + *u;
                *u = *u + *v * t;
            }
        }
    }
}

/// Values on the domain of `data.len()` points from novel-basis coefficients: the butterflies `2^i` points apart,
/// largest first.
fn evaluate(data: &mut [K], twiddles: &[Vec<K>]) {
    for i in (0..data.len().ilog2() as usize).rev() {
        for (block, &t) in data.chunks_exact_mut(2 << i).zip(&twiddles[i]) {
            let (top, bot) = block.split_at_mut(1 << i);
            for (u, v) in top.iter_mut().zip(bot) {
                *u = *u + *v * t;
                *v = *v + *u;
            }
        }
    }
}

/// `twiddles[i][b]`: the twiddle of block `b` of the butterflies `2^i` points apart on the codeword's domain, the
/// normalized subspace polynomial `s_i` (`s_i(x^i) = 1`) at the block's offset `sum_j bit_j(b) x^(i + 1 + j)`. A block
/// of the payload's domain has the same twiddle.
fn twiddles() -> Vec<Vec<K>> {
    // `s_0(v) = v`, `s_(i+1)(v) = s_i(v) (s_i(v) + s_i(x^i))`, each at `x^i..x^LOG_CODEWORD_SYMBOLS`.
    let mut s: Vec<K> = (0..LOG_CODEWORD_SYMBOLS).map(|j| K(1 << j)).collect();
    let mut twiddles = Vec::new();
    while let Some((&first, rest)) = s.split_first() {
        let inv = first.inv();
        let basis: Vec<K> = rest.iter().map(|&v| v * inv).collect();
        // Each block's offset adds one basis value to that of the block with its top bit cleared.
        let mut row = vec![K(0)];
        for &value in &basis {
            row.extend_from_within(..);
            let half = row.len() / 2;
            for t in &mut row[half..] {
                *t = *t + value;
            }
        }
        twiddles.push(row);
        s = rest.iter().map(|&v| v * (v + first)).collect();
    }
    twiddles
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
        let codeword = encode_rows(&[blob]);
        assert_eq!(codeword[..BLOB_SYMBOLS], blob);
        for shift in [0, 64] {
            let mut limb: Vec<K> = codeword.iter().map(|&s| K((s >> shift) as u64)).collect();
            interpolate(&mut limb, &twiddles());
            assert!(limb[BLOB_SYMBOLS..].iter().all(|&x| x == K(0)));
        }
    }
}
