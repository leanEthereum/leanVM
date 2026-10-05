//! The key's and the signature's bit-packed encodings, read from big-endian words.

use crate::{BODY_BYTES, BODY_WORDS, FalconVerifyError, N, PublicKey, Q};

/// Coefficient `K` of a group of 32: the 14 bits at bit `14 K`, counted from the top of the group's first word.
#[inline(always)]
fn field<const K: usize>(words: &[u64]) -> i64 {
    let (i, shift) = (14 * K / 64, 14 * K % 64);
    let v = (words[i] << shift) >> 50;
    // Its low bits spill into the next word when it starts past bit 50.
    let v = if shift > 50 {
        v | (words[i + 1] >> (114 - shift))
    } else {
        v
    };
    v as i64
}

/// Unpack a group of 32 coefficients from 7 words, every shift a constant, each checked below `q`.
macro_rules! unpack {
    ($words:ident, $out:ident, $($k:literal)*) => {
        $(
            let v = field::<$k>($words);
            if v >= Q {
                return Err(FalconVerifyError::InvalidPublicKey);
            }
            $out[$k] = v;
        )*
    };
}

/// The key's `h`: 14 bits per coefficient, each below `q`.
///
/// 32 coefficients fill 7 words exactly, so a group's shifts are constants.
pub fn decode_public_key(pk: &PublicKey, h: &mut [i64; N]) -> Result<(), FalconVerifyError> {
    for (words, coefficients) in pk.h.as_chunks::<7>().0.iter().zip(h.as_chunks_mut::<32>().0) {
        unpack!(words, coefficients, 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31);
    }
    Ok(())
}

/// The signature's `s2`, compressed, into `s2`; returns its squared norm.
///
/// Per coefficient: a sign bit, the low 7 bits of its magnitude, then the high bits in unary.
///
/// ```text
///   -213 = -(1 * 128 + 85)     1 | 1010101 | 0 1
///   sign, low bits, one 0 per 128, a closing 1
/// ```
///
/// The body must be the canonical encoding of 512 coefficients in 625 bytes:
///
/// - each magnitude is at most 2047, and no zero is negative;
/// - every bit past the last coefficient is zero.
pub fn decompress(body: &[u64; BODY_WORDS], s2: &mut [i64; N]) -> Result<i64, FalconVerifyError> {
    const BITS: usize = 8 * BODY_BYTES;
    let invalid = Err(FalconVerifyError::InvalidEncoding);

    // The 64 bits from `pos`, of which a coefficient takes at most 24.
    //
    // The second shift is split in two, so that `pos % 64 = 0` shifts the next word out entirely.
    let window_at = |pos: usize| {
        let (i, rem) = (pos / 64, pos % 64);
        (body[i] << rem) | ((body[i + 1] >> 1) >> (63 - rem))
    };

    let (mut norm, mut pos) = (0, 0);
    let (mut window, mut left) = (window_at(0), 64);
    for x in s2.iter_mut() {
        // A new window once fewer than 24 bits are left: every 2 to 4 coefficients.
        if left < 24 {
            // Past the body's last bit, nothing is a coefficient.
            if pos > BITS {
                return invalid;
            }
            (window, left) = (window_at(pos), 64);
        }

        // Sign, low bits, then a zero per 128 until the closing one.
        let negative = window >> 63 == 1;
        let low = (window >> 56) & 0x7F;
        let mut unary = window << 8;
        let mut high = 0;
        while unary >> 63 == 0 {
            high += 1;
            // A magnitude past 2047 is not Falcon's.
            if high == 16 {
                return invalid;
            }
            unary <<= 1;
        }
        let magnitude = (low + 128 * high as u64) as i64;

        // Zero has one encoding.
        if negative && magnitude == 0 {
            return invalid;
        }
        *x = if negative { -magnitude } else { magnitude };
        norm += magnitude * magnitude;

        // The coefficient's 9 + high bits are consumed.
        (window, left, pos) = (unary << 1, left - 9 - high, pos + 9 + high);
    }

    // The last coefficient ends within the body, and the rest of it is zero.
    let (i, rem) = (pos / 64, pos % 64);
    let tail_is_zero = body[i] << rem == 0 && body[i + 1..].iter().all(|&w| w == 0);
    if pos <= BITS && tail_is_zero { Ok(norm) } else { invalid }
}
