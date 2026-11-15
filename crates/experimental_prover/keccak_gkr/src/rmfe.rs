//! The reverse multiplication-friendly embedding the protocol packs sixteen instances with, the verifier's
//! ([`verifier::keccak::RMFE_EMBED`], [`verifier::keccak::RMFE_PROJECT`]), with the byte tables the kernels embed
//! through.
//!
//! `embed` sends sixteen bits to a binary polynomial of degree at most 23, and `project` sends a
//! product of two embeddings back to the bitwise AND of what they embed:
//!
//! ```text
//!     project(embed(a) * embed(b)) = a & b
//! ```

use verifier::keccak::{PACK, RMFE_EMBED};

pub struct Rmfe {
    /// `embed` of each unit vector.
    pub emb: [u32; PACK],
    /// `embed` of a low byte and of a high byte.
    pub(crate) emb_lo: [u32; 256],
    pub(crate) emb_hi: [u32; 256],
    /// `embed` of all ones.
    pub ones: u32,
}

/// Built at compile time, so the kernels read it as constants.
pub static RMFE: Rmfe = Rmfe::build();

/// The embedding of each value of the byte at bit `shift` of the input.
const fn byte_table(emb: &[u32; PACK], shift: usize) -> [u32; 256] {
    let mut table = [0u32; 256];
    let mut byte = 0;
    while byte < 256 {
        let mut t = 0;
        while t < 8 {
            if byte >> t & 1 == 1 {
                table[byte] ^= emb[shift + t];
            }
            t += 1;
        }
        byte += 1;
    }
    table
}

impl Rmfe {
    const fn build() -> Self {
        let emb = RMFE_EMBED;
        let (emb_lo, emb_hi) = (byte_table(&emb, 0), byte_table(&emb, 8));
        Self {
            emb,
            emb_lo,
            emb_hi,
            ones: emb_lo[255] ^ emb_hi[255],
        }
    }

    #[inline(always)]
    pub fn embed(&self, a: u16) -> u32 {
        self.emb_lo[a as usize & 0xff] ^ self.emb_hi[a as usize >> 8]
    }

    #[cfg(test)]
    fn project(&self, product: u64) -> u16 {
        (0..PACK).fold(0, |a, i| {
            a | (((product & verifier::keccak::RMFE_PROJECT[i]).count_ones() as u16 & 1) << i)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::field::gf2_64::mul_wide;
    use primitives::test_rng::Rng;
    use verifier::keccak::{EMBED_BITS, PRODUCT_BITS};

    #[test]
    fn product_of_embeddings_projects_to_and() {
        let r = &RMFE;
        // Bilinear, so the unit vectors decide it.
        for i in 0..PACK {
            for j in 0..PACK {
                let p = mul_wide(r.emb[i] as u64, r.emb[j] as u64) as u64;
                assert_eq!(r.project(p), if i == j { 1 << i } else { 0 }, "{i} {j}");
            }
        }
        let mut rng = Rng::new(7);
        for _ in 0..1000 {
            let (a, b) = (rng.next_u64() as u16, rng.next_u64() as u16);
            let (ea, eb) = (r.embed(a), r.embed(b));
            assert!(ea < 1 << EMBED_BITS);
            let p = mul_wide(ea as u64, eb as u64) as u64;
            assert!(p < 1 << PRODUCT_BITS);
            assert_eq!(r.project(p), a & b);
        }
    }
}
