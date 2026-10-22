//! The reverse multiplication-friendly embedding the protocol packs sixteen instances with.
//!
//! `embed` sends sixteen bits to a binary polynomial of degree at most 23, and `project` sends a
//! product of two embeddings back to the bitwise AND of what they embed:
//!
//! ```text
//!     project(embed(a) * embed(b)) = a & b
//! ```
//!
//! The polynomial is glued by the Chinese remainder theorem from seven small fields, each
//! holding a few bits as the values of a low-degree polynomial at `0`, `1` and `infinity`, plus
//! one bit carried by the leading coefficient.

/// Bits one embedding carries.
pub const PACK: usize = 16;
/// Coefficients of an embedding.
pub const EMBED_BITS: usize = 24;
/// Coefficients of a product of two embeddings.
pub const PROD_BITS: usize = 2 * EMBED_BITS - 1;

/// The moduli, with the number of bits each one holds.
const FACTORS: [(u64, usize); 7] = [
    (0b10, 1),
    (0b11, 1),
    (0b1011, 2),
    (0b1101, 2),
    (0b100101, 3),
    (0b101001, 3),
    (0b101111, 3),
];

pub struct Rmfe {
    /// `embed` of each unit vector.
    pub emb: [u32; PACK],
    /// `embed` of a low byte and of a high byte.
    pub emb_lo: [u32; 256],
    pub emb_hi: [u32; 256],
    /// Bit `i` of `project(p)` is the parity of `p & proj[i]`.
    pub proj: [u64; PACK],
    /// `embed` of all ones.
    pub ones: u32,
}

/// Built at compile time, so the kernels read it as constants.
pub static RMFE: Rmfe = Rmfe::build();

const fn deg(a: u64) -> usize {
    63 - a.leading_zeros() as usize
}

/// A carry-less product that fits in a word.
const fn pmul(a: u64, b: u64) -> u64 {
    let mut p = 0;
    let mut i = 0;
    while i < 64 {
        if b >> i & 1 == 1 {
            assert!(i == 0 || a >> (64 - i) == 0);
            p ^= a << i;
        }
        i += 1;
    }
    p
}

const fn pdivmod(mut a: u64, f: u64) -> (u64, u64) {
    let mut q = 0;
    while a != 0 && deg(a) >= deg(f) {
        let s = deg(a) - deg(f);
        q |= 1 << s;
        a ^= f << s;
    }
    (q, a)
}

const fn pmod(a: u64, f: u64) -> u64 {
    pdivmod(a, f).1
}

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
        let mut modulus = 1;
        let mut held = 0;
        let mut f = 0;
        while f < FACTORS.len() {
            modulus = pmul(modulus, FACTORS[f].0);
            held += FACTORS[f].1;
            f += 1;
        }
        assert!(deg(modulus) == EMBED_BITS - 1);
        assert!(held == PACK - 1);

        let mut emb = [0u32; PACK];
        let mut proj = [0u64; PACK];
        let mut bit = 0;
        let mut i = 0;
        while i < FACTORS.len() {
            let (f, bits) = FACTORS[i];
            // The lift of a residue: 1 modulo `f`, 0 modulo the other factors.
            let (cofactor, rem) = pdivmod(modulus, f);
            assert!(rem == 0);
            let mut inv = 1;
            while pmod(pmul(pmod(cofactor, f), inv), f) != 1 {
                inv += 1;
                assert!(inv < 1 << deg(f), "coprime factors");
            }
            let lift = pmul(cofactor, inv);
            // A residue is the polynomial taking the bits as its values at 0, 1 and infinity.
            let residues: &[u64] = match bits {
                1 => &[1],
                2 => &[0b11, 0b10],
                _ => &[0b011, 0b010, 0b110],
            };
            let mut k = 0;
            while k < residues.len() {
                emb[bit + k] = pmod(pmul(pmod(lift, modulus), residues[k]), modulus) as u32;
                k += 1;
            }
            let mut c = 0;
            while c < PROD_BITS {
                let g = pmod(1 << c, f);
                let at_one = g.count_ones() as u64 & 1;
                let values: [u64; 3] = match bits {
                    1 if f == 0b10 => [g & 1, 0, 0],
                    1 => [at_one, 0, 0],
                    2 => [g & 1, at_one, 0],
                    _ => [g & 1, at_one, g >> 4],
                };
                let mut k = 0;
                while k < bits {
                    proj[bit + k] |= values[k] << c;
                    k += 1;
                }
                c += 1;
            }
            bit += bits;
            i += 1;
        }
        // The last bit rides the leading coefficient, which the residues do not see.
        emb[PACK - 1] = modulus as u32;
        proj[PACK - 1] = 1 << (PROD_BITS - 1);

        let (emb_lo, emb_hi) = (byte_table(&emb, 0), byte_table(&emb, 8));
        Self {
            emb,
            emb_lo,
            emb_hi,
            proj,
            ones: emb_lo[255] ^ emb_hi[255],
        }
    }

    #[inline(always)]
    pub fn embed(&self, a: u16) -> u32 {
        self.emb_lo[a as usize & 0xff] ^ self.emb_hi[a as usize >> 8]
    }

    #[cfg(test)]
    fn project(&self, product: u64) -> u16 {
        (0..PACK).fold(0, |a, i| a | (((product & self.proj[i]).count_ones() as u16 & 1) << i))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::field::gf2_64::mul_wide;
    use primitives::test_rng::Rng;

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
            assert!(p < 1 << PROD_BITS);
            assert_eq!(r.project(p), a & b);
        }
    }
}
