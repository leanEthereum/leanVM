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

/// Variables of an instance's index within its pack.
pub const PACK_BITS: usize = 4;
/// Bits one embedding carries: the instances of a pack.
pub const PACK: usize = 1 << PACK_BITS;
/// Coefficients of an embedding: one more than the degree of the product of the moduli.
pub const EMBED_BITS: usize = 24;
/// Coefficients of a product of two embeddings.
pub const PROD_BITS: usize = 2 * EMBED_BITS - 1;

/// An embedding, coefficient `b` at bit `b`.
pub type Emb = u32;
/// A product of two embeddings, coefficient `c` at bit `c`.
pub type Prod = u64;

const _: () = assert!(EMBED_BITS <= Emb::BITS as usize && PROD_BITS <= Prod::BITS as usize);

/// The moduli, with the number of bits each one holds.
const FACTORS: [(Prod, usize); 7] = [
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
    pub emb: [Emb; PACK],
    /// `embed` of a low byte and of a high byte.
    pub(crate) emb_lo: [Emb; 256],
    pub(crate) emb_hi: [Emb; 256],
    /// Bit `i` of `project(p)` is the parity of `p & proj[i]`.
    pub proj: [Prod; PACK],
    /// `embed` of all ones.
    pub ones: Emb,
}

/// Built at compile time, so the kernels read it as constants.
pub static RMFE: Rmfe = Rmfe::build();

const fn deg(a: Prod) -> usize {
    (Prod::BITS - 1 - a.leading_zeros()) as usize
}

/// A carry-less product that fits in a word.
const fn pmul(a: Prod, b: Prod) -> Prod {
    let mut p = 0;
    let mut i = 0;
    while i < Prod::BITS {
        if b >> i & 1 == 1 {
            assert!(i == 0 || a >> (Prod::BITS - i) == 0);
            p ^= a << i;
        }
        i += 1;
    }
    p
}

const fn pdivmod(mut a: Prod, f: Prod) -> (Prod, Prod) {
    let mut q = 0;
    while a != 0 && deg(a) >= deg(f) {
        let s = deg(a) - deg(f);
        q |= 1 << s;
        a ^= f << s;
    }
    (q, a)
}

const fn pmod(a: Prod, f: Prod) -> Prod {
    pdivmod(a, f).1
}

/// The embedding of each value of the byte at bit `shift` of the input.
const fn byte_table(emb: &[Emb; PACK], shift: usize) -> [Emb; 256] {
    let mut table = [0; 256];
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

        let mut emb = [0; PACK];
        let mut proj = [0; PACK];
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
            let residues: &[Prod] = match bits {
                1 => &[1],
                2 => &[0b11, 0b10],
                _ => &[0b011, 0b010, 0b110],
            };
            let mut k = 0;
            while k < residues.len() {
                emb[bit + k] = pmod(pmul(pmod(lift, modulus), residues[k]), modulus) as Emb;
                k += 1;
            }
            // `g = X^c mod f`, stepped: a word cannot hold `X^c` itself for every `c`.
            let mut g: Prod = 1;
            let mut c = 0;
            while c < PROD_BITS {
                let at_one = g.count_ones() as Prod & 1;
                let values: [Prod; 3] = match bits {
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
                g = pmod(g << 1, f);
                c += 1;
            }
            bit += bits;
            i += 1;
        }
        // The last bit rides the leading coefficient, which the residues do not see.
        emb[PACK - 1] = modulus as Emb;
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

    /// The embedding of a pack's bits, bit `i` being instance `i`.
    #[inline(always)]
    pub fn embed(&self, a: u16) -> Emb {
        const { assert!(PACK == 16, "a pack's bits are a u16, two byte tables") };
        self.emb_lo[a as usize & 0xff] ^ self.emb_hi[a as usize >> 8]
    }

    #[cfg(test)]
    fn project(&self, product: Prod) -> u16 {
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
                let p = mul_wide(r.emb[i] as u64, r.emb[j] as u64) as Prod;
                assert_eq!(r.project(p), if i == j { 1 << i } else { 0 }, "{i} {j}");
            }
        }
        let mut rng = Rng::new(7);
        for _ in 0..1000 {
            let (a, b) = (rng.next_u64() as u16, rng.next_u64() as u16);
            let (ea, eb) = (r.embed(a), r.embed(b));
            assert!(ea < 1 << EMBED_BITS);
            let p = mul_wide(ea as u64, eb as u64) as Prod;
            assert!(p < 1 << PROD_BITS);
            assert_eq!(r.project(p), a & b);
        }
    }
}
