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

use std::sync::LazyLock;

use primitives::field::gf2_64::mul_wide;

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

pub static RMFE: LazyLock<Rmfe> = LazyLock::new(Rmfe::build);

fn deg(a: u64) -> usize {
    63 - a.leading_zeros() as usize
}

fn pmul(a: u64, b: u64) -> u64 {
    let p = mul_wide(a, b);
    assert_eq!(p >> 64, 0);
    p as u64
}

fn pdivmod(mut a: u64, f: u64) -> (u64, u64) {
    let mut q = 0;
    while a != 0 && deg(a) >= deg(f) {
        let s = deg(a) - deg(f);
        q |= 1 << s;
        a ^= f << s;
    }
    (q, a)
}

fn pmod(a: u64, f: u64) -> u64 {
    pdivmod(a, f).1
}

impl Rmfe {
    fn build() -> Self {
        let modulus = FACTORS.iter().fold(1, |p, &(f, _)| pmul(p, f));
        assert_eq!(deg(modulus), EMBED_BITS - 1);
        assert_eq!(FACTORS.iter().map(|f| f.1).sum::<usize>(), PACK - 1);

        let mut emb = [0u32; PACK];
        let mut proj = [0u64; PACK];
        let mut bit = 0;
        for &(f, bits) in &FACTORS {
            // The lift of a residue: 1 modulo `f`, 0 modulo the other factors.
            let (cofactor, rem) = pdivmod(modulus, f);
            assert_eq!(rem, 0);
            let inv = (1..1u64 << deg(f))
                .find(|&g| pmod(pmul(pmod(cofactor, f), g), f) == 1)
                .expect("coprime factors");
            let lift = pmul(cofactor, inv);
            // A residue is the polynomial taking the bits as its values at 0, 1 and infinity.
            let residues: &[u64] = match bits {
                1 => &[1],
                2 => &[0b11, 0b10],
                _ => &[0b011, 0b010, 0b110],
            };
            for (k, &r) in residues.iter().enumerate() {
                emb[bit + k] = pmod(pmul(pmod(lift, modulus), r), modulus) as u32;
            }
            for c in 0..PROD_BITS {
                let g = pmod(1 << c, f);
                let at_one = g.count_ones() as u64 & 1;
                let values: &[u64] = match bits {
                    1 if f == 0b10 => &[g & 1],
                    1 => &[at_one],
                    2 => &[g & 1, at_one],
                    _ => &[g & 1, at_one, g >> 4],
                };
                for (k, &v) in values.iter().enumerate() {
                    proj[bit + k] |= v << c;
                }
            }
            bit += bits;
        }
        // The last bit rides the leading coefficient, which the residues do not see.
        emb[PACK - 1] = modulus as u32;
        proj[PACK - 1] = 1 << (PROD_BITS - 1);

        let table = |shift: usize| {
            std::array::from_fn(|byte| (0..8).filter(|t| byte >> t & 1 == 1).fold(0, |e, t| e ^ emb[shift + t]))
        };
        let (emb_lo, emb_hi): ([u32; 256], [u32; 256]) = (table(0), table(8));
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
    use primitives::test_rng::Rng;

    #[test]
    fn product_of_embeddings_projects_to_and() {
        let r = &*RMFE;
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
