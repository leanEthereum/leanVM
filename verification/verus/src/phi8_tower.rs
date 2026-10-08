//! The embedding `φ₈: GF(2^8) → E`, whose image lies in `K`.
//!
//! The executable functions are `crates/primitives/src/field/phi8_tower.rs`, copied with the same bodies;
//! `tests/equivalence/phi8_tower.rs` checks the two agree.
//!
//! Specification: [`phi8`] is the GF(2)-linear map sending the byte `x^i` (bit `i`) to the production
//! constant `PHI_8_BASIS[i]` of `K` ([`phi8_basis`]), and `phi8_192(a)` is `φ₈(a)` embedded in `E`
//! ([`e_from_k`]). The theorems: `φ₈` is a ring homomorphism from `GF(2^8)` ([`f8_mul`]) into `K`
//! ([`k_mul`]) and into `E` ([`e_mul`]), sends one to one, and is injective, so its image is a subfield
//! of `K` with 256 elements.
//!
//! The proof: `φ₈` commutes with the multiplication by `x`, `φ₈(x a) = g φ₈(a)` with `g = φ₈(x)`
//! ([`lemma_phi8_mulx`]); by linearity this needs it only on the eight bytes `x^i`, eight products in `K`
//! of concrete constants, evaluated by [`clmul64_closed`]. Then `φ₈(x^i b) = φ₈(x^i) φ₈(b)` by induction
//! on `i`, and the general product by linearity in the left factor.
use crate::clmul::*;
use crate::gf2_64::*;
use crate::gf2_64x3::*;
use crate::gf2_8::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------------------------
/// `φ₈(x^i)` for `i < 8`: the production `PHI_8_BASIS[i]`.
pub open spec fn phi8_basis(i: u8) -> u64 {
    if i == 0 {
        0x0000000000000001u64
    } else if i == 1 {
        0x033ce8beddc8a656u64
    } else if i == 2 {
        0x512620375ed2a108u64
    } else if i == 3 {
        0x0c9e636090aafc01u64
    } else if i == 4 {
        0xba4f3cd82801769cu64
    } else if i == 5 {
        0xba26e7904adb4a47u64
    } else if i == 6 {
        0x467698598926dc01u64
    } else {
        0x4418ae808b28bdd0u64
    }
}

/// `[a_i] φ₈(x^i)`.
pub open spec fn phi8_term(a: u8, i: u8) -> u64 {
    if (a >> i) & 1 == 1 {
        phi8_basis(i)
    } else {
        0
    }
}

/// `φ₈` of the low `n` coefficients of `a`: the XOR of `φ₈(x^i)` over the set bits `i < n` of `a`.
pub open spec fn phi8_upto(a: u8, n: nat) -> u64
    decreases n,
{
    if n == 0 {
        0
    } else {
        phi8_upto(a, (n - 1) as nat) ^ phi8_term(a, (n - 1) as u8)
    }
}

/// `φ₈(a)`, in `K`.
pub open spec fn phi8(a: u8) -> u64 {
    phi8_upto(a, 8)
}

/// [`phi8`] as a bit-vector term.
pub open spec fn phi8_closed(a: u8) -> u64 {
    phi8_term(a, 0) ^ phi8_term(a, 1) ^ phi8_term(a, 2) ^ phi8_term(a, 3) ^ phi8_term(a, 4) ^ phi8_term(a, 5)
        ^ phi8_term(a, 6) ^ phi8_term(a, 7)
}

/// `φ₈(a)`, in `E`.
pub open spec fn phi8_e(a: u8) -> F192 {
    e_from_k(phi8(a))
}

// ---------------------------------------------------------------------------------------------
// Linearity
// ---------------------------------------------------------------------------------------------
pub proof fn lemma_phi8_closed(a: u8)
    ensures
        phi8(a) == phi8_closed(a),
{
    reveal_with_fuel(phi8_upto, 9);
    let t0 = phi8_term(a, 0);
    assert(0u64 ^ t0 == t0) by (bit_vector);
}

/// `φ₈` is GF(2)-linear: `φ₈(a + b) = φ₈(a) + φ₈(b)`.
pub proof fn lemma_phi8_xor(a: u8, b: u8)
    ensures
        phi8(a ^ b) == phi8(a) ^ phi8(b),
{
    lemma_phi8_closed(a);
    lemma_phi8_closed(b);
    lemma_phi8_closed(a ^ b);
    assert(phi8_closed(a ^ b) == phi8_closed(a) ^ phi8_closed(b)) by (bit_vector);
}

/// `φ₈(0) = 0` and `φ₈(1) = 1`.
pub proof fn lemma_phi8_zero_one()
    ensures
        phi8(0) == 0,
        phi8(1) == 1,
{
    lemma_phi8_closed(0);
    lemma_phi8_closed(1);
    assert(phi8_closed(0) == 0 && phi8_closed(1) == 1) by (bit_vector);
}

/// `φ₈` is injective: the eight basis images are GF(2)-independent.
pub proof fn lemma_phi8_injective(a: u8, b: u8)
    ensures
        phi8(a) == phi8(b) ==> a == b,
{
    lemma_phi8_closed(a);
    lemma_phi8_closed(b);
    assert(phi8_closed(a) == phi8_closed(b) ==> a == b) by (bit_vector);
}

/// `φ₈(a)` is zero only at zero.
pub proof fn lemma_phi8_nonzero(a: u8)
    requires
        a != 0,
    ensures
        phi8(a) != 0,
{
    lemma_phi8_injective(a, 0);
    lemma_phi8_zero_one();
}

/// `φ₈(x^i)` is the basis constant.
pub proof fn lemma_phi8_monomial(i: u8)
    requires
        i < 8,
    ensures
        phi8(1u8 << i) == phi8_basis(i),
{
    lemma_phi8_closed(1u8 << i);
    assert(i < 8 ==> phi8_closed(1u8 << i) == phi8_basis(i)) by (bit_vector);
}

// ---------------------------------------------------------------------------------------------
// Products of concrete elements of K
// ---------------------------------------------------------------------------------------------
/// `[a_i] * b * x^i`, with a machine-word index.
pub open spec fn term64(a: u64, b: u128, i: u64) -> u128 {
    if (a >> i) & 1 == 1 {
        b << (i as u128)
    } else {
        0
    }
}

/// The 64 partial products of [`clmul`], XORed: a bit-vector term.
pub open spec fn clmul64_closed(a: u64, b: u128) -> u128 {
    term64(a, b, 0) ^ term64(a, b, 1) ^ term64(a, b, 2) ^ term64(a, b, 3) ^ term64(a, b, 4) ^ term64(a, b, 5)
        ^ term64(a, b, 6) ^ term64(a, b, 7) ^ term64(a, b, 8) ^ term64(a, b, 9) ^ term64(a, b, 10)
        ^ term64(a, b, 11) ^ term64(a, b, 12) ^ term64(a, b, 13) ^ term64(a, b, 14) ^ term64(a, b, 15)
        ^ term64(a, b, 16) ^ term64(a, b, 17) ^ term64(a, b, 18) ^ term64(a, b, 19) ^ term64(a, b, 20)
        ^ term64(a, b, 21) ^ term64(a, b, 22) ^ term64(a, b, 23) ^ term64(a, b, 24) ^ term64(a, b, 25)
        ^ term64(a, b, 26) ^ term64(a, b, 27) ^ term64(a, b, 28) ^ term64(a, b, 29) ^ term64(a, b, 30)
        ^ term64(a, b, 31) ^ term64(a, b, 32) ^ term64(a, b, 33) ^ term64(a, b, 34) ^ term64(a, b, 35)
        ^ term64(a, b, 36) ^ term64(a, b, 37) ^ term64(a, b, 38) ^ term64(a, b, 39) ^ term64(a, b, 40)
        ^ term64(a, b, 41) ^ term64(a, b, 42) ^ term64(a, b, 43) ^ term64(a, b, 44) ^ term64(a, b, 45)
        ^ term64(a, b, 46) ^ term64(a, b, 47) ^ term64(a, b, 48) ^ term64(a, b, 49) ^ term64(a, b, 50)
        ^ term64(a, b, 51) ^ term64(a, b, 52) ^ term64(a, b, 53) ^ term64(a, b, 54) ^ term64(a, b, 55)
        ^ term64(a, b, 56) ^ term64(a, b, 57) ^ term64(a, b, 58) ^ term64(a, b, 59) ^ term64(a, b, 60)
        ^ term64(a, b, 61) ^ term64(a, b, 62) ^ term64(a, b, 63)
}

/// [`clmul`] is [`clmul64_closed`].
pub proof fn lemma_clmul64_closed(a: u64, b: u128)
    ensures
        clmul(a, b) == clmul64_closed(a, b),
{
    reveal_with_fuel(clmul_upto, 65);
    let t0 = term(a, b, 0);
    assert(0u128 ^ t0 == t0) by (bit_vector);
}

/// The product in `K` as a bit-vector term.
pub open spec fn k_mul_closed(a: u64, b: u64) -> u64 {
    reduce_formula(clmul64_closed(a, b as u128))
}

pub proof fn lemma_k_mul_closed(a: u64, b: u64)
    ensures
        k_mul(a, b) == k_mul_closed(a, b),
{
    lemma_clmul64_closed(a, b as u128);
    lemma_k_mod(clmul(a, b as u128));
}

// ---------------------------------------------------------------------------------------------
// φ₈ is multiplicative
// ---------------------------------------------------------------------------------------------
/// `g φ₈(x^i) = φ₈(x * x^i)` for the eight monomials, `g = φ₈(x)`: eight products of constants.
proof fn lemma_phi8_mulx_monomial(i: u8)
    requires
        i < 8,
    ensures
        k_mul(phi8_basis(1), phi8_basis(i)) == phi8(mulx8(1u8 << i)),
{
    lemma_k_mul_closed(phi8_basis(1), phi8_basis(i));
    lemma_phi8_closed(mulx8(1u8 << i));
    let g = phi8_basis(1);
    if i == 0 {
        assert(k_mul_closed(0x033ce8beddc8a656u64, 0x0000000000000001u64) == 0x033ce8beddc8a656u64)
            by (bit_vector);
        assert(phi8_closed(mulx8(1u8 << 0u8)) == 0x033ce8beddc8a656u64) by (bit_vector);
    } else if i == 1 {
        assert(k_mul_closed(0x033ce8beddc8a656u64, 0x033ce8beddc8a656u64) == 0x512620375ed2a108u64)
            by (bit_vector);
        assert(phi8_closed(mulx8(1u8 << 1u8)) == 0x512620375ed2a108u64) by (bit_vector);
    } else if i == 2 {
        assert(k_mul_closed(0x033ce8beddc8a656u64, 0x512620375ed2a108u64) == 0x0c9e636090aafc01u64)
            by (bit_vector);
        assert(phi8_closed(mulx8(1u8 << 2u8)) == 0x0c9e636090aafc01u64) by (bit_vector);
    } else if i == 3 {
        assert(k_mul_closed(0x033ce8beddc8a656u64, 0x0c9e636090aafc01u64) == 0xba4f3cd82801769cu64)
            by (bit_vector);
        assert(phi8_closed(mulx8(1u8 << 3u8)) == 0xba4f3cd82801769cu64) by (bit_vector);
    } else if i == 4 {
        assert(k_mul_closed(0x033ce8beddc8a656u64, 0xba4f3cd82801769cu64) == 0xba26e7904adb4a47u64)
            by (bit_vector);
        assert(phi8_closed(mulx8(1u8 << 4u8)) == 0xba26e7904adb4a47u64) by (bit_vector);
    } else if i == 5 {
        assert(k_mul_closed(0x033ce8beddc8a656u64, 0xba26e7904adb4a47u64) == 0x467698598926dc01u64)
            by (bit_vector);
        assert(phi8_closed(mulx8(1u8 << 5u8)) == 0x467698598926dc01u64) by (bit_vector);
    } else if i == 6 {
        assert(k_mul_closed(0x033ce8beddc8a656u64, 0x467698598926dc01u64) == 0x4418ae808b28bdd0u64)
            by (bit_vector);
        assert(phi8_closed(mulx8(1u8 << 6u8)) == 0x4418ae808b28bdd0u64) by (bit_vector);
    } else {
        // x^8 = x^4 + x^3 + x + 1.
        assert(k_mul_closed(0x033ce8beddc8a656u64, 0x4418ae808b28bdd0u64) == 0xb5edb70665632ccau64)
            by (bit_vector);
        assert(phi8_closed(mulx8(1u8 << 7u8)) == 0xb5edb70665632ccau64) by (bit_vector);
    }
}

/// `φ₈(x a) = g φ₈(a)` on the low `n` coefficients of `a`, by linearity from the monomials.
proof fn lemma_phi8_mulx_upto(a: u8, n: u16)
    requires
        n <= 8,
    ensures
        phi8(mulx8(low8(a, n))) == k_mul(phi8_basis(1), phi8(low8(a, n))),
    decreases n,
{
    let g = phi8_basis(1);
    if n == 0 {
        assert(((a as u16) & sub(1u16 << 0u16, 1)) as u8 == 0 && mulx8(0) == 0) by (bit_vector);
        lemma_phi8_zero_one();
        lemma_k_mul_zero(g);
    } else {
        let i = sub(n, 1);
        lemma_phi8_mulx_upto(a, i);
        let e: u8 = if (a >> (i as u8)) & 1 == 1 {
            1u8 << (i as u8)
        } else {
            0
        };
        let lo = low8(a, i);
        assert(i < 8 ==> ((a as u16) & sub(1u16 << add(i, 1), 1)) as u8 == ((a as u16) & sub(1u16 << i, 1)) as u8
            ^ (if (a >> (i as u8)) & 1 == 1 {
            1u8 << (i as u8)
        } else {
            0u8
        })) by (bit_vector);
        assert(low8(a, n) == lo ^ e);
        assert(mulx8(lo ^ e) == mulx8(lo) ^ mulx8(e)) by (bit_vector);
        lemma_phi8_xor(mulx8(lo), mulx8(e));
        lemma_phi8_xor(lo, e);
        lemma_k_mul_xor_right(g, phi8(lo), phi8(e));
        if (a >> (i as u8)) & 1 == 1 {
            lemma_phi8_mulx_monomial(i as u8);
            lemma_phi8_monomial(i as u8);
        } else {
            assert(mulx8(0) == 0) by (bit_vector);
            lemma_phi8_zero_one();
            lemma_k_mul_zero(g);
        }
    }
}

/// `φ₈` commutes with the multiplication by `x`: `φ₈(x a) = φ₈(x) φ₈(a)`.
pub proof fn lemma_phi8_mulx(a: u8)
    ensures
        phi8(mulx8(a)) == k_mul(phi8(2), phi8(a)),
{
    lemma_phi8_mulx_upto(a, 8);
    assert(((a as u16) & sub(1u16 << 8u16, 1)) as u8 == a) by (bit_vector);
    assert(2u8 == 1u8 << 1u8) by (bit_vector);
    lemma_phi8_monomial(1);
}

/// `φ₈(x^i b) = φ₈(x^i) φ₈(b)`.
proof fn lemma_phi8_mulx_pow(b: u8, i: u8)
    requires
        i < 8,
    ensures
        phi8(mulx8_pow(b, i as nat)) == k_mul(phi8(1u8 << i), phi8(b)),
    decreases i,
{
    if i == 0 {
        assert(1u8 << 0u8 == 1) by (bit_vector);
        lemma_phi8_zero_one();
        lemma_k_mul_one(phi8(b));
    } else {
        let j = (i - 1) as u8;
        lemma_phi8_mulx_pow(b, j);
        let m = mulx8_pow(b, j as nat);
        assert(mulx8_pow(b, i as nat) == mulx8(m));
        lemma_phi8_mulx(m);
        // g (φ₈(x^j) φ₈(b)) = (g φ₈(x^j)) φ₈(b) = φ₈(x^(j+1)) φ₈(b).
        lemma_k_mul_assoc(phi8(2), phi8(1u8 << j), phi8(b));
        lemma_phi8_mulx(1u8 << j);
        assert(j < 7 ==> mulx8(1u8 << j) == 1u8 << add(j, 1)) by (bit_vector);
    }
}

/// `φ₈(a b) = φ₈(a) φ₈(b)` on the low `n` coefficients of `a`.
proof fn lemma_phi8_mul_upto(a: u8, b: u8, n: u16)
    requires
        n <= 8,
    ensures
        phi8(f8_mul(low8(a, n), b)) == k_mul(phi8(low8(a, n)), phi8(b)),
    decreases n,
{
    if n == 0 {
        assert(((a as u16) & sub(1u16 << 0u16, 1)) as u8 == 0) by (bit_vector);
        lemma_f8_mul_zero(b);
        lemma_phi8_zero_one();
        lemma_k_mul_zero(phi8(b));
        lemma_k_mul_comm(0, phi8(b));
    } else {
        let i = sub(n, 1);
        lemma_phi8_mul_upto(a, b, i);
        let e: u8 = if (a >> (i as u8)) & 1 == 1 {
            1u8 << (i as u8)
        } else {
            0
        };
        let lo = low8(a, i);
        assert(i < 8 ==> ((a as u16) & sub(1u16 << add(i, 1), 1)) as u8 == ((a as u16) & sub(1u16 << i, 1)) as u8
            ^ (if (a >> (i as u8)) & 1 == 1 {
            1u8 << (i as u8)
        } else {
            0u8
        })) by (bit_vector);
        assert(low8(a, n) == lo ^ e);
        // (lo + e) b = lo b + e b, in both rings.
        lemma_f8_mul_comm(lo ^ e, b);
        lemma_f8_mul_xor_right(b, lo, e);
        lemma_f8_mul_comm(b, lo);
        lemma_f8_mul_comm(b, e);
        lemma_phi8_xor(f8_mul(lo, b), f8_mul(e, b));
        lemma_phi8_xor(lo, e);
        lemma_k_mul_xor_left(phi8(lo), phi8(e), phi8(b));
        if (a >> (i as u8)) & 1 == 1 {
            lemma_f8_mul_monomial(b, i as nat);
            lemma_phi8_mulx_pow(b, i as u8);
        } else {
            lemma_f8_mul_zero(b);
            lemma_phi8_zero_one();
            lemma_k_mul_zero(phi8(b));
            lemma_k_mul_comm(0, phi8(b));
        }
    }
}

/// `φ₈` is multiplicative into `K`: `φ₈(a b) = φ₈(a) φ₈(b)`.
pub proof fn lemma_phi8_mul(a: u8, b: u8)
    ensures
        phi8(f8_mul(a, b)) == k_mul(phi8(a), phi8(b)),
{
    lemma_phi8_mul_upto(a, b, 8);
    assert(((a as u16) & sub(1u16 << 8u16, 1)) as u8 == a) by (bit_vector);
}

/// `φ₈` is a ring homomorphism from `GF(2^8)` into `E`, injective, with image in `K`.
pub proof fn lemma_phi8_e_homomorphism(a: u8, b: u8)
    ensures
        phi8_e(f8_mul(a, b)) == e_mul(phi8_e(a), phi8_e(b)),
        phi8_e(a ^ b) == e_add(phi8_e(a), phi8_e(b)),
        phi8_e(1) == F192::ONE,
        phi8_e(0) == F192::ZERO,
        phi8_e(a) == phi8_e(b) ==> a == b,
        phi8_e(a).c1 == 0 && phi8_e(a).c2 == 0,
{
    lemma_phi8_mul(a, b);
    lemma_e_from_k_mul(phi8(a), phi8(b));
    lemma_phi8_xor(a, b);
    assert(0u64 ^ 0u64 == 0u64) by (bit_vector);
    lemma_phi8_zero_one();
    lemma_phi8_injective(a, b);
}

// ---------------------------------------------------------------------------------------------
// Executable code: `crates/primitives/src/field/phi8_tower.rs`
// ---------------------------------------------------------------------------------------------
/// φ₈(2ᵏ) for k ∈ [0,8): the images of the GF(2⁸) polynomial basis. All in
/// `F64` (`c1 == c2 == 0`).
const PHI_8_BASIS: [u64; 8] = [
    0x0000000000000001,
    0x033ce8beddc8a656,
    0x512620375ed2a108,
    0x0c9e636090aafc01,
    0xba4f3cd82801769c,
    0xba26e7904adb4a47,
    0x467698598926dc01,
    0x4418ae808b28bdd0,
];

const fn build_phi8_table_192() -> (table: [F192; 256])
    ensures
        forall|v: int| 0 <= v < 256 ==> #[trigger] table[v] == phi8_e(v as u8),
{
    let mut table = [F192::ZERO; 256];
    let mut value = 1;
    assert(table[0] == phi8_e(0)) by {
        lemma_phi8_zero_one();
    }
    while value < table.len()
        invariant
            1 <= value <= 256,
            forall|v: int| 0 <= v < value ==> #[trigger] table[v] == phi8_e(v as u8),
        decreases 256 - value,
    {
        let mut c0 = 0u64;
        let mut bit = 0;
        while bit < PHI_8_BASIS.len()
            invariant
                1 <= value < 256,
                bit <= 8,
                c0 == phi8_upto(value as u8, bit as nat),
            decreases 8 - bit,
        {
            assert(PHI_8_BASIS[bit as int] == phi8_basis(bit as u8));
            assert(value < 256 && bit < 8 ==> ((value & (1usize << bit) != 0) == ((value as u8 >> bit as u8) & 1
                == 1))) by (bit_vector);
            if value & (1 << bit) != 0 {
                c0 ^= PHI_8_BASIS[bit];
            } else {
                assert(c0 ^ 0 == c0) by (bit_vector);
            }
            bit += 1;
        }
        table[value] = F192::new(c0, 0, 0);
        value += 1;
    }
    table
}

/// The unique GF(2^8) subfield embedded in F192. It lies in the F64 base, so
/// both higher extension coordinates are zero.
///
/// Production's `static` with the initializer `build_phi8_table_192()`, written as Verus's `exec static` with
/// that initializer as its body so that its value has a specification.
pub exec static PHI_8_TABLE_192: [F192; 256]
    ensures
        forall|v: int| 0 <= v < 256 ==> #[trigger] PHI_8_TABLE_192[v] == phi8_e(v as u8),
{
    build_phi8_table_192()
}

#[inline]
pub fn phi8_192(a: F8) -> (r: F192)
    ensures
        r == phi8_e(a.0),
{
    PHI_8_TABLE_192[a.0 as usize]
}

} // verus!
