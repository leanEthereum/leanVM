//! Bit transposes.
//!
//! The executable functions are copies of `crates/primitives/src/bits.rs`: the portable paths and the SIMD arms
//! of `bit_transpose_64bytes` (AVX-512 VBMI with GFNI, AVX2 with GFNI, AVX2, NEON), each under production's
//! `cfg`, so every build Verus checks proves the arms it compiles. `tests/equivalence/bits.rs` checks the copies
//! agree with production. Where Verus rejects the production form (`step_by`, const-generic inner functions,
//! `as_chunks_mut`, `array::from_fn`, `from_le_bytes`, `array::map`, function-local `const` items, loads and
//! stores through raw pointers), the copy spells out the same arithmetic in `while`/`for` loops or calls a
//! helper of `crate::intrinsics`; each such spot says what it replaces.
//!
//! Specification: a word is a row of bits, bit `i` of `x` being `(x >> i) & 1` ([`bit64`], [`bit8`]). Every
//! transpose is stated bit by bit: which input bit lands at which output bit. The arms of the 64-byte transpose
//! all prove [`is_bit_transpose_64bytes`], given the intrinsic specifications of `crate::intrinsics`.
#[cfg(all(target_arch = "aarch64", verus_keep_ghost))]
use crate::intrinsics::aarch64::*;
#[cfg(all(target_arch = "aarch64", verus_keep_ghost))]
use crate::intrinsics::aarch64_bits::*;
#[cfg(target_arch = "aarch64")]
use crate::intrinsics::aarch64_bits::{vld1q_u8_16, vld1q_u8_at, vst1q_u8_at};
#[cfg(all(target_arch = "x86_64", verus_keep_ghost))]
use crate::intrinsics::x86::*;
#[cfg(all(target_arch = "x86_64", verus_keep_ghost))]
use crate::intrinsics::x86_bits::*;
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
use crate::intrinsics::x86_bits::{load128_bytes, load256_bytes_at, store256_bytes_at};
#[cfg(all(target_arch = "x86_64", target_feature = "avx512vbmi", target_feature = "gfni"))]
use crate::intrinsics::x86_bits::{load512_bytes, store512_bytes};
#[cfg(target_arch = "aarch64")]
use core::arch::aarch64::*;
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
use core::arch::x86_64::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------------------------
/// Bit `i` of a 64-bit word.
pub open spec fn bit64(x: u64, i: int) -> bool {
    (x >> (i as u64)) & 1 == 1
}

/// Bit `i` of a byte.
pub open spec fn bit8(x: u8, i: int) -> bool {
    (x >> (i as u8)) & 1 == 1
}

/// `after` is the transpose of the 64x64 bit matrix `before`, word `r` being row `r`.
pub open spec fn is_transpose_64x64(before: [u64; 64], after: [u64; 64]) -> bool {
    forall|r: int, c: int| 0 <= r < 64 && 0 <= c < 64 ==> #[trigger] bit64(after[c], r) == bit64(before[r], c)
}

/// Two words agreeing on bits `0..n` agree on their low `n` bits.
proof fn lemma_bit64_ext_upto(x: u64, y: u64, n: u64)
    requires
        n <= 64,
        forall|i: int| 0 <= i < 64 ==> #[trigger] bit64(x, i) == bit64(y, i),
    ensures
        n < 64 ==> x & sub(1u64 << n, 1) == y & sub(1u64 << n, 1),
        n == 64 ==> x == y,
    decreases n,
{
    if n == 0 {
        assert(x & sub(1u64 << 0u64, 1) == y & sub(1u64 << 0u64, 1)) by (bit_vector);
    } else {
        let m = sub(n, 1);
        lemma_bit64_ext_upto(x, y, m);
        assert(bit64(x, m as int) == bit64(y, m as int));
        assert(m < 64 && x & sub(1u64 << m, 1) == y & sub(1u64 << m, 1) && (((x >> m) & 1 == 1) == ((y >> m) & 1
            == 1)) ==> (add(m, 1) < 64 ==> x & sub(1u64 << add(m, 1), 1) == y & sub(1u64 << add(m, 1), 1)) && (
        add(m, 1) == 64 ==> x == y)) by (bit_vector);
    }
}

/// Two words with the same 64 bits are equal.
pub proof fn lemma_bit64_ext(x: u64, y: u64)
    requires
        forall|i: int| 0 <= i < 64 ==> #[trigger] bit64(x, i) == bit64(y, i),
    ensures
        x == y,
{
    lemma_bit64_ext_upto(x, y, 64);
}

// ---------------------------------------------------------------------------------------------
// The 8x8 transpose
// ---------------------------------------------------------------------------------------------
/// The production `transpose_8x8_bits`, as a spec function.
pub open spec fn transpose_8x8_formula(x: u64) -> u64 {
    let t = (x ^ (x >> 7u64)) & 0x00AA_00AA_00AA_00AAu64;
    let x1 = x ^ (t ^ (t << 7u64));
    let t = (x1 ^ (x1 >> 14u64)) & 0x0000_CCCC_0000_CCCCu64;
    let x2 = x1 ^ (t ^ (t << 14u64));
    let t = (x2 ^ (x2 >> 28u64)) & 0x0000_0000_F0F0_F0F0u64;
    x2 ^ t ^ (t << 28u64)
}

/// Bit `r * 8 + c` of the 8x8 transpose is bit `c * 8 + r` of its input.
pub proof fn lemma_transpose_8x8_bit(x: u64, r: u64, c: u64)
    by (bit_vector)
    requires
        r < 8,
        c < 8,
    ensures
        ((transpose_8x8_formula(x) >> add(mul(r, 8), c)) & 1 == 1) == ((x >> add(mul(c, 8), r)) & 1 == 1),
{
}

/// The 8x8 transpose is an involution.
pub proof fn lemma_transpose_8x8_involution(x: u64)
    ensures
        transpose_8x8_formula(transpose_8x8_formula(x)) == x,
{
    assert(transpose_8x8_formula(transpose_8x8_formula(x)) == x) by (bit_vector);
}

// ---------------------------------------------------------------------------------------------
// The 64x64 transpose: one round
// ---------------------------------------------------------------------------------------------
/// The (distance, mask) pairs of the six rounds: the mask keeps the columns whose bit `j` is clear.
pub open spec fn is_round(j: u64, mask: u64) -> bool {
    ||| j == 32 && mask == 0x0000_0000_FFFF_FFFFu64
    ||| j == 16 && mask == 0x0000_FFFF_0000_FFFFu64
    ||| j == 8 && mask == 0x00FF_00FF_00FF_00FFu64
    ||| j == 4 && mask == 0x0F0F_0F0F_0F0F_0F0Fu64
    ||| j == 2 && mask == 0x3333_3333_3333_3333u64
    ||| j == 1 && mask == 0x5555_5555_5555_5555u64
}

/// `base` is a multiple of `2j`.
pub open spec fn aligned(base: u64, j: u64) -> bool {
    base & sub(add(j, j), 1) == 0
}

/// The row/column bits from `j` up: the bits a transpose has exchanged after the rounds `32, ..., j`.
pub open spec fn high_bits(j: u64) -> u64 {
    63u64 & !sub(j, 1)
}

/// What one round writes to word `r`: the masked swap of the pair `(r & !j, r | j)` it belongs to.
pub open spec fn round_word(m0: [u64; 64], r: u64, j: u64, mask: u64) -> u64 {
    let (lo, hi) = (r & !j, (r & !j) | j);
    let t = ((m0[lo as int] >> j) ^ m0[hi as int]) & mask;
    if r & j == 0 {
        m0[r as int] ^ (t << j)
    } else {
        m0[r as int] ^ t
    }
}

/// One masked swap, bit by bit: the low word takes the high word's bits of the columns with bit `j` set,
/// shifted down by `j`, and the high word the low word's bits of the columns with bit `j` clear, shifted up.
proof fn lemma_round_pair(a: u64, b: u64, j: u64, mask: u64, c: u64)
    by (bit_vector)
    requires
        is_round(j, mask),
        c < 64,
    ensures
        ({
            let t = ((a >> j) ^ b) & mask;
            &&& ((((a ^ (t << j)) >> c) & 1 == 1) == if c & j != 0 {
                (b >> (c ^ j)) & 1 == 1
            } else {
                (a >> c) & 1 == 1
            })
            &&& ((((b ^ t) >> c) & 1 == 1) == if c & j == 0 {
                (a >> (c ^ j)) & 1 == 1
            } else {
                (b >> c) & 1 == 1
            })
        }),
{
}

/// Index facts of [`round_word`], by bit-vector reasoning.
proof fn lemma_round_index(r: u64, c: u64, j: u64, mask: u64)
    by (bit_vector)
    requires
        is_round(j, mask),
        r < 64,
        c < 64,
    ensures
        ({
            let (lo, hi, s) = (r & !j, (r & !j) | j, (r ^ c) & j);
            &&& lo < 64 && hi < 64 && r ^ s < 64 && c ^ s < 64 && c ^ j < 64
            &&& r & j == 0 ==> lo == r && (if c & j != 0 {
                r ^ s == hi && c ^ s == c ^ j
            } else {
                r ^ s == r && c ^ s == c
            })
            &&& r & j != 0 ==> hi == r && (if c & j == 0 {
                r ^ s == lo && c ^ s == c ^ j
            } else {
                r ^ s == r && c ^ s == c
            })
        }),
{
}

/// [`round_word`] bit by bit: the round moves bit `(r ^ s, c ^ s)` to `(r, c)`, with `s = j` exactly when bit
/// `j` of the row and the column differ.
proof fn lemma_round_word_bit(m0: [u64; 64], r: u64, c: u64, j: u64, mask: u64)
    requires
        is_round(j, mask),
        r < 64,
        c < 64,
    ensures
        bit64(round_word(m0, r, j, mask), c as int) == bit64(
            m0[(r ^ ((r ^ c) & j)) as int],
            (c ^ ((r ^ c) & j)) as int,
        ),
{
    lemma_round_index(r, c, j, mask);
    let (lo, hi) = (r & !j, (r & !j) | j);
    lemma_round_pair(m0[lo as int], m0[hi as int], j, mask, c);
}

/// The first block is aligned, and a low half never exceeds its row.
proof fn lemma_round_start(j: u64, mask: u64, r: u64)
    by (bit_vector)
    requires
        is_round(j, mask),
    ensures
        aligned(0, j),
        r & !j <= r,
{
}

/// Index facts of the round's loops, by bit-vector reasoning.
proof fn lemma_round_loop(j: u64, mask: u64, base: u64, k: u64, r: u64)
    by (bit_vector)
    requires
        is_round(j, mask),
        aligned(base, j),
        base < 64,
    ensures
        aligned(add(base, add(j, j)), j),
        add(base, add(j, j)) <= 64,
        // Within a block, the low half has bit `j` clear and its partner is `k + j`.
        base <= k < add(base, j) ==> {
            &&& k < 64 && k & j == 0 && add(k, j) < 64 && add(k, j) & j != 0
            &&& k & !j == k && add(k, j) & !j == k && (k & !j) | j == add(k, j)
        },
        base <= k < add(base, j) ==> ((r & !j) < add(k, 1) <==> ((r & !j) < k || r == k || r == add(k, j))),
        // No low half lies in the block's upper half.
        (r & !j) < add(base, j) <==> (r & !j) < add(base, add(j, j)),
{
}

/// One round of [`transpose_64x64`]: for every block, swap the `j x j` blocks above and below the diagonal.
///
/// The production's `for base in (0..64).step_by(2 * J)` is the `while` loop over `base` below; the
/// production nests this function inside `transpose_64x64`.
#[inline(always)]
fn round<const J: usize>(m: &mut [u64; 64], mask: u64)
    requires
        is_round(J as u64, mask),
    ensures
        forall|r: int, c: int|
            0 <= r < 64 && 0 <= c < 64 ==> #[trigger] bit64(final(m)[r], c) == bit64(
                old(m)[(r as u64 ^ ((r as u64 ^ c as u64) & J as u64)) as int],
                (c as u64 ^ ((r as u64 ^ c as u64) & J as u64)) as int,
            ),
{
    let ghost m0 = *m;
    let ghost j = J as u64;
    proof {
        lemma_round_start(j, mask, 0);
    }
    let mut base: usize = 0;
    while base < 64
        invariant
            is_round(j, mask),
            j == J as u64,
            base <= 64,
            base < 64 ==> aligned(base as u64, j),
            forall|r: int|
                0 <= r < 64 ==> #[trigger] m[r] == if (r as u64 & !j) < base as u64 {
                    round_word(m0, r as u64, j, mask)
                } else {
                    m0[r]
                },
        decreases 64 - base,
    {
        for k in base..base + J
            invariant
                is_round(j, mask),
                j == J as u64,
                base < 64,
                aligned(base as u64, j),
                forall|r: int|
                    0 <= r < 64 ==> #[trigger] m[r] == if (r as u64 & !j) < k as u64 {
                        round_word(m0, r as u64, j, mask)
                    } else {
                        m0[r]
                    },
        {
            proof {
                lemma_round_loop(j, mask, base as u64, k as u64, k as u64);
                assert(m[k as int] == m0[k as int] && m[(k + J) as int] == m0[(k + J) as int]);
            }
            let ghost m1 = *m;
            let t = ((m[k] >> J) ^ m[k + J]) & mask;
            m[k] ^= t << J;
            m[k + J] ^= t;
            assert(m[k as int] == round_word(m0, k as u64, j, mask));
            assert(m[(k + J) as int] == round_word(m0, (k + J) as u64, j, mask));
            proof {
                assert forall|r: int| 0 <= r < 64 implies #[trigger] m[r] == if (r as u64 & !j) < (k + 1) as u64 {
                    round_word(m0, r as u64, j, mask)
                } else {
                    m0[r]
                } by {
                    lemma_round_loop(j, mask, base as u64, k as u64, r as u64);
                    assert(m1[r] == if (r as u64 & !j) < k as u64 {
                        round_word(m0, r as u64, j, mask)
                    } else {
                        m0[r]
                    });
                }
            }
        }
        proof {
            assert forall|r: int| 0 <= r < 64 implies #[trigger] m[r] == if (r as u64 & !j) < (base + 2 * J) as u64 {
                round_word(m0, r as u64, j, mask)
            } else {
                m0[r]
            } by {
                lemma_round_loop(j, mask, base as u64, 0, r as u64);
            }
            lemma_round_loop(j, mask, base as u64, 0, 0);
        }
        base += 2 * J;
    }
    proof {
        assert forall|r: int, c: int| 0 <= r < 64 && 0 <= c < 64 implies #[trigger] bit64(m[r], c) == bit64(
            m0[(r as u64 ^ ((r as u64 ^ c as u64) & j)) as int],
            (c as u64 ^ ((r as u64 ^ c as u64) & j)) as int,
        ) by {
            lemma_round_start(j, mask, r as u64);
            assert(m[r] == round_word(m0, r as u64, j, mask));
            lemma_round_word_bit(m0, r as u64, c as u64, j, mask);
        }
    }
}

// ---------------------------------------------------------------------------------------------
// The 64x64 transpose: the six rounds
// ---------------------------------------------------------------------------------------------
/// After the rounds `32, ..., j`, bit `(r, c)` came from the position whose row and column bits from `j` up are
/// exchanged.
pub open spec fn stage(m0: [u64; 64], m: [u64; 64], j: u64) -> bool {
    forall|r: int, c: int|
        0 <= r < 64 && 0 <= c < 64 ==> #[trigger] bit64(m[r], c) == bit64(
            m0[(r as u64 ^ ((r as u64 ^ c as u64) & high_bits(j))) as int],
            (c as u64 ^ ((r as u64 ^ c as u64) & high_bits(j))) as int,
        )
}

/// Composing round `j` with the rounds before it exchanges bit `j` too.
proof fn lemma_stage_index(r: u64, c: u64, j: u64, mask: u64)
    by (bit_vector)
    requires
        is_round(j, mask),
        r < 64,
        c < 64,
    ensures
        ({
            let s = (r ^ c) & j;
            let (r1, c1) = (r ^ s, c ^ s);
            let d1 = (r1 ^ c1) & high_bits(add(j, j));
            let d = (r ^ c) & high_bits(j);
            &&& r1 < 64 && c1 < 64 && r ^ d < 64 && c ^ d < 64
            &&& r1 ^ d1 == r ^ d && c1 ^ d1 == c ^ d
        }),
{
}

proof fn lemma_stage_step(m0: [u64; 64], m1: [u64; 64], m2: [u64; 64], j: u64, mask: u64)
    requires
        is_round(j, mask),
        stage(m0, m1, add(j, j)),
        forall|r: int, c: int|
            0 <= r < 64 && 0 <= c < 64 ==> #[trigger] bit64(m2[r], c) == bit64(
                m1[(r as u64 ^ ((r as u64 ^ c as u64) & j)) as int],
                (c as u64 ^ ((r as u64 ^ c as u64) & j)) as int,
            ),
    ensures
        stage(m0, m2, j),
{
    assert forall|r: int, c: int| 0 <= r < 64 && 0 <= c < 64 implies #[trigger] bit64(m2[r], c) == bit64(
        m0[(r as u64 ^ ((r as u64 ^ c as u64) & high_bits(j))) as int],
        (c as u64 ^ ((r as u64 ^ c as u64) & high_bits(j))) as int,
    ) by {
        lemma_stage_index(r as u64, c as u64, j, mask);
        let s = (r as u64 ^ c as u64) & j;
        let (r1, c1) = ((r as u64 ^ s) as int, (c as u64 ^ s) as int);
        assert(bit64(m1[r1], c1) == bit64(
            m0[(r1 as u64 ^ ((r1 as u64 ^ c1 as u64) & high_bits(add(j, j)))) as int],
            (c1 as u64 ^ ((r1 as u64 ^ c1 as u64) & high_bits(add(j, j)))) as int,
        ));
    }
}

/// Transpose the 64x64 bit matrix whose word `r` is row `r`, in place.
///
/// ```text
///     after: m[c] bit r  =  before: m[r] bit c
/// ```
///
/// Six rounds of masked swaps (Hacker's Delight, section 7-3), halving the block each round.
/// Round `j` swaps the upper-right and lower-left `j x j` blocks of every `2j x 2j` block on the diagonal.
/// The rounds with `j >= 8` pair whole runs of words, which the compiler vectorizes.
#[inline]
pub fn transpose_64x64(m: &mut [u64; 64])
    ensures
        is_transpose_64x64(*old(m), *final(m)),
{
    let ghost m0 = *m;
    proof {
        assert forall|r: int, c: int| 0 <= r < 64 && 0 <= c < 64 implies #[trigger] bit64(m0[r], c) == bit64(
            m0[(r as u64 ^ ((r as u64 ^ c as u64) & high_bits(64))) as int],
            (c as u64 ^ ((r as u64 ^ c as u64) & high_bits(64))) as int,
        ) by {
            let (r, c) = (r as u64, c as u64);
            assert(r < 64 && c < 64 ==> r ^ ((r ^ c) & high_bits(64)) == r && c ^ ((r ^ c) & high_bits(64)) == c)
                by (bit_vector);
        }
    }
    let ghost m1 = *m;
    round::<32>(m, 0x0000_0000_FFFF_FFFF);
    proof {
        lemma_stage_step(m0, m1, *m, 32, 0x0000_0000_FFFF_FFFF);
    }
    let ghost m1 = *m;
    round::<16>(m, 0x0000_FFFF_0000_FFFF);
    proof {
        lemma_stage_step(m0, m1, *m, 16, 0x0000_FFFF_0000_FFFF);
    }
    let ghost m1 = *m;
    round::<8>(m, 0x00FF_00FF_00FF_00FF);
    proof {
        lemma_stage_step(m0, m1, *m, 8, 0x00FF_00FF_00FF_00FF);
    }
    let ghost m1 = *m;
    round::<4>(m, 0x0F0F_0F0F_0F0F_0F0F);
    proof {
        lemma_stage_step(m0, m1, *m, 4, 0x0F0F_0F0F_0F0F_0F0F);
    }
    let ghost m1 = *m;
    round::<2>(m, 0x3333_3333_3333_3333);
    proof {
        lemma_stage_step(m0, m1, *m, 2, 0x3333_3333_3333_3333);
    }
    let ghost m1 = *m;
    round::<1>(m, 0x5555_5555_5555_5555);
    proof {
        lemma_stage_step(m0, m1, *m, 1, 0x5555_5555_5555_5555);
        assert forall|r: int, c: int| 0 <= r < 64 && 0 <= c < 64 implies #[trigger] bit64(m[c], r) == bit64(
            m0[r],
            c,
        ) by {
            let (r, c) = (r as u64, c as u64);
            assert(r < 64 && c < 64 ==> c ^ ((c ^ r) & high_bits(1)) == r && r ^ ((c ^ r) & high_bits(1)) == c)
                by (bit_vector);
        }
    }
}

/// Transposing twice gives back the matrix.
pub proof fn lemma_transpose_64x64_involution(a: [u64; 64], b: [u64; 64], c: [u64; 64])
    requires
        is_transpose_64x64(a, b),
        is_transpose_64x64(b, c),
    ensures
        c == a,
{
    assert forall|r: int| 0 <= r < 64 implies c[r] == a[r] by {
        assert forall|i: int| 0 <= i < 64 implies #[trigger] bit64(c[r], i) == bit64(a[r], i) by {
            assert(bit64(c[r], i) == bit64(b[i], r));
            assert(bit64(b[i], r) == bit64(a[r], i));
        }
        lemma_bit64_ext(c[r], a[r]);
    }
    assert(c =~= a);
}

// ---------------------------------------------------------------------------------------------
// The 64-byte transpose
// ---------------------------------------------------------------------------------------------
/// Transpose the 8x8 bit matrix whose byte `r` is row `r` (Hacker's Delight, section 7-3).
///
/// Bit `r * 8 + c` moves to bit `c * 8 + r`.
#[inline(always)]
pub const fn transpose_8x8_bits(mut x: u64) -> (y: u64)
    ensures
        y == transpose_8x8_formula(x),
        forall|r: int, c: int| 0 <= r < 8 && 0 <= c < 8 ==> #[trigger] bit64(y, r * 8 + c) == bit64(x, c * 8 + r),
{
    let ghost x0 = x;
    let t = (x ^ (x >> 7)) & 0x00AA_00AA_00AA_00AA;
    x ^= t ^ (t << 7);
    let t = (x ^ (x >> 14)) & 0x0000_CCCC_0000_CCCC;
    x ^= t ^ (t << 14);
    let t = (x ^ (x >> 28)) & 0x0000_0000_F0F0_F0F0;
    proof {
        assert forall|r: int, c: int| 0 <= r < 8 && 0 <= c < 8 implies #[trigger] bit64(
            transpose_8x8_formula(x0),
            r * 8 + c,
        ) == bit64(x0, c * 8 + r) by {
            lemma_transpose_8x8_bit(x0, r as u64, c as u64);
        }
    }
    x ^ t ^ (t << 28)
}

/// Gathering byte `v` into byte `x` of a word whose bytes from `x` up are clear.
proof fn lemma_gather_byte(column: u64, v: u8, x: u64, x2: u64, t: u64)
    by (bit_vector)
    requires
        x < 8,
        t < 8,
        column >> mul(8, x) == 0,
    ensures
        add(x, 1) < 8 ==> (column | ((v as u64) << mul(8, x))) >> mul(8, add(x, 1)) == 0,
        x2 < x ==> ((((column | ((v as u64) << mul(8, x))) >> add(mul(x2, 8), t)) & 1 == 1) == ((column >> add(
            mul(x2, 8),
            t,
        )) & 1 == 1)),
        (((column | ((v as u64) << mul(8, x))) >> add(mul(x, 8), t)) & 1 == 1) == ((v >> (t as u8)) & 1 == 1),
{
}

/// Byte `t` of a word, bit `x`, is bit `t * 8 + x` of the word.
proof fn lemma_scatter_byte(row: u64, t: u64, x: u64)
    by (bit_vector)
    requires
        t < 8,
        x < 8,
    ensures
        ((((row >> mul(8, t)) as u8) >> (x as u8)) & 1 == 1) == ((row >> add(mul(t, 8), x)) & 1 == 1),
{
}

/// What every arm of `bit_transpose_64bytes` computes: bit `x` of `output[8b + t]` is bit `t` of `input[8x + b]`.
///
/// ```text
///     output[b * 8 + t] bit x  =  input[x * 8 + b] bit t
/// ```
pub open spec fn is_bit_transpose_64bytes(input: [u8; 64], output: [u8; 64]) -> bool {
    forall|b: int, t: int, x: int|
        0 <= b < 8 && 0 <= t < 8 && 0 <= x < 8 ==> #[trigger] bit8(output[b * 8 + t], x) == bit8(input[x * 8 + b], t)
}

/// Gather each byte column into a word, and transpose its bits.
///
/// ```text
///     output[b * 8 + t] bit x  =  input[x * 8 + b] bit t
/// ```
///
/// The production iterates `output.as_chunks_mut::<8>()`, gathers the column with
/// `u64::from_le_bytes(std::array::from_fn(|x| input[8 * x + b]))` and stores the row with `to_le_bytes`; the
/// copy spells out the same gather and store as loops over the bytes. Production's function is private.
#[inline]
pub fn bit_transpose_64bytes_portable(input: &[u8; 64], output: &mut [u8; 64])
    ensures
        is_bit_transpose_64bytes(*input, *final(output)),
{
    for b in 0..8
        invariant
            forall|b2: int, t: int, x: int|
                0 <= b2 < b && 0 <= t < 8 && 0 <= x < 8 ==> #[trigger] bit8(output[b2 * 8 + t], x) == bit8(
                    input[x * 8 + b2],
                    t,
                ),
    {
        // `u64::from_le_bytes(std::array::from_fn(|x| input[8 * x + b]))`: byte `x` of the column is
        // `input[8 * x + b]`.
        let mut column = 0u64;
        assert(0u64 >> mul(8, 0u64) == 0) by (bit_vector);
        for x in 0..8
            invariant
                0 <= b < 8,
                x < 8 ==> column >> mul(8, x as u64) == 0,
                forall|x2: int, t: int|
                    0 <= x2 < x && 0 <= t < 8 ==> #[trigger] bit64(column, x2 * 8 + t) == bit8(input[x2 * 8 + b], t),
        {
            let ghost c0 = column;
            column |= (input[8 * x + b] as u64) << (8 * x);
            proof {
                let v = input[8 * x + b];
                lemma_gather_byte(c0, v, x as u64, 0, 0);
                assert forall|x2: int, t: int| 0 <= x2 < x + 1 && 0 <= t < 8 implies #[trigger] bit64(
                    column,
                    x2 * 8 + t,
                ) == bit8(input[x2 * 8 + b], t) by {
                    lemma_gather_byte(c0, v, x as u64, x2 as u64, t as u64);
                    if x2 < x {
                        assert(bit64(c0, x2 * 8 + t) == bit8(input[x2 * 8 + b], t));
                    }
                }
            }
        }
        let row = transpose_8x8_bits(column);
        // `*row = transpose_8x8_bits(column).to_le_bytes()`: byte `t` of the row is `output[8 * b + t]`.
        for t in 0..8
            invariant
                0 <= b < 8,
                forall|r: int, c: int| 0 <= r < 8 && 0 <= c < 8 ==> #[trigger] bit64(row, r * 8 + c) == bit64(column, c * 8 + r),
                forall|x2: int, t2: int|
                    0 <= x2 < 8 && 0 <= t2 < 8 ==> #[trigger] bit64(column, x2 * 8 + t2) == bit8(input[x2 * 8 + b], t2),
                forall|b2: int, t2: int, x: int|
                    0 <= b2 < b && 0 <= t2 < 8 && 0 <= x < 8 ==> #[trigger] bit8(output[b2 * 8 + t2], x) == bit8(
                        input[x * 8 + b2],
                        t2,
                    ),
                forall|t2: int, x: int|
                    0 <= t2 < t && 0 <= x < 8 ==> #[trigger] bit8(output[b * 8 + t2], x) == bit8(input[x * 8 + b], t2),
        {
            output[8 * b + t] = (row >> (8 * t)) as u8;
            proof {
                assert forall|x: int| 0 <= x < 8 implies #[trigger] bit8(output[b * 8 + t], x) == bit8(
                    input[x * 8 + b],
                    t as int,
                ) by {
                    lemma_scatter_byte(row, t as u64, x as u64);
                    assert(bit64(row, t * 8 + x) == bit64(column, x * 8 + t));
                    assert(bit64(column, x * 8 + t) == bit8(input[x * 8 + b], t as int));
                }
            }
        }
        proof {
            assert forall|b2: int, t: int, x: int| 0 <= b2 < b + 1 && 0 <= t < 8 && 0 <= x < 8 implies #[trigger] bit8(
                output[b2 * 8 + t],
                x,
            ) == bit8(input[x * 8 + b2], t) by {
                if b2 == b {
                    assert(bit8(output[b * 8 + t], x) == bit8(input[x * 8 + b], t));
                }
            }
        }
    }
}

/// Transpose the eight 8x8 bit matrices of a 64-byte block, gathered across rows.
///
/// ```text
///     output[b * 8 + t] bit x  =  input[x * 8 + b] bit t
/// ```
///
/// So byte column `b` of the eight input rows becomes output row `b`, bit-transposed.
///
/// - AVX-512 VBMI with GFNI: one byte permute and one affine map.
/// - AVX2 with GFNI: a byte gather in shuffles and unpacks, then one affine map.
/// - AVX2: the same gather, then three masked-swap rounds.
/// - aarch64: a table lookup, then three masked-swap rounds.
/// - Elsewhere: the same rounds on a gathered word per column.
#[inline]
pub fn bit_transpose_64bytes(input: &[u8; 64], output: &mut [u8; 64])
    ensures
        is_bit_transpose_64bytes(*input, *final(output)),
{
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512vbmi", target_feature = "gfni"))]
    // SAFETY: the features are enabled at compile time.
    unsafe {
        bit_transpose_64bytes_gfni(input, output);
    }
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx2",
        target_feature = "gfni",
        not(target_feature = "avx512vbmi")
    ))]
    // SAFETY: the features are enabled at compile time.
    unsafe {
        bit_transpose_64bytes_gfni_avx2(input, output);
    }
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "gfni")))]
    // SAFETY: the feature is enabled at compile time.
    unsafe {
        bit_transpose_64bytes_avx2(input, output);
    }
    #[cfg(target_arch = "aarch64")]
    // SAFETY: aarch64 always has NEON.
    unsafe {
        bit_transpose_64bytes_neon(input, output);
    }
    #[cfg(not(any(
        all(target_arch = "x86_64", target_feature = "avx512vbmi", target_feature = "gfni"),
        all(target_arch = "x86_64", target_feature = "avx2"),
        target_arch = "aarch64"
    )))]
    bit_transpose_64bytes_portable(input, output);
}

// ---------------------------------------------------------------------------------------------
// The SIMD arms: shared specifications and lemmas
// ---------------------------------------------------------------------------------------------
/// Byte `t` of a word, little-endian.
pub open spec fn byte_of(w: u64, t: int) -> u8 {
    (w >> ((8 * t) as u64)) as u8
}

/// `column` holds byte column `b` of the input in row order: its byte `x` is `input[8x + b]`.
pub open spec fn is_column(input: [u8; 64], b: int, column: u64) -> bool {
    forall|x: int| 0 <= x < 8 ==> #[trigger] byte_of(column, x) == input[8 * x + b]
}

/// `column` holds byte column `b` of the input in reversed row order: its byte `y` is `input[8 (7 - y) + b]`.
pub open spec fn is_reversed_column(input: [u8; 64], b: int, column: u64) -> bool {
    forall|y: int| 0 <= y < 8 ==> #[trigger] byte_of(column, y) == input[8 * (7 - y) + b]
}

proof fn lemma_cases_4(k: int)
    requires
        0 <= k < 4,
    ensures
        k == 0 || k == 1 || k == 2 || k == 3,
{
}

proof fn lemma_cases_8(k: int)
    requires
        0 <= k < 8,
    ensures
        k == 0 || k == 1 || k == 2 || k == 3 || k == 4 || k == 5 || k == 6 || k == 7,
{
}

proof fn lemma_cases_16(k: int)
    requires
        0 <= k < 16,
    ensures
        k == 0 || k == 1 || k == 2 || k == 3 || k == 4 || k == 5 || k == 6 || k == 7 || k == 8 || k == 9 || k == 10
            || k == 11 || k == 12 || k == 13 || k == 14 || k == 15,
{
}

proof fn lemma_cases_32(k: int)
    requires
        0 <= k < 32,
    ensures
        k == 0 || k == 1 || k == 2 || k == 3 || k == 4 || k == 5 || k == 6 || k == 7 || k == 8 || k == 9 || k == 10
            || k == 11 || k == 12 || k == 13 || k == 14 || k == 15 || k == 16 || k == 17 || k == 18 || k == 19 || k
            == 20 || k == 21 || k == 22 || k == 23 || k == 24 || k == 25 || k == 26 || k == 27 || k == 28 || k == 29
            || k == 30 || k == 31,
{
}

/// Byte `8j + t` of a run of words is byte `t` of word `j`.
proof fn lemma_div8(j: int, t: int)
    requires
        0 <= t < 8,
    ensures
        (8 * j + t) / 8 == j,
        (8 * j + t) % 8 == t,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(8 * j + t, 8, j, t);
}

/// The 8x8 transpose of column `b` is output row `b`: bit `x` of its byte `t` is bit `t` of `input[8x + b]`.
proof fn lemma_transposed_column(input: [u8; 64], b: int, column: u64, t: int)
    requires
        0 <= b < 8,
        0 <= t < 8,
        is_column(input, b, column),
    ensures
        forall|x: int|
            0 <= x < 8 ==> #[trigger] bit8(byte_of(transpose_8x8_formula(column), t), x) == bit8(input[x * 8 + b], t),
{
    let row = transpose_8x8_formula(column);
    assert forall|x: int| 0 <= x < 8 implies #[trigger] bit8(byte_of(row, t), x) == bit8(input[x * 8 + b], t) by {
        lemma_scatter_byte(row, t as u64, x as u64);
        lemma_transpose_8x8_bit(column, t as u64, x as u64);
        lemma_scatter_byte(column, x as u64, t as u64);
        assert(byte_of(column, x) == input[8 * x + b]);
    }
}

/// The masked swap of one round of [`transpose_8x8_bits`] on a word: `t = (x ^ (x >> d)) & mask`, then
/// `x ^ (t ^ (t << d))`.
pub open spec fn swap_word(x: u64, d: u64, mask: u64) -> u64 {
    let t = (x ^ (x >> d)) & mask;
    x ^ (t ^ (t << d))
}

/// The three masked swaps of the AVX2 and NEON arms are [`transpose_8x8_formula`].
pub proof fn lemma_three_swaps(x: u64)
    ensures
        swap_word(swap_word(swap_word(x, 7, 0x00AA_00AA_00AA_00AAu64), 14, 0x0000_CCCC_0000_CCCCu64), 28, 0x0000_0000_F0F0_F0F0u64)
            == transpose_8x8_formula(x),
{
    assert(swap_word(swap_word(swap_word(x, 7, 0x00AA_00AA_00AA_00AAu64), 14, 0x0000_CCCC_0000_CCCCu64), 28, 0x0000_0000_F0F0_F0F0u64)
        == transpose_8x8_formula(x)) by (bit_vector);
}

/// The unit matrix constant of the GFNI arms, as `i64` and back.
proof fn lemma_unit_word()
    ensures
        (0x8040_2010_0804_0201u64 as i64) as u64 == 0x8040_2010_0804_0201u64,
{
    assert((0x8040_2010_0804_0201u64 as i64) as u64 == 0x8040_2010_0804_0201u64) by (bit_vector);
}

/// Byte `s` of the unit matrix constant `0x8040_2010_0804_0201` is `1 << s`.
proof fn lemma_unit_byte(s: u64)
    by (bit_vector)
    requires
        s < 8,
    ensures
        (0x8040_2010_0804_0201u64 >> mul(8, s)) as u8 == 1u8 << (s as u8),
{
}

/// A byte below 16 selects itself in a byte shuffle.
proof fn lemma_small_byte(v: u8)
    by (bit_vector)
    requires
        v < 16,
    ensures
        v & 0x80 == 0,
        v & 15 == v,
        v & 63 == v,
{
}

/// GF2P8AFFINEQB of the byte `1 << t` with matrix word `a`: bit `x` of the result is bit `t` of byte `7 - x`
/// of `a`.
#[cfg(target_arch = "x86_64")]
proof fn lemma_affine_unit(a: u64, t: u64, x: u64)
    by (bit_vector)
    requires
        t < 8,
        x < 8,
    ensures
        ((affine_byte(a, 1u8 << (t as u8), 0) >> (x as u8)) & 1 == 1) == ((((a >> mul(8, sub(7, x))) as u8) >> (t as u8))
            & 1 == 1),
{
}

/// A reversed column through the unit affine map is output row `b`: bit `x` of byte `t` is bit `t` of
/// `input[8x + b]`.
#[cfg(target_arch = "x86_64")]
proof fn lemma_affine_column(input: [u8; 64], b: int, column: u64, t: int)
    requires
        0 <= b < 8,
        0 <= t < 8,
        is_reversed_column(input, b, column),
    ensures
        forall|x: int|
            0 <= x < 8 ==> #[trigger] bit8(affine_byte(column, 1u8 << (t as u8), 0), x) == bit8(input[x * 8 + b], t),
{
    assert forall|x: int| 0 <= x < 8 implies #[trigger] bit8(affine_byte(column, 1u8 << (t as u8), 0), x) == bit8(
        input[x * 8 + b],
        t,
    ) by {
        lemma_affine_unit(column, t as u64, x as u64);
        assert(byte_of(column, 7 - x) == input[8 * (7 - (7 - x)) + b]);
    }
}

// ---------------------------------------------------------------------------------------------
// AVX-512 VBMI with GFNI
// ---------------------------------------------------------------------------------------------
/// Word `b`, byte `j`: input row `7 - j`, column `b`.
///
/// Production builds this function-local `const` with a `while` loop, entry `i` being `(7 - i % 8) * 8 + i / 8`;
/// here it is a module-level `const` with the 64 entries written out, which [`lemma_idx`] reads as that formula.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512vbmi", target_feature = "gfni"))]
pub const IDX: [u8; 64] = [
    56, 48, 40, 32, 24, 16, 8, 0, 57, 49, 41, 33, 25, 17, 9, 1, 58, 50, 42, 34, 26, 18, 10, 2, 59, 51, 43, 35, 27, 19,
    11, 3, 60, 52, 44, 36, 28, 20, 12, 4, 61, 53, 45, 37, 29, 21, 13, 5, 62, 54, 46, 38, 30, 22, 14, 6, 63, 55, 47,
    39, 31, 23, 15, 7,
];

/// Entry `8b + y` of [`IDX`] is byte `b` of input row `7 - y`.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512vbmi", target_feature = "gfni"))]
proof fn lemma_idx(b: int, y: int)
    requires
        0 <= b < 8,
        0 <= y < 8,
    ensures
        IDX[8 * b + y] as int == 8 * (7 - y) + b,
{
    lemma_cases_8(b);
    lemma_cases_8(y);
}

/// `vpermb` gathers each byte column into a word, rows reversed.
///
/// `vgf2p8affineqb` then computes, per byte `j` of the constant and word `A`:
///
/// ```text
///     result byte j bit i  =  parity(A byte (7 - i)  &  constant byte j)
/// ```
///
/// With constant byte `j = 1 << j`, that is bit `j` of `A`'s byte `7 - i`: the reversal undoes it.
///
/// Rewritten for Verus: the loads and the store through `as_ptr().cast()` are the helpers `load512_bytes` and
/// `store512_bytes`, whose bodies are those calls; `IDX` is a module-level `const` (see [`IDX`]). Production's
/// function is private.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512vbmi", target_feature = "gfni"))]
#[target_feature(enable = "avx512f,avx512vbmi,gfni")]
pub unsafe fn bit_transpose_64bytes_gfni(input: &[u8; 64], output: &mut [u8; 64])
    ensures
        is_bit_transpose_64bytes(*input, *final(output)),
{
    // SAFETY: each load and store is one 64-byte array.
    unsafe {
        let columns = _mm512_permutexvar_epi8(load512_bytes(&IDX), load512_bytes(input));
        let unit = _mm512_set1_epi64(0x8040_2010_0804_0201_u64 as i64);
        let rows = _mm512_gf2p8affine_epi64_epi8::<0>(unit, columns);
        proof {
            broadcast use axiom_m512_bytes;

            lemma_unit_word();
            assert forall|b: int, t: int, x: int| 0 <= b < 8 && 0 <= t < 8 && 0 <= x < 8 implies #[trigger] bit8(
                m512_bytes(rows)[b * 8 + t],
                x,
            ) == bit8(input[x * 8 + b], t) by {
                let column = m512(columns)[b];
                assert forall|y: int| 0 <= y < 8 implies #[trigger] byte_of(column, y) == input[8 * (7 - y) + b] by {
                    lemma_idx(b, y);
                    assert(IDX[8 * b + y] & 63 == IDX[8 * b + y]) by {
                        let v = IDX[8 * b + y];
                        assert(v < 64 ==> v & 63 == v) by (bit_vector);
                    }
                    lemma_div8(b, y);
                    assert(m512_bytes(columns)[8 * b + y] == input[8 * (7 - y) + b]);
                }
                lemma_div8(b, t);
                lemma_unit_byte(t as u64);
                assert(m512_bytes(unit)[8 * b + t] == 1u8 << (t as u8));
                lemma_affine_column(*input, b, column, t);
            }
        }
        store512_bytes(output, rows);
    }
}

// ---------------------------------------------------------------------------------------------
// AVX2: the column gather
// ---------------------------------------------------------------------------------------------
/// The word `_mm256_permute4x64_epi64::<0b11_01_10_00>` puts at word `i`.
pub open spec fn permute_d8(i: int) -> int {
    if i == 1 {
        2
    } else if i == 2 {
        1
    } else {
        i
    }
}

/// The input byte at byte `k` of register `w` after the two unpack rounds of [`gather_columns_avx2`]: lane
/// `k / 16` holds rows `0, 1, 4, 5` (lane 0) or `2, 3, 6, 7` (lane 1), dword `(k % 16) / 4` of it column
/// `4w + (k % 16) / 4`.
pub open spec fn unpacked_src(w: int, k: int) -> int {
    16 * (k / 16) + 4 * w + (k % 16) / 4 + 8 * (k % 2) + 32 * ((k / 2) % 2)
}

/// The input byte at byte `k` of register `w` of [`gather_columns_avx2`] before its final shuffle: lane `l`
/// holds columns `4w + 2l` and `4w + 2l + 1`.
pub open spec fn gather_src(w: int, k: int) -> int {
    unpacked_src(w, 8 * permute_d8(k / 8) + k % 8)
}

/// The selections of the immediate `0b11_01_10_00`.
proof fn lemma_permute_d8()
    ensures
        forall|i: int| 0 <= i < 4 ==> (((0b11_01_10_00i32 as u8) >> ((2 * i) as u8)) & 3) as int == #[trigger] permute_d8(i),
{
    assert(((0xD8u8 >> 0u8) & 3) == 0) by (bit_vector);
    assert(((0xD8u8 >> 2u8) & 3) == 2) by (bit_vector);
    assert(((0xD8u8 >> 4u8) & 3) == 1) by (bit_vector);
    assert(((0xD8u8 >> 6u8) & 3) == 3) by (bit_vector);
    assert forall|i: int| 0 <= i < 4 implies (((0b11_01_10_00i32 as u8) >> ((2 * i) as u8)) & 3) as int == #[trigger] permute_d8(i) by {
        lemma_cases_4(i);
    }
}

/// The input byte at byte `k` of the first unpack round of [`gather_columns_avx2`] (`unpacklo`; the `unpackhi`
/// one is 8 further): in each lane, rows `r` and `r + 4` byte-interleaved.
pub open spec fn unpack1_src(k: int) -> int {
    16 * (k / 16) + (k % 16) / 2 + 32 * (k % 2)
}

/// The two unpack rounds of [`gather_columns_avx2`] put input byte [`unpacked_src`] at each byte.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[verifier::rlimit(30)]
proof fn lemma_unpack_rounds(
    input: [u8; 64],
    v0: __m256i,
    v1: __m256i,
    t0: __m256i,
    t1: __m256i,
    u0: __m256i,
    u1: __m256i,
)
    requires
        forall|k: int| 0 <= k < 32 ==> #[trigger] m256_bytes(v0)[k] == input[0 + k],
        forall|k: int| 0 <= k < 32 ==> #[trigger] m256_bytes(v1)[k] == input[32 + k],
        forall|k: int|
            0 <= k < 32 ==> #[trigger] m256_bytes(t0)[k] == unpacklo_epi8_lane(m256_bytes(v0)@, m256_bytes(v1)@, k),
        forall|k: int|
            0 <= k < 32 ==> #[trigger] m256_bytes(t1)[k] == unpackhi_epi8_lane(m256_bytes(v0)@, m256_bytes(v1)@, k),
        forall|k: int|
            0 <= k < 32 ==> #[trigger] m256_bytes(u0)[k] == unpacklo_epi8_lane(m256_bytes(t0)@, m256_bytes(t1)@, k),
        forall|k: int|
            0 <= k < 32 ==> #[trigger] m256_bytes(u1)[k] == unpackhi_epi8_lane(m256_bytes(t0)@, m256_bytes(t1)@, k),
    ensures
        forall|k: int| 0 <= k < 32 ==> #[trigger] m256_bytes(u0)[k] == input[unpacked_src(0, k)],
        forall|k: int| 0 <= k < 32 ==> #[trigger] m256_bytes(u1)[k] == input[unpacked_src(1, k)],
{
    assert forall|k: int| 0 <= k < 32 implies #[trigger] m256_bytes(t0)[k] == input[unpack1_src(k)] by {
        let j = 16 * (k / 16) + (k % 16) / 2;
        assert(m256_bytes(v0)[j] == input[0 + j]);
        assert(m256_bytes(v1)[j] == input[32 + j]);
    }
    assert forall|k: int| 0 <= k < 32 implies #[trigger] m256_bytes(t1)[k] == input[unpack1_src(k) + 8] by {
        let j = 16 * (k / 16) + 8 + (k % 16) / 2;
        assert(m256_bytes(v0)[j] == input[0 + j]);
        assert(m256_bytes(v1)[j] == input[32 + j]);
    }
    assert forall|k: int| 0 <= k < 32 implies #[trigger] m256_bytes(u0)[k] == input[unpacked_src(0, k)] by {
        lemma_cases_32(k);
    }
    assert forall|k: int| 0 <= k < 32 implies #[trigger] m256_bytes(u1)[k] == input[unpacked_src(1, k)] by {
        lemma_cases_32(k);
    }
}

/// The permute of [`gather_columns_avx2`] moves input byte [`unpacked_src`] to [`gather_src`].
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
proof fn lemma_permuted(input: [u8; 64], u: __m256i, p: __m256i, w: int)
    requires
        forall|k: int| 0 <= k < 32 ==> #[trigger] m256_bytes(u)[k] == input[unpacked_src(w, k)],
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(p)[i] == permute4x64_lane(m256(u)@, 0b11_01_10_00i32 as u8, i),
    ensures
        forall|k: int| 0 <= k < 32 ==> #[trigger] m256_bytes(p)[k] == input[gather_src(w, k)],
{
    broadcast use axiom_m256_bytes;

    lemma_permute_d8();
    assert forall|k: int| 0 <= k < 32 implies #[trigger] m256_bytes(p)[k] == input[gather_src(w, k)] by {
        let (i, t) = (k / 8, k % 8);
        let s = permute_d8(i);
        lemma_div8(i, t);
        lemma_div8(s, t);
        assert(k == 8 * i + t);
        assert(m256(p)[i] == m256(u)[s]);
        assert(m256_bytes(u)[8 * s + t] == input[unpacked_src(w, 8 * s + t)]);
    }
}

/// Gather each byte column of the eight 8-byte rows into a word, in the row order `order` picks.
///
/// After two unpack rounds, lane `l` of the result's register `w` holds columns `4w + 2l` and `4w + 2l + 1`.
/// Their bytes sit at:
///
/// ```text
///     rows 0, 1, 4, 5    bytes 0..4 (first column), 4..8 (second)
///     rows 2, 3, 6, 7    bytes 8..12 (first column), 12..16 (second)
/// ```
///
/// So `order[8c + k]` is the byte that becomes byte `k` of the lane's column `c`.
///
/// Rewritten for Verus: the loads through `as_ptr().cast()` are the helpers `load256_bytes_at` and
/// `load128_bytes`, whose bodies are those calls; `[u0, u1].map(|u| ...)` is written out as its two calls, the
/// permutes bound to `p0`, `p1`. Production's function is private.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[inline]
#[target_feature(enable = "avx2")]
pub fn gather_columns_avx2(input: &[u8; 64], order: &[u8; 16]) -> (r: [__m256i; 2])
    ensures
        forall|w: int, k: int|
            0 <= w < 2 && 0 <= k < 32 && order[k % 16] < 16 ==> #[trigger] m256_bytes(r[w])[k] == input[gather_src(
                w,
                16 * (k / 16) + order[k % 16] as int,
            )],
{
    let ghost order_bytes = *order;
    // SAFETY: the loads read the two halves of the 64-byte input and the 16-byte order.
    let (v0, v1, order) = unsafe {
        (load256_bytes_at(input, 0), load256_bytes_at(input, 32), _mm256_broadcastsi128_si256(load128_bytes(order)))
    };
    // Lane 0: rows 0 and 4, then rows 1 and 5, byte-interleaved; lane 1: rows 2 and 6, then 3 and 7.
    let (t0, t1) = (_mm256_unpacklo_epi8(v0, v1), _mm256_unpackhi_epi8(v0, v1));
    // Dword `c` of lane 0 is column `c` of rows 0, 1, 4, 5; of lane 1, of rows 2, 3, 6, 7.
    let (u0, u1) = (_mm256_unpacklo_epi8(t0, t1), _mm256_unpackhi_epi8(t0, t1));
    proof {
        lemma_unpack_rounds(*input, v0, v1, t0, t1, u0, u1);
    }
    // Bring both halves of two columns into one lane, then order their bytes.
    let (p0, p1) = (_mm256_permute4x64_epi64::<0b11_01_10_00>(u0), _mm256_permute4x64_epi64::<0b11_01_10_00>(u1));
    proof {
        broadcast use axiom_m256_bytes, axiom_m128_bytes;

        lemma_permuted(*input, u0, p0, 0);
        lemma_permuted(*input, u1, p1, 1);
        assert forall|k: int| 0 <= k < 32 implies #[trigger] m256_bytes(order)[k] == order_bytes[k % 16] by {
            lemma_cases_32(k);
        }
    }
    let r = [_mm256_shuffle_epi8(p0, order), _mm256_shuffle_epi8(p1, order)];
    proof {
        assert forall|w: int, k: int| 0 <= w < 2 && 0 <= k < 32 && order_bytes[k % 16] < 16 implies #[trigger] m256_bytes(
            r[w],
        )[k] == input[gather_src(w, 16 * (k / 16) + order_bytes[k % 16] as int)] by {
            lemma_small_byte(order_bytes[k % 16]);
            assert(m256_bytes(order)[k] == order_bytes[k % 16]);
        }
    }
    r
}

// ---------------------------------------------------------------------------------------------
// AVX2 with GFNI
// ---------------------------------------------------------------------------------------------
/// Production's function-local `REVERSED` of `bit_transpose_64bytes_gfni_avx2`, at module level.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "gfni"))]
pub const REVERSED: [u8; 16] = [11, 10, 3, 2, 9, 8, 1, 0, 15, 14, 7, 6, 13, 12, 5, 4];

/// [`REVERSED`] orders each column's bytes by reversed row: byte `kk` of word `j` of register `w` is
/// `input[8 (7 - kk) + 4w + j]`.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "gfni"))]
proof fn lemma_reversed(w: int, j: int, kk: int)
    requires
        0 <= w < 2,
        0 <= j < 4,
        0 <= kk < 8,
    ensures
        REVERSED[(8 * j + kk) % 16] < 16,
        gather_src(w, 16 * ((8 * j + kk) / 16) + REVERSED[(8 * j + kk) % 16] as int) == 8 * (7 - kk) + 4 * w + j,
{
    lemma_cases_4(j);
    lemma_cases_8(kk);
}

/// One register of [`bit_transpose_64bytes_gfni_avx2`]: its four reversed columns through the unit affine map,
/// stored at `32i`, are output rows `4i..4i + 4`.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "gfni"))]
proof fn lemma_gfni_avx2_rows(
    input: [u8; 64],
    after: [u8; 64],
    i: int,
    unit: __m256i,
    columns: __m256i,
    rows: __m256i,
)
    requires
        0 <= i < 2,
        forall|j: int| 0 <= j < 4 ==> #[trigger] is_reversed_column(input, 4 * i + j, m256(columns)[j]),
        forall|k: int| 0 <= k < 32 ==> #[trigger] m256_bytes(unit)[k] == 1u8 << ((k % 8) as u8),
        forall|k: int|
            0 <= k < 32 ==> #[trigger] m256_bytes(rows)[k] == gf2p8affine_lane(m256_bytes(unit)@, m256(columns)@, 0i32 as u8, k),
        forall|k: int| 32 * i <= k < 32 * i + 32 ==> #[trigger] after[k] == m256_bytes(rows)[k - 32 * i],
    ensures
        forall|b: int, t: int, x: int|
            4 * i <= b < 4 * i + 4 && 0 <= t < 8 && 0 <= x < 8 ==> #[trigger] bit8(after[b * 8 + t], x) == bit8(
                input[x * 8 + b],
                t,
            ),
{
    assert forall|b: int, t: int, x: int| 4 * i <= b < 4 * i + 4 && 0 <= t < 8 && 0 <= x < 8 implies #[trigger] bit8(
        after[b * 8 + t],
        x,
    ) == bit8(input[x * 8 + b], t) by {
        let j = b - 4 * i;
        lemma_div8(j, t);
        assert(after[b * 8 + t] == m256_bytes(rows)[8 * j + t]);
        assert(m256_bytes(unit)[8 * j + t] == 1u8 << (t as u8));
        assert(is_reversed_column(input, 4 * i + j, m256(columns)[j]));
        lemma_affine_column(input, b, m256(columns)[j], t);
    }
}

/// [`gather_columns_avx2`] with the rows reversed, then the affine map of the AVX-512 arm.
///
/// Rewritten for Verus: `for (i, columns) in gather_columns_avx2(input, &REVERSED).into_iter().enumerate()` is an
/// index loop over the gathered pair; the store through `as_mut_ptr().add(32 * i).cast()` is the helper
/// `store256_bytes_at`, whose body is that call; `REVERSED` is a module-level `const`. Production's function is
/// private.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "gfni"))]
#[cfg_attr(target_feature = "avx512vbmi", allow(dead_code))]
#[target_feature(enable = "avx2,gfni")]
pub unsafe fn bit_transpose_64bytes_gfni_avx2(input: &[u8; 64], output: &mut [u8; 64])
    ensures
        is_bit_transpose_64bytes(*input, *final(output)),
{
    let unit = _mm256_set1_epi64x(0x8040_2010_0804_0201_u64 as i64);
    let gathered = gather_columns_avx2(input, &REVERSED);
    proof {
        broadcast use axiom_m256_bytes;

        lemma_unit_word();
        assert forall|k: int| 0 <= k < 32 implies #[trigger] m256_bytes(unit)[k] == 1u8 << ((k % 8) as u8) by {
            lemma_unit_byte((k % 8) as u64);
        }
        assert forall|w: int, j: int| 0 <= w < 2 && 0 <= j < 4 implies #[trigger] is_reversed_column(
            *input,
            4 * w + j,
            m256(gathered[w])[j],
        ) by {
            assert forall|kk: int| 0 <= kk < 8 implies #[trigger] byte_of(m256(gathered[w])[j], kk) == input[8 * (7
                - kk) + 4 * w + j] by {
                lemma_reversed(w, j, kk);
                lemma_div8(j, kk);
                assert(m256_bytes(gathered[w])[8 * j + kk] == input[8 * (7 - kk) + 4 * w + j]);
            }
        }
    }
    for i in 0..2
        invariant
            forall|k: int| 0 <= k < 32 ==> #[trigger] m256_bytes(unit)[k] == 1u8 << ((k % 8) as u8),
            forall|w: int, j: int|
                0 <= w < 2 && 0 <= j < 4 ==> #[trigger] is_reversed_column(*input, 4 * w + j, m256(gathered[w])[j]),
            forall|b: int, t: int, x: int|
                0 <= b < 4 * i && 0 <= t < 8 && 0 <= x < 8 ==> #[trigger] bit8(output[b * 8 + t], x) == bit8(
                    input[x * 8 + b],
                    t,
                ),
    {
        let columns = gathered[i];
        let rows = _mm256_gf2p8affine_epi64_epi8::<0>(unit, columns);
        // SAFETY: the two stores fill the 64-byte output.
        unsafe { store256_bytes_at(output, 32 * i, rows) };
        proof {
            assert forall|j: int| 0 <= j < 4 implies #[trigger] is_reversed_column(*input, 4 * i + j, m256(columns)[j]) by {
                assert(is_reversed_column(*input, 4 * i + j, m256(gathered[i as int])[j]));
            }
            lemma_gfni_avx2_rows(*input, *output, i as int, unit, columns, rows);
        }
    }
}

// ---------------------------------------------------------------------------------------------
// AVX2
// ---------------------------------------------------------------------------------------------
/// Production's function-local `NATURAL` of `bit_transpose_64bytes_avx2`, at module level.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
pub const NATURAL: [u8; 16] = [0, 1, 8, 9, 2, 3, 10, 11, 4, 5, 12, 13, 6, 7, 14, 15];

/// [`NATURAL`] orders each column's bytes by row: byte `kk` of word `j` of register `w` is `input[8kk + 4w + j]`.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
proof fn lemma_natural(w: int, j: int, kk: int)
    requires
        0 <= w < 2,
        0 <= j < 4,
        0 <= kk < 8,
    ensures
        NATURAL[(8 * j + kk) % 16] < 16,
        gather_src(w, 16 * ((8 * j + kk) / 16) + NATURAL[(8 * j + kk) % 16] as int) == 8 * kk + 4 * w + j,
{
    lemma_cases_4(j);
    lemma_cases_8(kk);
}

/// The masked swap of [`transpose_8x8_bits`] on four words.
///
/// Production nests this function in `bit_transpose_64bytes_avx2`; Verus does not take nested functions, so it
/// is here, under that function's `cfg`.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[inline]
#[target_feature(enable = "avx2")]
pub fn swap<const D: i32>(x: __m256i, mask: u64) -> (r: __m256i)
    requires
        0 < D < 64,
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r)[i] == swap_word(m256(x)[i], D as u64, mask),
{
    let ghost m = mask;
    let mask = _mm256_set1_epi64x(mask as i64);
    proof {
        assert((m as i64) as u64 == m) by (bit_vector);
    }
    let t = _mm256_and_si256(_mm256_xor_si256(x, _mm256_srli_epi64::<D>(x)), mask);
    _mm256_xor_si256(x, _mm256_xor_si256(t, _mm256_slli_epi64::<D>(t)))
}

/// One register of [`bit_transpose_64bytes_avx2`]: its four columns, transposed and stored at `32i`, are output
/// rows `4i..4i + 4`.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
proof fn lemma_avx2_rows(input: [u8; 64], after: [u8; 64], i: int, columns: __m256i, rows: __m256i)
    requires
        0 <= i < 2,
        forall|j: int| 0 <= j < 4 ==> #[trigger] is_column(input, 4 * i + j, m256(columns)[j]),
        forall|j: int| 0 <= j < 4 ==> #[trigger] m256(rows)[j] == transpose_8x8_formula(m256(columns)[j]),
        forall|k: int| 32 * i <= k < 32 * i + 32 ==> #[trigger] after[k] == m256_bytes(rows)[k - 32 * i],
    ensures
        forall|b: int, t: int, x: int|
            4 * i <= b < 4 * i + 4 && 0 <= t < 8 && 0 <= x < 8 ==> #[trigger] bit8(after[b * 8 + t], x) == bit8(
                input[x * 8 + b],
                t,
            ),
{
    broadcast use axiom_m256_bytes;

    assert forall|b: int, t: int, x: int| 4 * i <= b < 4 * i + 4 && 0 <= t < 8 && 0 <= x < 8 implies #[trigger] bit8(
        after[b * 8 + t],
        x,
    ) == bit8(input[x * 8 + b], t) by {
        let j = b - 4 * i;
        lemma_div8(j, t);
        assert(after[b * 8 + t] == m256_bytes(rows)[8 * j + t]);
        assert(m256_bytes(rows)[8 * j + t] == byte_of(transpose_8x8_formula(m256(columns)[j]), t));
        assert(is_column(input, 4 * i + j, m256(columns)[j]));
        lemma_transposed_column(input, b, m256(columns)[j], t);
    }
}

/// [`gather_columns_avx2`] in row order, then the three masked-swap rounds of [`transpose_8x8_bits`] on four
/// words at a time.
///
/// Rewritten for Verus: `for (i, x) in gather_columns_avx2(input, &NATURAL).into_iter().enumerate()` is an index
/// loop over the gathered pair; the store through `as_mut_ptr().add(32 * i).cast()` is the helper
/// `store256_bytes_at`, whose body is that call; `NATURAL` and `swap` are at module level. Production's function
/// is private.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[cfg_attr(target_feature = "gfni", allow(dead_code))]
#[target_feature(enable = "avx2")]
pub unsafe fn bit_transpose_64bytes_avx2(input: &[u8; 64], output: &mut [u8; 64])
    ensures
        is_bit_transpose_64bytes(*input, *final(output)),
{
    let gathered = gather_columns_avx2(input, &NATURAL);
    proof {
        broadcast use axiom_m256_bytes;

        assert forall|w: int, j: int| 0 <= w < 2 && 0 <= j < 4 implies #[trigger] is_column(
            *input,
            4 * w + j,
            m256(gathered[w])[j],
        ) by {
            assert forall|kk: int| 0 <= kk < 8 implies #[trigger] byte_of(m256(gathered[w])[j], kk) == input[8 * kk + 4
                * w + j] by {
                lemma_natural(w, j, kk);
                lemma_div8(j, kk);
                assert(m256_bytes(gathered[w])[8 * j + kk] == input[8 * kk + 4 * w + j]);
            }
        }
    }
    for i in 0..2
        invariant
            forall|w: int, j: int|
                0 <= w < 2 && 0 <= j < 4 ==> #[trigger] is_column(*input, 4 * w + j, m256(gathered[w])[j]),
            forall|b: int, t: int, x: int|
                0 <= b < 4 * i && 0 <= t < 8 && 0 <= x < 8 ==> #[trigger] bit8(output[b * 8 + t], x) == bit8(
                    input[x * 8 + b],
                    t,
                ),
    {
        let x = gathered[i];
        let ghost columns = x;
        let x = swap::<7>(x, 0x00AA_00AA_00AA_00AA);
        let x = swap::<14>(x, 0x0000_CCCC_0000_CCCC);
        let x = swap::<28>(x, 0x0000_0000_F0F0_F0F0);
        // SAFETY: the two stores fill the 64-byte output.
        unsafe { store256_bytes_at(output, 32 * i, x) };
        proof {
            assert forall|j: int| 0 <= j < 4 implies #[trigger] m256(x)[j] == transpose_8x8_formula(m256(columns)[j]) by {
                lemma_three_swaps(m256(columns)[j]);
            }
            assert forall|j: int| 0 <= j < 4 implies #[trigger] is_column(*input, 4 * i + j, m256(columns)[j]) by {
                assert(is_column(*input, 4 * i + j, m256(gathered[i as int])[j]));
            }
            lemma_avx2_rows(*input, *output, i as int, columns, x);
        }
    }
}

// ---------------------------------------------------------------------------------------------
// NEON
// ---------------------------------------------------------------------------------------------
/// Production's function-local `vqtbl4q` indexes of `bit_transpose_64bytes_neon`, at module level: they bring
/// bytes belonging to byte-chunk `b` in `0..8` into contiguous 8-byte runs, packed two chunks per Q register.
#[cfg(target_arch = "aarch64")]
pub const IDX0: [u8; 16] = [0, 8, 16, 24, 32, 40, 48, 56, 1, 9, 17, 25, 33, 41, 49, 57];
#[cfg(target_arch = "aarch64")]
pub const IDX1: [u8; 16] = [2, 10, 18, 26, 34, 42, 50, 58, 3, 11, 19, 27, 35, 43, 51, 59];
#[cfg(target_arch = "aarch64")]
pub const IDX2: [u8; 16] = [4, 12, 20, 28, 36, 44, 52, 60, 5, 13, 21, 29, 37, 45, 53, 61];
#[cfg(target_arch = "aarch64")]
pub const IDX3: [u8; 16] = [6, 14, 22, 30, 38, 46, 54, 62, 7, 15, 23, 31, 39, 47, 55, 63];

/// Entry `k` of `IDXj` is row `k % 8` of column `2j + k / 8`.
#[cfg(target_arch = "aarch64")]
proof fn lemma_neon_idx(k: int)
    requires
        0 <= k < 16,
    ensures
        IDX0[k] as int == 8 * (k % 8) + k / 8,
        IDX1[k] as int == 8 * (k % 8) + 2 + k / 8,
        IDX2[k] as int == 8 * (k % 8) + 4 + k / 8,
        IDX3[k] as int == 8 * (k % 8) + 6 + k / 8,
{
    lemma_cases_16(k);
}

/// One table lookup of [`bit_transpose_64bytes_neon`]: with the index `idx` of register `j`, its two words are
/// columns `2j` and `2j + 1`.
#[cfg(target_arch = "aarch64")]
proof fn lemma_neon_columns(
    input: [u8; 64],
    v0: uint8x16_t,
    v1: uint8x16_t,
    v2: uint8x16_t,
    v3: uint8x16_t,
    idx: [u8; 16],
    y: uint64x2_t,
    j: int,
)
    requires
        0 <= j < 4,
        forall|k: int| 0 <= k < 16 ==> #[trigger] u8x16(v0)[k] == input[k],
        forall|k: int| 0 <= k < 16 ==> #[trigger] u8x16(v1)[k] == input[16 + k],
        forall|k: int| 0 <= k < 16 ==> #[trigger] u8x16(v2)[k] == input[32 + k],
        forall|k: int| 0 <= k < 16 ==> #[trigger] u8x16(v3)[k] == input[48 + k],
        forall|k: int| 0 <= k < 16 ==> #[trigger] idx[k] as int == 8 * (k % 8) + 2 * j + k / 8,
        forall|k: int|
            0 <= k < 16 ==> #[trigger] u64x2_byte(u64x2(y)@, k) == tbl4_byte(
                u8x16(v0)@,
                u8x16(v1)@,
                u8x16(v2)@,
                u8x16(v3)@,
                idx[k] as int,
            ),
    ensures
        is_column(input, 2 * j, u64x2(y)[0]),
        is_column(input, 2 * j + 1, u64x2(y)[1]),
{
    assert forall|x: int| 0 <= x < 8 implies #[trigger] byte_of(u64x2(y)[0], x) == input[8 * x + 2 * j] by {
        lemma_div8(0, x);
        assert(idx[x] as int == 8 * x + 2 * j);
        assert(u64x2_byte(u64x2(y)@, x) == input[8 * x + 2 * j]);
    }
    assert forall|x: int| 0 <= x < 8 implies #[trigger] byte_of(u64x2(y)[1], x) == input[8 * x + 2 * j + 1] by {
        lemma_div8(1, x);
        assert(idx[8 + x] as int == 8 * x + 2 * j + 1);
        assert(u64x2_byte(u64x2(y)@, 8 + x) == input[8 * x + 2 * j + 1]);
    }
}

/// One register of [`bit_transpose_64bytes_neon`]: its two columns, transposed and stored at `16j`, are output
/// rows `2j` and `2j + 1`.
#[cfg(target_arch = "aarch64")]
proof fn lemma_neon_rows(input: [u8; 64], output: [u8; 64], j: int, columns: uint64x2_t, rows: uint64x2_t)
    requires
        0 <= j < 4,
        is_column(input, 2 * j, u64x2(columns)[0]),
        is_column(input, 2 * j + 1, u64x2(columns)[1]),
        u64x2(rows)[0] == transpose_8x8_formula(u64x2(columns)[0]),
        u64x2(rows)[1] == transpose_8x8_formula(u64x2(columns)[1]),
        forall|k: int| 16 * j <= k < 16 * j + 16 ==> #[trigger] output[k] == u64x2_byte(u64x2(rows)@, k - 16 * j),
    ensures
        forall|b: int, t: int, x: int|
            2 * j <= b < 2 * j + 2 && 0 <= t < 8 && 0 <= x < 8 ==> #[trigger] bit8(output[b * 8 + t], x) == bit8(
                input[x * 8 + b],
                t,
            ),
{
    assert forall|b: int, t: int, x: int| 2 * j <= b < 2 * j + 2 && 0 <= t < 8 && 0 <= x < 8 implies #[trigger] bit8(
        output[b * 8 + t],
        x,
    ) == bit8(input[x * 8 + b], t) by {
        let h = b - 2 * j;
        lemma_div8(h, t);
        assert(output[b * 8 + t] == u64x2_byte(u64x2(rows)@, 8 * h + t));
        assert(output[b * 8 + t] == byte_of(u64x2(rows)[h], t));
        if h == 0 {
            lemma_transposed_column(input, b, u64x2(columns)[0], t);
        } else {
            lemma_transposed_column(input, b, u64x2(columns)[1], t);
        }
    }
}

/// `vqtbl4q_u8` gathers each byte column into a word, then three masked-swap rounds transpose its bits.
///
/// Rewritten for Verus: the loads `vld1q_u8(in_ptr.add(16 * j))` and `vld1q_u8(IDXj.as_ptr())` and the stores
/// `vst1q_u8(out_ptr.add(16 * j), ..)` are the helpers `vld1q_u8_at`, `vld1q_u8_16` and `vst1q_u8_at`, whose
/// bodies are those calls (so `in_ptr` and `out_ptr` are gone); `IDX0..IDX3` are module-level `const`s.
/// Production's function is private.
#[cfg(target_arch = "aarch64")]
#[inline(always)]
pub unsafe fn bit_transpose_64bytes_neon(input: &[u8; 64], output: &mut [u8; 64])
    ensures
        is_bit_transpose_64bytes(*input, *final(output)),
{
    // SAFETY: NEON is part of the aarch64 baseline, and every load and store offset is below 64, the length of
    // both arrays.
    unsafe {
        let v0 = vld1q_u8_at(input, 0);
        let v1 = vld1q_u8_at(input, 16);
        let v2 = vld1q_u8_at(input, 32);
        let v3 = vld1q_u8_at(input, 48);
        let table = uint8x16x4_t(v0, v1, v2, v3);

        let mut y0 = vreinterpretq_u64_u8(vqtbl4q_u8(table, vld1q_u8_16(&IDX0)));
        let mut y1 = vreinterpretq_u64_u8(vqtbl4q_u8(table, vld1q_u8_16(&IDX1)));
        let mut y2 = vreinterpretq_u64_u8(vqtbl4q_u8(table, vld1q_u8_16(&IDX2)));
        let mut y3 = vreinterpretq_u64_u8(vqtbl4q_u8(table, vld1q_u8_16(&IDX3)));
        let ghost (c0, c1, c2, c3) = (y0, y1, y2, y3);
        proof {
            assert forall|k: int| 0 <= k < 16 implies #[trigger] IDX0[k] as int == 8 * (k % 8) + 2 * 0 + k / 8 && IDX1[k]
                as int == 8 * (k % 8) + 2 * 1 + k / 8 && IDX2[k] as int == 8 * (k % 8) + 2 * 2 + k / 8 && IDX3[k] as int
                == 8 * (k % 8) + 2 * 3 + k / 8 by {
                lemma_neon_idx(k);
            }
            lemma_neon_columns(*input, v0, v1, v2, v3, IDX0, c0, 0);
            lemma_neon_columns(*input, v0, v1, v2, v3, IDX1, c1, 1);
            lemma_neon_columns(*input, v0, v1, v2, v3, IDX2, c2, 2);
            lemma_neon_columns(*input, v0, v1, v2, v3, IDX3, c3, 3);
        }

        let mask1 = vdupq_n_u64(0x00AA00AA00AA00AA);
        let mask2 = vdupq_n_u64(0x0000CCCC0000CCCC);
        let mask3 = vdupq_n_u64(0x00000000F0F0F0F0);

        // Round 1: distance 7.
        let t0 = vandq_u64(veorq_u64(y0, vshrq_n_u64::<7>(y0)), mask1);
        let t1 = vandq_u64(veorq_u64(y1, vshrq_n_u64::<7>(y1)), mask1);
        let t2 = vandq_u64(veorq_u64(y2, vshrq_n_u64::<7>(y2)), mask1);
        let t3 = vandq_u64(veorq_u64(y3, vshrq_n_u64::<7>(y3)), mask1);
        y0 = veorq_u64(y0, veorq_u64(t0, vshlq_n_u64::<7>(t0)));
        y1 = veorq_u64(y1, veorq_u64(t1, vshlq_n_u64::<7>(t1)));
        y2 = veorq_u64(y2, veorq_u64(t2, vshlq_n_u64::<7>(t2)));
        y3 = veorq_u64(y3, veorq_u64(t3, vshlq_n_u64::<7>(t3)));

        // Round 2: distance 14.
        let t0 = vandq_u64(veorq_u64(y0, vshrq_n_u64::<14>(y0)), mask2);
        let t1 = vandq_u64(veorq_u64(y1, vshrq_n_u64::<14>(y1)), mask2);
        let t2 = vandq_u64(veorq_u64(y2, vshrq_n_u64::<14>(y2)), mask2);
        let t3 = vandq_u64(veorq_u64(y3, vshrq_n_u64::<14>(y3)), mask2);
        y0 = veorq_u64(y0, veorq_u64(t0, vshlq_n_u64::<14>(t0)));
        y1 = veorq_u64(y1, veorq_u64(t1, vshlq_n_u64::<14>(t1)));
        y2 = veorq_u64(y2, veorq_u64(t2, vshlq_n_u64::<14>(t2)));
        y3 = veorq_u64(y3, veorq_u64(t3, vshlq_n_u64::<14>(t3)));

        // Round 3: distance 28.
        let t0 = vandq_u64(veorq_u64(y0, vshrq_n_u64::<28>(y0)), mask3);
        let t1 = vandq_u64(veorq_u64(y1, vshrq_n_u64::<28>(y1)), mask3);
        let t2 = vandq_u64(veorq_u64(y2, vshrq_n_u64::<28>(y2)), mask3);
        let t3 = vandq_u64(veorq_u64(y3, vshrq_n_u64::<28>(y3)), mask3);
        y0 = veorq_u64(y0, veorq_u64(t0, vshlq_n_u64::<28>(t0)));
        y1 = veorq_u64(y1, veorq_u64(t1, vshlq_n_u64::<28>(t1)));
        y2 = veorq_u64(y2, veorq_u64(t2, vshlq_n_u64::<28>(t2)));
        y3 = veorq_u64(y3, veorq_u64(t3, vshlq_n_u64::<28>(t3)));
        proof {
            lemma_three_swaps(u64x2(c0)[0]);
            lemma_three_swaps(u64x2(c0)[1]);
            lemma_three_swaps(u64x2(c1)[0]);
            lemma_three_swaps(u64x2(c1)[1]);
            lemma_three_swaps(u64x2(c2)[0]);
            lemma_three_swaps(u64x2(c2)[1]);
            lemma_three_swaps(u64x2(c3)[0]);
            lemma_three_swaps(u64x2(c3)[1]);
        }

        vst1q_u8_at(output, 0, vreinterpretq_u8_u64(y0));
        vst1q_u8_at(output, 16, vreinterpretq_u8_u64(y1));
        vst1q_u8_at(output, 32, vreinterpretq_u8_u64(y2));
        vst1q_u8_at(output, 48, vreinterpretq_u8_u64(y3));
        proof {
            lemma_neon_rows(*input, *output, 0, c0, y0);
            lemma_neon_rows(*input, *output, 1, c1, y1);
            lemma_neon_rows(*input, *output, 2, c2, y2);
            lemma_neon_rows(*input, *output, 3, c3, y3);
        }
    }
}

} // verus!
