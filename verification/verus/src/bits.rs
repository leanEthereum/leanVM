//! Bit transposes.
//!
//! The executable functions are the portable paths of `crates/primitives/src/bits.rs`; `tests/equivalence/bits.rs`
//! checks the two agree. Where Verus rejects the production form (`step_by`, const-generic inner functions,
//! `as_chunks_mut`, `array::from_fn`, `from_le_bytes`), the copy spells out the same arithmetic in `while`/`for`
//! loops; each such spot says what it replaces.
//!
//! Specification: a word is a row of bits, bit `i` of `x` being `(x >> i) & 1` ([`bit64`], [`bit8`]). Every
//! transpose is stated bit by bit: which input bit lands at which output bit.
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

/// Gather each byte column into a word, and transpose its bits.
///
/// ```text
///     output[b * 8 + t] bit x  =  input[x * 8 + b] bit t
/// ```
///
/// The production iterates `output.as_chunks_mut::<8>()`, gathers the column with
/// `u64::from_le_bytes(std::array::from_fn(|x| input[8 * x + b]))` and stores the row with `to_le_bytes`; the
/// copy spells out the same gather and store as loops over the bytes.
#[inline]
pub fn bit_transpose_64bytes_portable(input: &[u8; 64], output: &mut [u8; 64])
    ensures
        forall|b: int, t: int, x: int|
            0 <= b < 8 && 0 <= t < 8 && 0 <= x < 8 ==> #[trigger] bit8(final(output)[b * 8 + t], x) == bit8(
                input[x * 8 + b],
                t,
            ),
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
    }
}

} // verus!
