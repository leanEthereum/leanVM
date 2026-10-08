//! Weighted sums of packed bit rows: the fold that turns witness bits into `E` values, and the GF(2)-linear
//! maps `E -> E` that ring switching applies.
//!
//! The executable functions are the portable paths of `crates/primitives/src/bit_fold.rs` and
//! `bit_fold/portable.rs`, copied with the same bodies where Verus accepts them;
//! `tests/equivalence/bit_fold.rs` checks the two agree.
//!
//! Specification: bit `s` of a row of bytes is bit `s % 8` of byte `s / 8`, and the fold of the row with
//! weights `w` is ([`fold_spec`])
//!
//! ```text
//!     fold(row) = sum_{s : bit s of row is set} w_s,
//! ```
//!
//! the sum in `E` ([`e_add`]). An `E` value has 192 coordinate bits, bit `b` being bit `b % 64` of coefficient
//! `b / 64`, and the map with weights `w` sends `x` to the sum of the weights of its set coordinate bits
//! ([`map_spec`]): every GF(2)-linear map `E -> E` is of this form, `w_b` being the image of the `b`-th
//! coordinate vector ([`unit`]).
use crate::bits::*;
use crate::gf2_64::*;
use crate::gf2_64x3::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------------------------
/// `w` if `set`, else zero.
pub open spec fn pick(set: bool, w: F192) -> F192 {
    if set {
        w
    } else {
        F192::ZERO
    }
}

/// `sum_{i < n : bit i of v} w[i]`: the subset sum of the weights of a byte.
pub open spec fn byte_sum(w: Seq<F192>, v: u8, n: nat) -> F192
    decreases n,
{
    if n == 0 {
        F192::ZERO
    } else {
        e_add(byte_sum(w, v, (n - 1) as nat), pick(bit8(v, n - 1), w[n - 1]))
    }
}

/// `sum_{s < n : bit s of row}  w[s]`, bit `s` of the row being bit `s % 8` of byte `s / 8`.
pub open spec fn row_sum(w: Seq<F192>, row: Seq<u8>, n: nat) -> F192
    decreases n,
{
    if n == 0 {
        F192::ZERO
    } else {
        e_add(row_sum(w, row, (n - 1) as nat), pick(bit8(row[(n - 1) / 8], (n - 1) % 8), w[n - 1]))
    }
}

/// The fold of a row: the sum of the weights of its set bits.
pub open spec fn fold_spec(w: Seq<F192>, row: Seq<u8>) -> F192 {
    row_sum(w, row, 8 * row.len())
}

/// Coefficient `q < 3` of `x`.
pub open spec fn coeff(x: F192, q: int) -> u64 {
    if q == 0 {
        x.c0
    } else if q == 1 {
        x.c1
    } else {
        x.c2
    }
}

/// Coordinate bit `b < 192` of `x`: bit `b % 64` of coefficient `b / 64`.
pub open spec fn coord(x: F192, b: int) -> bool {
    bit64(coeff(x, b / 64), b % 64)
}

/// `sum_{b < n : coordinate bit b of x} w[b]`.
pub open spec fn coord_sum(w: Seq<F192>, x: F192, n: nat) -> F192
    decreases n,
{
    if n == 0 {
        F192::ZERO
    } else {
        e_add(coord_sum(w, x, (n - 1) as nat), pick(coord(x, n - 1), w[n - 1]))
    }
}

/// The GF(2)-linear map `E -> E` sending coordinate bit `b` to `w[b]`.
pub open spec fn map_spec(w: Seq<F192>, x: F192) -> F192 {
    coord_sum(w, x, 192)
}

/// The coordinate vector `b`: coordinate bit `b` set, every other clear.
pub open spec fn unit(b: int) -> F192 {
    let one = 1u64 << ((b % 64) as u64);
    F192 {
        c0: if b / 64 == 0 { one } else { 0 },
        c1: if b / 64 == 1 { one } else { 0 },
        c2: if b / 64 == 2 { one } else { 0 },
    }
}

/// The 24 bytes of `x`: the little-endian bytes of `c0`, then `c1`, then `c2`.
pub open spec fn le_row(x: F192) -> Seq<u8> {
    Seq::new(24, |k: int| (coeff(x, k / 8) >> ((8 * (k % 8)) as u64)) as u8)
}

/// `sum_{j < n} tables[j][row[j]]`: what the byte tables add up.
pub open spec fn tables_fold(tables: Seq<[F192; 256]>, row: Seq<u8>, n: nat) -> F192
    decreases n,
{
    if n == 0 {
        F192::ZERO
    } else {
        e_add(tables_fold(tables, row, (n - 1) as nat), tables[n - 1][row[n - 1] as int])
    }
}

// ---------------------------------------------------------------------------------------------
// Sums in E
// ---------------------------------------------------------------------------------------------
proof fn lemma_xor_laws(x: u64, y: u64, z: u64)
    ensures
        x ^ y == y ^ x,
        (x ^ y) ^ z == x ^ (y ^ z),
        x ^ 0 == x,
        0 ^ x == x,
        x ^ x == 0,
{
    assert(x ^ y == y ^ x && (x ^ y) ^ z == x ^ (y ^ z) && x ^ 0 == x && 0 ^ x == x && x ^ x == 0) by (bit_vector);
}

/// `E` under `+` is an abelian group of exponent 2.
pub proof fn lemma_e_add_laws(a: F192, b: F192, c: F192)
    ensures
        e_add(a, b) == e_add(b, a),
        e_add(e_add(a, b), c) == e_add(a, e_add(b, c)),
        e_add(a, F192::ZERO) == a,
        e_add(F192::ZERO, a) == a,
        e_add(a, a) == F192::ZERO,
{
    lemma_xor_laws(a.c0, b.c0, c.c0);
    lemma_xor_laws(a.c1, b.c1, c.c1);
    lemma_xor_laws(a.c2, b.c2, c.c2);
}

/// `(a + b) + (c + d) = (a + c) + (b + d)`.
pub proof fn lemma_e_add_swap(a: F192, b: F192, c: F192, d: F192)
    ensures
        e_add(e_add(a, b), e_add(c, d)) == e_add(e_add(a, c), e_add(b, d)),
{
    assert(forall|x: u64, y: u64, z: u64, t: u64| #[trigger] ((x ^ y) ^ (z ^ t)) == (x ^ z) ^ (y ^ t))
        by (bit_vector);
}

/// `pick(p xor q, w) = pick(p, w) + pick(q, w)`.
proof fn lemma_pick_xor(p: bool, q: bool, w: F192)
    ensures
        pick(p != q, w) == e_add(pick(p, w), pick(q, w)),
{
    lemma_e_add_laws(w, F192::ZERO, F192::ZERO);
    lemma_e_add_laws(F192::ZERO, F192::ZERO, F192::ZERO);
}

// ---------------------------------------------------------------------------------------------
// The byte tables
// ---------------------------------------------------------------------------------------------
/// Clearing a set bit `t` of `v` removes `w[t]` from its subset sum.
pub proof fn lemma_byte_sum_clear(w: Seq<F192>, v: u8, t: u8, n: nat)
    requires
        t < 8,
        n <= 8,
        bit8(v, t as int),
    ensures
        byte_sum(w, v, n) == e_add(byte_sum(w, v ^ (1u8 << t), n), pick(t < n, w[t as int])),
    decreases n,
{
    let v2 = v ^ (1u8 << t);
    if n == 0 {
        lemma_e_add_laws(F192::ZERO, F192::ZERO, F192::ZERO);
    } else {
        let i = (n - 1) as nat;
        lemma_byte_sum_clear(w, v, t, i);
        let iu = i as u8;
        assert(t < 8 && iu < 8 ==> ((((v ^ (1u8 << t)) >> iu) & 1 == 1) <==> (((v >> iu) & 1 == 1) != (iu
            == t)))) by (bit_vector);
        let (s, s2) = (byte_sum(w, v, i), byte_sum(w, v2, i));
        let q = pick(t < i, w[t as int]);
        if i == t {
            // s + w_t = (s2 + 0) + w_t.
            lemma_e_add_laws(s2, F192::ZERO, w[t as int]);
            lemma_e_add_laws(s2, w[t as int], F192::ZERO);
        } else {
            let p = pick(bit8(v, i as int), w[i as int]);
            // (s2 + q) + p = (s2 + p) + q.
            lemma_e_add_laws(s2, q, p);
            lemma_e_add_laws(q, p, F192::ZERO);
            lemma_e_add_laws(s2, p, q);
        }
    }
}

/// The subset sum of the single bit `t` is `w[t]`.
pub proof fn lemma_byte_sum_monomial(w: Seq<F192>, t: u8, n: nat)
    requires
        t < 8,
        n <= 8,
    ensures
        byte_sum(w, 1u8 << t, n) == pick(t < n, w[t as int]),
    decreases n,
{
    if n == 0 {
    } else {
        let i = (n - 1) as nat;
        lemma_byte_sum_monomial(w, t, i);
        let iu = i as u8;
        assert(t < 8 && iu < 8 ==> ((((1u8 << t) >> iu) & 1 == 1) <==> (iu == t))) by (bit_vector);
        lemma_e_add_laws(pick(t < i, w[t as int]), F192::ZERO, F192::ZERO);
        lemma_e_add_laws(w[t as int], F192::ZERO, F192::ZERO);
    }
}

/// The subset sum depends only on the first `n` weights.
proof fn lemma_byte_sum_ext(w1: Seq<F192>, w2: Seq<F192>, v: u8, n: nat)
    requires
        forall|i: int| 0 <= i < n ==> w1[i] == w2[i],
    ensures
        byte_sum(w1, v, n) == byte_sum(w2, v, n),
    decreases n,
{
    if n > 0 {
        lemma_byte_sum_ext(w1, w2, v, (n - 1) as nat);
    }
}

// ---------------------------------------------------------------------------------------------
// Folds by byte
// ---------------------------------------------------------------------------------------------
/// The bits `8j .. 8j + i` of a row are bits `0 .. i` of byte `j`.
proof fn lemma_row_sum_byte(w: Seq<F192>, row: Seq<u8>, j: int, i: nat)
    requires
        0 <= j < row.len(),
        8 * j + 8 <= w.len(),
        i <= 8,
    ensures
        row_sum(w, row, (8 * j + i) as nat) == e_add(
            row_sum(w, row, (8 * j) as nat),
            byte_sum(w.subrange(8 * j, 8 * j + 8), row[j], i),
        ),
    decreases i,
{
    let base = row_sum(w, row, (8 * j) as nat);
    if i == 0 {
        lemma_e_add_laws(base, F192::ZERO, F192::ZERO);
    } else {
        let k = (i - 1) as nat;
        lemma_row_sum_byte(w, row, j, k);
        let s = 8 * j + k;
        assert(s / 8 == j && s % 8 == k) by (nonlinear_arith)
            requires
                s == 8 * j + k,
                0 <= k < 8,
                0 <= j,
        ;
        let p = pick(bit8(row[j], k as int), w[s]);
        assert(w.subrange(8 * j, 8 * j + 8)[k as int] == w[s]);
        lemma_e_add_laws(base, byte_sum(w.subrange(8 * j, 8 * j + 8), row[j], k), p);
    }
}

/// The byte tables of the weights `w` fold a row as [`fold_spec`] does.
pub proof fn lemma_tables_fold(tables: Seq<[F192; 256]>, w: Seq<F192>, row: Seq<u8>, n: nat)
    requires
        n <= row.len(),
        n <= tables.len(),
        8 * row.len() <= w.len(),
        forall|j: int, v: int|
            0 <= j < tables.len() && 0 <= v < 256 ==> #[trigger] tables[j][v] == byte_sum(
                w.subrange(8 * j, 8 * j + 8),
                v as u8,
                8,
            ),
    ensures
        tables_fold(tables, row, n) == row_sum(w, row, 8 * n),
    decreases n,
{
    if n > 0 {
        let j = n - 1;
        lemma_tables_fold(tables, w, row, (n - 1) as nat);
        lemma_row_sum_byte(w, row, j, 8);
        assert(tables[j][row[j] as int] == byte_sum(w.subrange(8 * j, 8 * j + 8), row[j], 8));
    }
}

// ---------------------------------------------------------------------------------------------
// The map on E
// ---------------------------------------------------------------------------------------------
/// Index arithmetic: bit `s % 8` of byte `s / 8` of [`le_row`] is coordinate bit `s`.
proof fn lemma_le_row_bit(x: F192, s: int)
    requires
        0 <= s < 192,
    ensures
        bit8(le_row(x)[s / 8], s % 8) == coord(x, s),
{
    let su = s as u64;
    assert(su < 192 ==> (su / 8) / 8 == su / 64 && su % 64 == 8 * ((su / 8) % 8) + su % 8) by (bit_vector);
    let (r, i) = (((s / 8) % 8) as u64, (s % 8) as u64);
    let c = coeff(x, s / 64);
    assert(r < 8 && i < 8 ==> ((((c >> (8 * r)) as u8) >> (i as u8)) & 1 == 1 <==> (c >> (8 * r + i)) & 1 == 1))
        by (bit_vector);
}

/// The fold of the bytes of `x` is the map of `x`.
pub proof fn lemma_row_sum_le_row(w: Seq<F192>, x: F192, n: nat)
    requires
        n <= 192,
    ensures
        row_sum(w, le_row(x), n) == coord_sum(w, x, n),
    decreases n,
{
    if n > 0 {
        lemma_row_sum_le_row(w, x, (n - 1) as nat);
        lemma_le_row_bit(x, n - 1);
    }
}

proof fn lemma_coeff_add(x: F192, y: F192, q: int)
    ensures
        coeff(e_add(x, y), q) == coeff(x, q) ^ coeff(y, q),
{
}

/// The map is GF(2)-linear: `map(x + y) = map(x) + map(y)`.
pub proof fn lemma_coord_sum_add(w: Seq<F192>, x: F192, y: F192, n: nat)
    ensures
        coord_sum(w, e_add(x, y), n) == e_add(coord_sum(w, x, n), coord_sum(w, y, n)),
    decreases n,
{
    if n == 0 {
        lemma_e_add_laws(F192::ZERO, F192::ZERO, F192::ZERO);
    } else {
        let b = n - 1;
        lemma_coord_sum_add(w, x, y, (n - 1) as nat);
        let (cx, cy) = (coeff(x, b / 64), coeff(y, b / 64));
        lemma_coeff_add(x, y, b / 64);
        let r = (b % 64) as u64;
        assert(((cx ^ cy) >> r) & 1 == 1 <==> (((cx >> r) & 1 == 1) != ((cy >> r) & 1 == 1))) by (bit_vector);
        lemma_pick_xor(coord(x, b), coord(y, b), w[b]);
        lemma_e_add_swap(
            coord_sum(w, x, (n - 1) as nat),
            coord_sum(w, y, (n - 1) as nat),
            pick(coord(x, b), w[b]),
            pick(coord(y, b), w[b]),
        );
    }
}

/// The map sends zero to zero.
pub proof fn lemma_coord_sum_zero(w: Seq<F192>, n: nat)
    ensures
        coord_sum(w, F192::ZERO, n) == F192::ZERO,
    decreases n,
{
    if n > 0 {
        lemma_coord_sum_zero(w, (n - 1) as nat);
        let r = ((n - 1) % 64) as u64;
        assert((0u64 >> r) & 1 != 1) by (bit_vector);
        lemma_e_add_laws(F192::ZERO, F192::ZERO, F192::ZERO);
    }
}

/// The coordinate bits below `n` of `x`, as an element.
pub open spec fn low_part(x: F192, n: nat) -> F192 {
    F192 {
        c0: crate::clmul::low(x.c0, if n < 64 { n } else { 64 }),
        c1: crate::clmul::low(x.c1, if n < 64 { 0 } else if n < 128 { (n - 64) as nat } else { 64 }),
        c2: crate::clmul::low(x.c2, if n < 128 { 0 } else { (n - 128) as nat }),
    }
}

/// `sum_{b < n : coordinate bit b of x} unit(b)` is the coordinate bits of `x` below `n`.
proof fn lemma_units_low_part(x: F192, n: nat)
    requires
        n <= 192,
    ensures
        coord_sum(Seq::new(192, |b: int| unit(b)), x, n) == low_part(x, n),
    decreases n,
{
    let units = Seq::new(192, |b: int| unit(b));
    assert(forall|a: u64| #[trigger] (a & ((1u64 << 0u64) - 1) as u64) == 0) by (bit_vector);
    if n == 0 {
        assert(crate::clmul::low(x.c0, 0) == 0 && crate::clmul::low(x.c1, 0) == 0 && crate::clmul::low(x.c2, 0)
            == 0);
    } else {
        let b = n - 1;
        lemma_units_low_part(x, b as nat);
        let (q, r) = (b / 64, b % 64);
        let prev = low_part(x, b as nat);
        crate::clmul::lemma_low_step(coeff(x, q), r as nat);
        lemma_xor_laws(prev.c0, 0, 0);
        lemma_xor_laws(prev.c1, 0, 0);
        lemma_xor_laws(prev.c2, 0, 0);
        assert(units[b] == unit(b));
        assert(e_add(prev, pick(coord(x, b), unit(b))) == low_part(x, n));
    }
}

/// Every element is the sum of the coordinate vectors of its set bits.
pub proof fn lemma_units_sum(x: F192)
    ensures
        map_spec(Seq::new(192, |b: int| unit(b)), x) == x,
{
    lemma_units_low_part(x, 192);
}

/// `(a + b) c = a c + b c` in `E`.
pub proof fn lemma_e_mul_add_left(a: F192, b: F192, c: F192)
    ensures
        e_mul(e_add(a, b), c) == e_add(e_mul(a, c), e_mul(b, c)),
{
    lemma_k_mul_xor_left(a.c0, b.c0, c.c0);
    lemma_k_mul_xor_left(a.c0, b.c0, c.c1);
    lemma_k_mul_xor_left(a.c0, b.c0, c.c2);
    lemma_k_mul_xor_left(a.c1, b.c1, c.c0);
    lemma_k_mul_xor_left(a.c1, b.c1, c.c1);
    lemma_k_mul_xor_left(a.c1, b.c1, c.c2);
    lemma_k_mul_xor_left(a.c2, b.c2, c.c0);
    lemma_k_mul_xor_left(a.c2, b.c2, c.c1);
    lemma_k_mul_xor_left(a.c2, b.c2, c.c2);
    let (a00, a01, a02) = (k_mul(a.c0, c.c0), k_mul(a.c0, c.c1), k_mul(a.c0, c.c2));
    let (a10, a11, a12) = (k_mul(a.c1, c.c0), k_mul(a.c1, c.c1), k_mul(a.c1, c.c2));
    let (a20, a21, a22) = (k_mul(a.c2, c.c0), k_mul(a.c2, c.c1), k_mul(a.c2, c.c2));
    let (b00, b01, b02) = (k_mul(b.c0, c.c0), k_mul(b.c0, c.c1), k_mul(b.c0, c.c2));
    let (b10, b11, b12) = (k_mul(b.c1, c.c0), k_mul(b.c1, c.c1), k_mul(b.c1, c.c2));
    let (b20, b21, b22) = (k_mul(b.c2, c.c0), k_mul(b.c2, c.c1), k_mul(b.c2, c.c2));
    // d0 + d3, d1 + d3 + d4, d2 + d4 of the sum are those of `a` plus those of `b`.
    assert((a00 ^ b00) ^ ((a12 ^ b12) ^ (a21 ^ b21)) == (a00 ^ (a12 ^ a21)) ^ (b00 ^ (b12 ^ b21))) by (bit_vector);
    assert(((a01 ^ b01) ^ (a10 ^ b10)) ^ ((a12 ^ b12) ^ (a21 ^ b21)) ^ (a22 ^ b22) == ((a01 ^ a10) ^ (a12 ^ a21)
        ^ a22) ^ ((b01 ^ b10) ^ (b12 ^ b21) ^ b22)) by (bit_vector);
    assert(((a02 ^ b02) ^ (a11 ^ b11) ^ (a20 ^ b20)) ^ (a22 ^ b22) == ((a02 ^ a11 ^ a20) ^ a22) ^ ((b02 ^ b11
        ^ b20) ^ b22)) by (bit_vector);
}

/// `0 c = 0` in `E`.
pub proof fn lemma_e_mul_zero_left(c: F192)
    ensures
        e_mul(F192::ZERO, c) == F192::ZERO,
{
    lemma_k_mul_zero(c.c0);
    lemma_k_mul_zero(c.c1);
    lemma_k_mul_zero(c.c2);
    assert(0u64 ^ 0u64 == 0u64 && 0u64 ^ 0u64 ^ 0u64 == 0u64) by (bit_vector);
}

/// The map with weights `w'_b = map(unit(b) c)`, on the coordinate bits below `n` of `x`, is `map` of
/// `low_part(x, n) c`.
proof fn lemma_after_mul_upto(w: Seq<F192>, c: F192, x: F192, n: nat)
    requires
        n <= 192,
    ensures
        coord_sum(Seq::new(192, |b: int| map_spec(w, e_mul(unit(b), c))), x, n) == map_spec(
            w,
            e_mul(coord_sum(Seq::new(192, |b: int| unit(b)), x, n), c),
        ),
    decreases n,
{
    let w2 = Seq::new(192, |b: int| map_spec(w, e_mul(unit(b), c)));
    let units = Seq::new(192, |b: int| unit(b));
    if n == 0 {
        lemma_e_mul_zero_left(c);
        lemma_coord_sum_zero(w, 192);
    } else {
        let b = n - 1;
        lemma_after_mul_upto(w, c, x, b as nat);
        let s = coord_sum(units, x, b as nat);
        let p = pick(coord(x, b), unit(b));
        assert(units[b] == unit(b));
        assert(w2[b] == map_spec(w, e_mul(unit(b), c)));
        lemma_e_mul_add_left(s, p, c);
        lemma_coord_sum_add(w, e_mul(s, c), e_mul(p, c), 192);
        if !coord(x, b) {
            lemma_e_mul_zero_left(c);
            lemma_coord_sum_zero(w, 192);
        }
    }
}

/// The map whose weights are `map(unit(b) c)` is `x -> map(x c)`: what `F192Map::after_mul` builds.
pub proof fn lemma_after_mul(w: Seq<F192>, c: F192, x: F192)
    ensures
        map_spec(Seq::new(192, |b: int| map_spec(w, e_mul(unit(b), c))), x) == map_spec(w, e_mul(x, c)),
{
    lemma_after_mul_upto(w, c, x, 192);
    lemma_units_sum(x);
}

// ---------------------------------------------------------------------------------------------
// Executable code: the portable arm, `crates/primitives/src/bit_fold/portable.rs`
// ---------------------------------------------------------------------------------------------
/// The fold of one row through the byte tables: one lookup and one XOR per byte.
///
/// Rewritten from `tables.try_into().expect("one table per byte")` and
/// `row.iter().zip(tables).fold(F192::ZERO, |acc, (&v, sums)| acc + sums[usize::from(v)])`: an index loop, the
/// length the `expect` checks a `requires`.
#[inline(always)]
fn fold_row_lookup<const CHUNKS: usize>(tables: &[[F192; 256]], row: &[u8; CHUNKS]) -> (r: F192)
    requires
        tables@.len() == CHUNKS,
    ensures
        r == tables_fold(tables@, row@, CHUNKS as nat),
{
    let mut acc = F192::ZERO;
    let mut j = 0;
    while j < CHUNKS
        invariant
            j <= CHUNKS,
            tables@.len() == CHUNKS,
            acc == tables_fold(tables@, row@, j as nat),
        decreases CHUNKS - j,
    {
        acc = acc + tables[j][usize::from(row[j])];
        j += 1;
    }
    acc
}

/// One 256-entry subset-sum table per byte of a row: entry `[j][v]` sums the weights of the set bits of `v` at byte `j`.
///
/// Rewritten from `weights.as_chunks::<8>().0.iter().map(..).collect()`: a loop over the whole chunks, pushing
/// each table. `v.isolate_lowest_one()` and `low.trailing_zeros()` (on `usize`, which `vstd` does not specify)
/// become `(v as u8).trailing_zeros()` and `1 << tz`, the same bit since `v < 256`.
fn lookup_tables(weights: &[F192]) -> (r: Vec<[F192; 256]>)
    ensures
        r@.len() == weights@.len() / 8,
        forall|j: int, v: int|
            0 <= j < r@.len() && 0 <= v < 256 ==> #[trigger] r@[j][v] == byte_sum(
                weights@.subrange(8 * j, 8 * j + 8),
                v as u8,
                8,
            ),
{
    let mut out: Vec<[F192; 256]> = Vec::new();
    let n = weights.len() / 8;
    let mut j = 0;
    while j < n
        invariant
            n == weights@.len() / 8,
            weights@.len() <= usize::MAX,
            j <= n,
            out@.len() == j,
            forall|j2: int, v: int|
                0 <= j2 < j && 0 <= v < 256 ==> #[trigger] out@[j2][v] == byte_sum(
                    weights@.subrange(8 * j2, 8 * j2 + 8),
                    v as u8,
                    8,
                ),
        decreases n - j,
    {
        let ghost w = weights@.subrange(8 * j, 8 * j + 8);
        let mut sums = [F192::ZERO; 256];
        assert(sums[0] == byte_sum(w, 0, 8)) by {
            assert((0u8 >> 0u8) & 1 != 1 && (0u8 >> 1u8) & 1 != 1 && (0u8 >> 2u8) & 1 != 1 && (0u8 >> 3u8) & 1 != 1
                && (0u8 >> 4u8) & 1 != 1 && (0u8 >> 5u8) & 1 != 1 && (0u8 >> 6u8) & 1 != 1 && (0u8 >> 7u8) & 1 != 1)
                by (bit_vector);
            reveal_with_fuel(byte_sum, 9);
            lemma_e_add_laws(F192::ZERO, F192::ZERO, F192::ZERO);
        }
        // Each entry adds its lowest set bit's weight to an entry already built.
        for v in 1..256usize
            invariant
                n == weights@.len() / 8,
                weights@.len() <= usize::MAX,
                j < n,
                w == weights@.subrange(8 * j, 8 * j + 8),
                forall|u: int| 0 <= u < v ==> #[trigger] sums[u] == byte_sum(w, u as u8, 8),
        {
            let tz = (v as u8).trailing_zeros() as usize;
            let low = 1usize << tz;
            proof {
                vstd::std_specs::bits::axiom_u8_trailing_zeros(v as u8);
                let (vb, t) = (v as u8, tz as u8);
                assert(vb != 0);
                assert(tz < 8 && t == tz as u8 && (vb >> t) & 1 == 1);
                assert(1 <= v < 256 && tz < 8 && t == tz as u8 && vb == v as u8 && (vb >> t) & 1 == 1 ==> (v ^ (1usize
                    << tz)) < v && (v ^ (1usize << tz)) as u8 == vb ^ (1u8 << t)) by (bit_vector);
                lemma_byte_sum_clear(w, vb, t, 8);
                assert(8 * j + 8 <= weights@.len());
                assert(w[t as int] == weights@[8 * j + t]);
            }
            sums[v] = sums[v ^ low] + weights[8 * j + tz];
        }
        out.push(sums);
        j += 1;
    }
    out
}

/// The byte tables.
#[derive(Clone, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Imp {
    /// One subset-sum table per byte of a row.
    tables: Vec<[F192; 256]>,
}

impl Imp {
    /// The weight of bit `s`: the entry of the single bit `s % 8` in table `s / 8`.
    pub closed spec fn weights(&self) -> Seq<F192> {
        Seq::new((8 * self.tables@.len()) as nat, |s: int| self.tables@[s / 8][(1u8 << ((s % 8) as u8)) as int])
    }

    /// Every table holds the subset sums of its weights.
    pub closed spec fn wf(&self) -> bool {
        forall|j: int, v: int|
            0 <= j < self.tables@.len() && 0 <= v < 256 ==> #[trigger] self.tables@[j][v] == byte_sum(
                self.weights().subrange(8 * j, 8 * j + 8),
                v as u8,
                8,
            )
    }

    /// Bytes per row.
    pub closed spec fn n_tables(&self) -> nat {
        self.tables@.len()
    }

    pub fn new(weights: &[F192]) -> (r: Self)
        ensures
            r.wf(),
            r.n_tables() == weights@.len() / 8,
            r.weights() == weights@.subrange(0, 8 * (weights@.len() / 8) as int),
    {
        let r = Self { tables: lookup_tables(weights) };
        proof {
            let n = weights@.len() / 8;
            let w = weights@.subrange(0, 8 * n as int);
            assert forall|s: int| 0 <= s < 8 * n implies #[trigger] r.weights()[s] == w[s] by {
                let (j, i) = (s / 8, s % 8);
                lemma_byte_sum_monomial(weights@.subrange(8 * j, 8 * j + 8), i as u8, 8);
            }
            assert(r.weights() =~= w);
            assert forall|j: int, v: int| 0 <= j < n && 0 <= v < 256 implies #[trigger] r.tables@[j][v] == byte_sum(
                r.weights().subrange(8 * j, 8 * j + 8),
                v as u8,
                8,
            ) by {
                assert(r.weights().subrange(8 * j, 8 * j + 8) =~= weights@.subrange(8 * j, 8 * j + 8));
            }
        }
        r
    }

    pub fn new_f192(weights: &[F192]) -> (r: Self)
        ensures
            r.wf(),
            r.n_tables() == weights@.len() / 8,
            r.weights() == weights@.subrange(0, 8 * (weights@.len() / 8) as int),
    {
        Self::new(weights)
    }

    /// Rewritten from `for (o, row) in out.iter_mut().zip(rows)`: an index loop to the shorter length.
    #[inline]
    pub fn fold_block<const CHUNKS: usize>(&self, rows: &[[u8; CHUNKS]], out: &mut [F192; BLOCK])
        requires
            self.wf(),
            self.n_tables() == CHUNKS,
        ensures
            forall|p: int|
                0 <= p < BLOCK && p < rows@.len() ==> #[trigger] final(out)[p] == fold_spec(self.weights(), rows@[p]@),
            forall|p: int| rows@.len() <= p < BLOCK ==> #[trigger] final(out)[p] == old(out)[p],
    {
        let mut p = 0;
        while p < BLOCK && p < rows.len()
            invariant
                self.wf(),
                self.n_tables() == CHUNKS,
                p <= BLOCK,
                p <= rows@.len(),
                forall|q: int| 0 <= q < p ==> #[trigger] out[q] == fold_spec(self.weights(), rows@[q]@),
                forall|q: int| p <= q < BLOCK ==> #[trigger] out[q] == old(out)[q],
            decreases BLOCK - p,
        {
            let o = fold_row_lookup(self.tables.as_slice(), &rows[p]);
            proof {
                lemma_tables_fold(self.tables@, self.weights(), rows@[p as int]@, CHUNKS as nat);
            }
            out[p] = o;
            p += 1;
        }
    }

    pub const fn slice(xs: &[F192; BLOCK]) -> (r: ImpSliced)
        ensures
            r == *xs,
    {
        *xs
    }

    #[inline]
    pub fn apply_sliced_add(&self, xs: &ImpSliced, out: &mut [F192])
        requires
            self.wf(),
            self.n_tables() == 24,
        ensures
            final(out).len() == old(out).len(),
            forall|p: int|
                0 <= p < old(out).len() && p < BLOCK ==> #[trigger] final(out)[p] == e_add(
                    old(out)[p],
                    map_spec(self.weights(), xs[p]),
                ),
            forall|p: int| BLOCK <= p < old(out).len() ==> #[trigger] final(out)[p] == old(out)[p],
    {
        self.apply_add_f192(xs, out);
    }

    /// Rewritten from `for (o, x) in out.iter_mut().zip(xs)`: an index loop to the shorter length; and from
    /// `row[..8].copy_from_slice(&x.c0.to_le_bytes())` (the same for `c1`, `c2`): a loop storing byte `k` of each
    /// coefficient, `vstd` specifying neither.
    #[inline]
    pub fn apply_add_f192(&self, xs: &[F192; BLOCK], out: &mut [F192])
        requires
            self.wf(),
            self.n_tables() == 24,
        ensures
            final(out).len() == old(out).len(),
            forall|p: int|
                0 <= p < old(out).len() && p < BLOCK ==> #[trigger] final(out)[p] == e_add(
                    old(out)[p],
                    map_spec(self.weights(), xs[p]),
                ),
            forall|p: int| BLOCK <= p < old(out).len() ==> #[trigger] final(out)[p] == old(out)[p],
    {
        let mut p = 0;
        while p < BLOCK && p < out.len()
            invariant
                self.wf(),
                self.n_tables() == 24,
                p <= BLOCK,
                p <= out.len(),
                out.len() == old(out).len(),
                forall|q: int|
                    0 <= q < p ==> #[trigger] out[q] == e_add(old(out)[q], map_spec(self.weights(), xs[q])),
                forall|q: int| p <= q < out.len() ==> #[trigger] out[q] == old(out)[q],
            decreases BLOCK - p,
        {
            let x = xs[p];
            let mut row = [0u8; 24];
            for k in 0..8
                invariant
                    forall|k2: int| 0 <= k2 < 24 && k2 % 8 < k ==> #[trigger] row[k2] == le_row(x)[k2],
            {
                row[k] = (x.c0 >> (8 * k as u64)) as u8;
                row[8 + k] = (x.c1 >> (8 * k as u64)) as u8;
                row[16 + k] = (x.c2 >> (8 * k as u64)) as u8;
            }
            assert(row@ =~= le_row(x));
            let image = fold_row_lookup(self.tables.as_slice(), &row);
            proof {
                lemma_tables_fold(self.tables@, self.weights(), row@, 24);
                lemma_row_sum_le_row(self.weights(), x, 192);
            }
            out[p] += image;
            p += 1;
        }
    }
}

/// A block of values, as they are: production's `portable::Sliced`, renamed since the two modules are one here.
pub type ImpSliced = [F192; BLOCK];

// ---------------------------------------------------------------------------------------------
// Executable code: `crates/primitives/src/bit_fold.rs`, on the portable arm
// ---------------------------------------------------------------------------------------------
/// Rows folded per call.
pub const BLOCK: usize = 64;

/// Production's row sizes: `n` bytes, `n` a power of two in `8..=128`.
pub open spec fn is_row_bytes(n: int) -> bool {
    n == 8 || n == 16 || n == 32 || n == 64 || n == 128
}

/// The weights of every bit of a row, prepared for folding.
#[derive(Clone, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct BitFold {
    /// Bytes per row.
    n_chunks: usize,
    /// The target's fold kernel data.
    imp: Imp,
}

impl BitFold {
    pub closed spec fn wf(&self) -> bool {
        self.imp.wf() && self.imp.n_tables() == self.n_chunks
    }

    /// The weight of every bit of a row.
    pub closed spec fn weights(&self) -> Seq<F192> {
        self.imp.weights()
    }

    pub closed spec fn spec_n_chunks(&self) -> usize {
        self.n_chunks
    }

    /// Prepare `weights`, one per bit of a row.
    ///
    /// Production's `assert!` that a row is 8 to 128 bytes, a power of two, is the `requires`: `vstd` specifies
    /// neither `is_power_of_two` nor `RangeInclusive::contains`.
    pub fn new(weights: &[F192]) -> (r: Self)
        requires
            weights@.len() % 8 == 0,
            is_row_bytes((weights@.len() / 8) as int),
        ensures
            r.wf(),
            r.weights() == weights@,
            r.spec_n_chunks() == weights@.len() / 8,
    {
        let n_chunks = weights.len() / 8;
        let r = Self { n_chunks, imp: Imp::new(weights) };
        assert(weights@.subrange(0, 8 * n_chunks as int) =~= weights@);
        r
    }

    /// Bytes per row.
    pub const fn n_chunks(&self) -> (r: usize)
        ensures
            r == self.spec_n_chunks(),
    {
        self.n_chunks
    }

    /// Fold up to 64 consecutive rows into `out[..rows.len()]`.
    ///
    /// Production's `debug_assert_eq!(CHUNKS, self.n_chunks)` and `assert!(rows.len() <= BLOCK)` are the
    /// `requires`.
    #[inline]
    pub fn fold_block<const CHUNKS: usize>(&self, rows: &[[u8; CHUNKS]], out: &mut [F192; BLOCK])
        requires
            self.wf(),
            CHUNKS == self.spec_n_chunks(),
            rows@.len() <= BLOCK,
        ensures
            forall|p: int|
                0 <= p < rows@.len() ==> #[trigger] final(out)[p] == fold_spec(self.weights(), rows@[p]@),
            forall|p: int| rows@.len() <= p < BLOCK ==> #[trigger] final(out)[p] == old(out)[p],
    {
        self.imp.fold_block(rows, out);
    }
}

/// A GF(2)-linear map from F192 to F192, given by the image of each of its 192 coordinate bits.
#[derive(Clone, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct F192Map {
    imp: Imp,
}

impl F192Map {
    pub closed spec fn wf(&self) -> bool {
        self.imp.wf() && self.imp.n_tables() == 24
    }

    /// The image of each coordinate bit.
    pub closed spec fn weights(&self) -> Seq<F192> {
        self.imp.weights()
    }

    /// The map sending coordinate bit `b` (bit `b % 64` of coefficient `b / 64`) to `weights[b]`.
    ///
    /// Production's `assert_eq!(weights.len(), 192)` is the `requires`.
    pub fn new(weights: &[F192]) -> (r: Self)
        requires
            weights@.len() == 192,
        ensures
            r.wf(),
            r.weights() == weights@,
    {
        let r = Self { imp: Imp::new_f192(weights) };
        assert(weights@.subrange(0, 192) =~= weights@);
        r
    }

    /// Add the image of each of `xs` to `out`.
    ///
    /// Production's `assert!(out.len() <= BLOCK)` is the `requires`.
    #[inline]
    pub fn apply_add(&self, xs: &[F192; BLOCK], out: &mut [F192])
        requires
            self.wf(),
            old(out).len() <= BLOCK,
        ensures
            final(out).len() == old(out).len(),
            forall|p: int|
                0 <= p < old(out).len() ==> #[trigger] final(out)[p] == e_add(
                    old(out)[p],
                    map_spec(self.weights(), xs[p]),
                ),
    {
        self.imp.apply_add_f192(xs, out);
    }

    /// The map `x -> self(x * c)`, itself GF(2)-linear.
    ///
    /// Rewritten from `weights.chunks_mut(BLOCK).enumerate()` and `std::array::from_fn`: index loops; each
    /// chunk's images are added into a zeroed `Vec` (as they are into the zeroed chunk) and copied to `weights`.
    pub fn after_mul(&self, c: F192) -> (r: Self)
        requires
            self.wf(),
        ensures
            r.wf(),
            r.weights() == Seq::new(192, |b: int| map_spec(self.weights(), e_mul(unit(b), c))),
            forall|x: F192| #[trigger] map_spec(r.weights(), x) == map_spec(self.weights(), e_mul(x, c)),
    {
        let ghost target = Seq::new(192, |b: int| map_spec(self.weights(), e_mul(unit(b), c)));
        let mut weights = [F192::ZERO; 192];
        let mut chunk = 0;
        while chunk < 3
            invariant
                self.wf(),
                chunk <= 3,
                target == Seq::new(192, |b: int| map_spec(self.weights(), e_mul(unit(b), c))),
                forall|b: int| 0 <= b < BLOCK * chunk ==> #[trigger] weights[b] == target[b],
            decreases 3 - chunk,
        {
            let mut xs = [F192::ZERO; BLOCK];
            for i in 0..BLOCK
                invariant
                    chunk < 3,
                    forall|i2: int| 0 <= i2 < i ==> #[trigger] xs[i2] == e_mul(unit(BLOCK * chunk + i2), c),
            {
                let bit = BLOCK * chunk + i;
                let mut words = [0u64; 3];
                words[bit / 64] = 1 << (bit % 64);
                assert((F192 { c0: words[0], c1: words[1], c2: words[2] }) == unit(bit as int));
                xs[i] = F192::new(words[0], words[1], words[2]) * c;
            }
            let mut w: Vec<F192> = Vec::new();
            for i in 0..BLOCK
                invariant
                    w@.len() == i,
                    forall|i2: int| 0 <= i2 < i ==> #[trigger] w@[i2] == F192::ZERO,
            {
                w.push(F192::ZERO);
            }
            self.apply_add(&xs, w.as_mut_slice());
            for i in 0..BLOCK
                invariant
                    chunk < 3,
                    w@.len() == BLOCK,
                    target == Seq::new(192, |b: int| map_spec(self.weights(), e_mul(unit(b), c))),
                    forall|i2: int|
                        0 <= i2 < BLOCK ==> #[trigger] w@[i2] == e_add(F192::ZERO, map_spec(self.weights(), xs[i2])),
                    forall|i2: int| 0 <= i2 < BLOCK ==> #[trigger] xs[i2] == e_mul(unit(BLOCK * chunk + i2), c),
                    forall|b: int| 0 <= b < BLOCK * chunk + i ==> #[trigger] weights[b] == target[b],
            {
                proof {
                    lemma_e_add_laws(map_spec(self.weights(), xs[i as int]), F192::ZERO, F192::ZERO);
                }
                weights[BLOCK * chunk + i] = w[i];
            }
            chunk += 1;
        }
        let r = Self::new(&weights);
        assert(r.weights() =~= target);
        assert forall|x: F192| #[trigger] map_spec(r.weights(), x) == map_spec(self.weights(), e_mul(x, c)) by {
            lemma_after_mul(self.weights(), c, x);
        }
        r
    }

    /// Add the image of each value of `xs` to `out`.
    ///
    /// Production's `assert!(out.len() <= BLOCK)` is the `requires`.
    #[inline]
    pub fn apply_sliced_add(&self, xs: &Sliced, out: &mut [F192])
        requires
            self.wf(),
            old(out).len() <= BLOCK,
        ensures
            final(out).len() == old(out).len(),
            forall|p: int|
                0 <= p < old(out).len() ==> #[trigger] final(out)[p] == e_add(
                    old(out)[p],
                    map_spec(self.weights(), xs.0[p]),
                ),
    {
        self.imp.apply_sliced_add(&xs.0, out);
    }
}

/// A block of values in the layout the map reads, so that a block mapped many times is transposed once.
///
/// Its field is public here (private in production) so that the specifications can name the block.
#[derive(Clone, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Sliced(pub ImpSliced);

impl Sliced {
    /// The block `xs`.
    pub fn new(xs: &[F192; BLOCK]) -> (r: Self)
        ensures
            r.0 == *xs,
    {
        Self(Imp::slice(xs))
    }
}

} // verus!
