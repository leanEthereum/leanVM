//! BLAKE2s (RFC 7693): the compression, and the one-shot, streaming and continued hashes.
//!
//! The executable functions are the scalar code of `crates/primitives/src/hash/mod.rs`, copied with the same names
//! and bodies where Verus accepts them; `tests/equivalence/blake2s.rs` checks the copies against production. Each
//! rewrite Verus forces (index loops for `for` over tables and `as_chunks`, shifts for `from_le_bytes` and
//! `to_le_bytes`, a loop for `fill`, the IV's values in `PARAM_IV`) is noted at the function.
//!
//! Specification, a transcription of RFC 7693 independent of production's structure:
//!
//! - [`g_spec`]: the mixing function G with rotations 16, 12, 8, 7 ([`rotr`] is the RFC's `>>>`).
//! - [`sigma`], [`iv`]: the message schedule and the initialization vector; [`round_spec`]: G on the columns, then
//!   on the diagonals; [`rounds_spec`]: the ten rounds.
//! - [`f_spec`]: the compression F, from the work vector [`init_spec`] (counter in words 12 and 13, word 14
//!   inverted on the final block) to `h ^ v[0..8] ^ v[8..16]`.
//! - [`blake2s_spec`]: the unkeyed BLAKE2s-256 of a message: [`param_iv`], the zero-padded blocks
//!   ([`block_spec`], little-endian words), [`chain_spec`] over all blocks but the last, the last block at counter
//!   `ll` with the final flag, and the digest's 32 little-endian bytes ([`digest_spec`]).
//!
//! Main results: `compress`'s postcondition (`h' = F(h, m, t, last)`), `hash`'s and `Hasher::finalize`'s
//! (`blake2s_spec` of the bytes passed), `hash_from_state`'s, `zero_prefix_state`'s, and
//! [`lemma_zero_prefix_continuation`].
//!
//! Trusted: `u32::rotate_right`, which vstd does not specify, is the RFC's rotation for `0 < n < 32`
//! (`assume_specification`, checked by `rotate_right_is_the_rfc_rotation`).
#[cfg(verus_keep_ghost)]
use vstd::compute::RangeAll;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Specification: RFC 7693, transcribed
// ---------------------------------------------------------------------------------------------
/// `x >>> n`, rotation of a 32-bit word right by `n` bits (RFC 7693, section 2.3).
pub open spec fn rotr(x: u32, n: u32) -> u32 {
    (x >> n) ^ (x << sub(32, n))
}

/// `(x + y + z) mod 2^32`.
pub open spec fn add_mod(x: u32, y: u32, z: u32) -> u32 {
    ((x + y + z) % 0x1_0000_0000) as u32
}

/// The mixing function G (RFC 7693, section 3.1), with BLAKE2s's rotations `R1..R4 = 16, 12, 8, 7`.
///
/// Opaque: proofs above one G treat it as a function.
#[verifier::opaque]
pub open spec fn g_spec(v: Seq<u32>, a: int, b: int, c: int, d: int, x: u32, y: u32) -> Seq<u32> {
    let v = v.update(a, add_mod(v[a], v[b], x));
    let v = v.update(d, rotr(v[d] ^ v[a], 16));
    let v = v.update(c, add_mod(v[c], v[d], 0));
    let v = v.update(b, rotr(v[b] ^ v[c], 12));
    let v = v.update(a, add_mod(v[a], v[b], y));
    let v = v.update(d, rotr(v[d] ^ v[a], 8));
    let v = v.update(c, add_mod(v[c], v[d], 0));
    v.update(b, rotr(v[b] ^ v[c], 7))
}

/// The initialization vector (RFC 7693, section 2.6).
pub open spec fn iv() -> Seq<u32> {
    seq![
        0x6A09E667u32, 0xBB67AE85u32, 0x3C6EF372u32, 0xA54FF53Au32,
        0x510E527Fu32, 0x9B05688Cu32, 0x1F83D9ABu32, 0x5BE0CD19u32,
    ]
}

/// The message schedule SIGMA (RFC 7693, section 2.7).
pub open spec fn sigma(i: int) -> Seq<int> {
    if i == 0 {
        seq![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
    } else if i == 1 {
        seq![14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3]
    } else if i == 2 {
        seq![11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4]
    } else if i == 3 {
        seq![7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8]
    } else if i == 4 {
        seq![9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13]
    } else if i == 5 {
        seq![2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9]
    } else if i == 6 {
        seq![12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11]
    } else if i == 7 {
        seq![13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10]
    } else if i == 8 {
        seq![6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5]
    } else {
        seq![10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]
    }
}

/// Round `i` of the compression (RFC 7693, section 3.2): G on the four columns, then on the four diagonals.
pub open spec fn round_spec(v: Seq<u32>, m: Seq<u32>, i: int) -> Seq<u32> {
    let s = sigma(i % 10);
    let v = g_spec(v, 0, 4, 8, 12, m[s[0]], m[s[1]]);
    let v = g_spec(v, 1, 5, 9, 13, m[s[2]], m[s[3]]);
    let v = g_spec(v, 2, 6, 10, 14, m[s[4]], m[s[5]]);
    let v = g_spec(v, 3, 7, 11, 15, m[s[6]], m[s[7]]);
    let v = g_spec(v, 0, 5, 10, 15, m[s[8]], m[s[9]]);
    let v = g_spec(v, 1, 6, 11, 12, m[s[10]], m[s[11]]);
    let v = g_spec(v, 2, 7, 8, 13, m[s[12]], m[s[13]]);
    g_spec(v, 3, 4, 9, 14, m[s[14]], m[s[15]])
}

/// Rounds `0..n`.
pub open spec fn rounds_spec(v: Seq<u32>, m: Seq<u32>, n: nat) -> Seq<u32>
    decreases n,
{
    if n == 0 {
        v
    } else {
        round_spec(rounds_spec(v, m, (n - 1) as nat), m, n - 1)
    }
}

/// The local work vector at the start of F (RFC 7693, section 3.2): `h`, then the IV with the offset counter
/// `t` (`0 <= t < 2^64`) in words 12 and 13 and, on the final block (`f`), word 14 inverted.
pub open spec fn init_spec(h: Seq<u32>, t: int, f: bool) -> Seq<u32> {
    let v = h + iv();
    let v = v.update(12, v[12] ^ ((t % 0x1_0000_0000) as u32));
    let v = v.update(13, v[13] ^ ((t / 0x1_0000_0000) as u32));
    if f { v.update(14, v[14] ^ 0xFFFF_FFFFu32) } else { v }
}

/// The compression function F (RFC 7693, section 3.2): chaining value `h`, message block `m`, offset counter `t`,
/// final block flag `f`; ten rounds, then the two halves of the work vector folded into `h`.
///
/// Opaque: the message-level proofs treat F as a function, only the compression proofs look inside.
#[verifier::opaque]
pub open spec fn f_spec(h: Seq<u32>, m: Seq<u32>, t: int, f: bool) -> Seq<u32> {
    let v = rounds_spec(init_spec(h, t, f), m, 10);
    Seq::new(8, |i: int| h[i] ^ v[i] ^ v[i + 8])
}

/// Byte `k` of the message `d` padded with zeros (RFC 7693, section 3.3).
pub open spec fn padded_byte(d: Seq<u8>, k: int) -> u8 {
    if 0 <= k < d.len() { d[k] } else { 0 }
}

/// The 32-bit word of padded bytes `k..k + 4`, little-endian (RFC 7693, section 2.4).
pub open spec fn le_word(d: Seq<u8>, k: int) -> u32 {
    (padded_byte(d, k) as int + 0x100 * padded_byte(d, k + 1) + 0x1_0000 * padded_byte(d, k + 2) + 0x100_0000
        * padded_byte(d, k + 3)) as u32
}

/// Message block `d[i]`: the 16 words of padded bytes `64 i .. 64 i + 64` (RFC 7693, section 3.3).
pub open spec fn block_spec(d: Seq<u8>, i: int) -> Seq<u32> {
    Seq::new(16, |w: int| le_word(d, 64 * i + 4 * w))
}

/// The chaining value after blocks `0..k` of `d`, none final, from `h`: block `i` at counter `t0 + 64 (i + 1)`.
///
/// The RFC's loop over the blocks before the last one, with `t0 = 0`; a nonzero `t0` continues a message whose
/// first `t0` bytes are already absorbed into `h`.
pub open spec fn chain_spec(h: Seq<u32>, d: Seq<u8>, t0: int, k: nat) -> Seq<u32>
    decreases k,
{
    if k == 0 {
        h
    } else {
        f_spec(chain_spec(h, d, t0, (k - 1) as nat), block_spec(d, k - 1), t0 + 64 * k, false)
    }
}

/// The unkeyed BLAKE2s-256 parameter block in the IV: `h[0] ^= 0x01010000 ^ (kk << 8) ^ nn` with `kk = 0` and
/// `nn = 32` (RFC 7693, section 3.3).
pub open spec fn param_iv() -> Seq<u32> {
    iv().update(0, iv()[0] ^ 0x0101_0000u32 ^ (0u32 << 8u32) ^ 32u32)
}

/// The number of blocks `dd` of an unkeyed message of `ll` bytes: `ceil(ll / 64)`, and one for the empty message.
pub open spec fn block_count(ll: int) -> int {
    if ll == 0 { 1 } else { (ll + 63) / 64 }
}

/// Byte `j` (`0 <= j < 4`) of a word, little-endian (RFC 7693, section 2.4).
pub open spec fn word_byte(x: u32, j: int) -> u8 {
    if j == 0 {
        (x % 0x100) as u8
    } else if j == 1 {
        (x / 0x100 % 0x100) as u8
    } else if j == 2 {
        (x / 0x1_0000 % 0x100) as u8
    } else {
        (x / 0x100_0000 % 0x100) as u8
    }
}

/// The first `nn = 32` bytes of the little-endian word array `h`.
pub open spec fn digest_spec(h: Seq<u32>) -> Seq<u8> {
    Seq::new(32, |i: int| word_byte(h[i / 4], i % 4))
}

/// The finalization from chaining value `h` with `d` the message after the `t0` bytes already in `h`: the blocks
/// before the last, then the last at counter `t0 + ll` with the final flag, then the digest.
pub open spec fn finish_spec(h: Seq<u32>, d: Seq<u8>, t0: int) -> Seq<u8> {
    let dd = block_count(d.len() as int);
    let h = chain_spec(h, d, t0, (dd - 1) as nat);
    digest_spec(f_spec(h, block_spec(d, dd - 1), t0 + d.len(), true))
}

/// Unkeyed BLAKE2s-256 of the message `d` (`ll = d.len() < 2^64`; RFC 7693, section 3.3).
pub open spec fn blake2s_spec(d: Seq<u8>) -> Seq<u8> {
    finish_spec(param_iv(), d, 0)
}

// ---------------------------------------------------------------------------------------------
// Production constants and compression
// ---------------------------------------------------------------------------------------------
/// BLAKE2s initial values: the SHA-256 IV.
pub const IV: [u32; 8] = [
    0x6A09_E667,
    0xBB67_AE85,
    0x3C6E_F372,
    0xA54F_F53A,
    0x510E_527F,
    0x9B05_688C,
    0x1F83_D9AB,
    0x5BE0_CD19,
];

/// Digest length in bytes: BLAKE2s-256 throughout.
pub const OUT_LEN: usize = 32;
/// Compression block length in bytes.
pub const BLOCK_LEN: usize = 64;
/// Rounds per compression.
pub const ROUNDS: usize = 10;

/// BLAKE2s message schedule.
pub const SIGMA: [[usize; 16]; ROUNDS] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
];

/// Lanes touched by G index `g` within a round: `[a, b, c, d]`.
pub const G_LANES: [[usize; 4]; 8] = [
    [0, 4, 8, 12],
    [1, 5, 9, 13],
    [2, 6, 10, 14],
    [3, 7, 11, 15],
    [0, 5, 10, 15],
    [1, 6, 11, 12],
    [2, 7, 8, 13],
    [3, 4, 9, 14],
];

/// The unkeyed BLAKE2s-256 initial chaining value: the IV with the parameter block in word 0.
///
/// Hashing 64 bytes is one compression from here, at counter 64 with the final flag.
///
/// Verus form: production's `let mut h = IV; h[0] ^= ..; h` block is the array written out, with the IV's values (a
/// const's body must be a pure expression, and indexing `IV` is not).
pub const PARAM_IV: [u32; 8] = [
    // Digest length 32, key length 0, fanout 1, depth 1.
    0x6A09_E667 ^ 0x0101_0000 ^ OUT_LEN as u32,
    0xBB67_AE85,
    0x3C6E_F372,
    0xA54F_F53A,
    0x510E_527F,
    0x9B05_688C,
    0x1F83_D9AB,
    0x5BE0_CD19,
];

/// `u32::rotate_right`, which vstd does not specify: for `0 < n < 32` it is the RFC's rotation.
pub assume_specification[ u32::rotate_right ](x: u32, n: u32) -> (r: u32)
    requires
        0 < n < 32,
    ensures
        r == rotr(x, n),
;

/// The state lanes `[a, b, c, d]` of G number `g` in a round (RFC 7693, section 3.2).
pub open spec fn g_lanes(g: int) -> Seq<int> {
    if g == 0 {
        seq![0, 4, 8, 12]
    } else if g == 1 {
        seq![1, 5, 9, 13]
    } else if g == 2 {
        seq![2, 6, 10, 14]
    } else if g == 3 {
        seq![3, 7, 11, 15]
    } else if g == 4 {
        seq![0, 5, 10, 15]
    } else if g == 5 {
        seq![1, 6, 11, 12]
    } else if g == 6 {
        seq![2, 7, 8, 13]
    } else {
        seq![3, 4, 9, 14]
    }
}

/// G number `g` of round `i`.
pub open spec fn g_of_round(v: Seq<u32>, m: Seq<u32>, i: int, g: int) -> Seq<u32> {
    let l = g_lanes(g);
    let s = sigma(i % 10);
    g_spec(v, l[0], l[1], l[2], l[3], m[s[2 * g]], m[s[2 * g + 1]])
}

/// The first `g` G's of round `i`.
pub open spec fn round_prefix(v: Seq<u32>, m: Seq<u32>, i: int, g: int) -> Seq<u32>
    decreases g,
{
    if g <= 0 {
        v
    } else {
        g_of_round(round_prefix(v, m, i, g - 1), m, i, g - 1)
    }
}

proof fn lemma_round_prefix(v: Seq<u32>, m: Seq<u32>, i: int)
    ensures
        round_prefix(v, m, i, 8) == round_spec(v, m, i),
{
    reveal_with_fuel(round_prefix, 9);
}

/// The production tables `SIGMA` and `G_LANES` are the RFC's.
proof fn lemma_tables()
    ensures
        forall|i: int, j: int| 0 <= i < 10 && 0 <= j < 16 ==> (#[trigger] SIGMA[i][j]) as int == sigma(i)[j] && SIGMA[i][j] < 16,
        forall|g: int, j: int| 0 <= g < 8 && 0 <= j < 4 ==> (#[trigger] G_LANES[g][j]) as int == g_lanes(g)[j] && G_LANES[g][j] < 16,
{
    assert((0..10int).all_spec(|i: int| (0..16int).all_spec(|j: int| SIGMA[i][j] as int == sigma(i)[j] && SIGMA[i][j] < 16))) by (compute);
    assert((0..8int).all_spec(|g: int| (0..4int).all_spec(|j: int| G_LANES[g][j] as int == g_lanes(g)[j] && G_LANES[g][j] < 16))) by (compute);
    broadcast use vstd::compute::all_spec_ensures;
}

/// Two wrapping additions are one addition modulo `2^32`.
pub broadcast proof fn lemma_add_mod3(x: u32, y: u32, z: u32)
    ensures
        #[trigger] vstd::wrapping::u32_specs::wrapping_add(vstd::wrapping::u32_specs::wrapping_add(x, y), z) == add_mod(x, y, z),
{
}

/// A wrapping addition is an addition modulo `2^32`.
pub broadcast proof fn lemma_add_mod2(x: u32, y: u32)
    ensures
        #[trigger] vstd::wrapping::u32_specs::wrapping_add(x, y) == add_mod(x, y, 0),
{
}

/// XOR associates.
pub proof fn lemma_xor3(a: u32, b: u32, c: u32)
    by (bit_vector)
    ensures
        a ^ (b ^ c) == a ^ b ^ c,
{
}

/// Bitwise not is the RFC's XOR with all ones.
pub proof fn lemma_not_is_xor(x: u32)
    by (bit_vector)
    ensures
        !x == x ^ 0xFFFF_FFFFu32,
{
}

/// The two halves of the counter are its residue and quotient modulo `2^32`.
pub proof fn lemma_cast_t(t: u64)
    ensures
        t as u32 == (t as int % 0x1_0000_0000) as u32,
        (t >> 32) as u32 == (t as int / 0x1_0000_0000) as u32,
{
    assert(t as u32 == (t % 0x1_0000_0000u64) as u32 && t >> 32 == t / 0x1_0000_0000u64) by (bit_vector);
}

/// The BLAKE2s compression: absorb block `m` at byte counter `t` into `h`.
///
/// `last` sets the final-block flag.
///
/// The last-node flag stays zero: nothing here uses the tree mode.
///
/// Verus form: the `for` loops over `&SIGMA` and `G_LANES.iter().enumerate()` are index loops, and the
/// destructuring of `G_LANES[g]` is indexing.
pub fn compress(h: &mut [u32; 8], m: &[u32; 16], t: u64, last: bool)
    ensures
        final(h)@ == f_spec(old(h)@, m@, t as int, last),
{
    let mut v = [0u32; 16];
    v[..8].copy_from_slice(h);
    v[8..].copy_from_slice(&IV);
    v[12] ^= t as u32;
    v[13] ^= (t >> 32) as u32;
    if last {
        v[14] = !v[14];
    }
    let ghost v0 = v@;
    proof {
        lemma_cast_t(t);
        lemma_not_is_xor(IV[6]);
        assert(IV@ =~= iv());
        assert(v0 =~= init_spec(old(h)@, t as int, last));
    }
    for r in 0..ROUNDS
        invariant
            v0 == init_spec(old(h)@, t as int, last),
            v@ == rounds_spec(v0, m@, r as nat),
    {
        let round = &SIGMA[r];
        let ghost vr = v@;
        for g in 0..8
            invariant
                0 <= r < 10,
                round == &SIGMA[r as int],
                vr == rounds_spec(v0, m@, r as nat),
                v0 == init_spec(old(h)@, t as int, last),
                v@ == round_prefix(vr, m@, r as int, g as int),
        {
            proof {
                lemma_tables();
            }
            let (a, b, c, d) = (G_LANES[g][0], G_LANES[g][1], G_LANES[g][2], G_LANES[g][3]);
            let (mx, my) = (m[round[2 * g]], m[round[2 * g + 1]]);
            let ghost vg = v@;
            v[a] = v[a].wrapping_add(v[b]).wrapping_add(mx);
            v[d] = (v[d] ^ v[a]).rotate_right(16);
            v[c] = v[c].wrapping_add(v[d]);
            v[b] = (v[b] ^ v[c]).rotate_right(12);
            v[a] = v[a].wrapping_add(v[b]).wrapping_add(my);
            v[d] = (v[d] ^ v[a]).rotate_right(8);
            v[c] = v[c].wrapping_add(v[d]);
            v[b] = (v[b] ^ v[c]).rotate_right(7);
            proof {
                broadcast use lemma_add_mod3, lemma_add_mod2;
                reveal(g_spec);
                assert(v@ =~= g_of_round(vg, m@, r as int, g as int));
            }
        }
        proof {
            lemma_round_prefix(vr, m@, r as int);
        }
    }
    let ghost vf = v@;
    for i in 0..8
        invariant
            v@ == vf,
            forall|j: int| 0 <= j < i ==> #[trigger] h[j] == old(h)[j] ^ vf[j] ^ vf[j + 8],
            forall|j: int| i <= j < 8 ==> h[j] == old(h)[j],
    {
        h[i] ^= v[i] ^ v[i + 8];
        proof {
            lemma_xor3(old(h)[i as int], vf[i as int], vf[i + 8]);
        }
    }
    proof {
        reveal(f_spec);
    }
    assert(h@ =~= f_spec(old(h)@, m@, t as int, last));
}

// ---------------------------------------------------------------------------------------------
// Messages: blocks, chaining and continuation
// ---------------------------------------------------------------------------------------------
/// Two blocks with the same padded bytes are the same words.
pub proof fn lemma_block_eq(a: Seq<u8>, i: int, b: Seq<u8>, j: int)
    requires
        forall|x: int| 64 * i <= x < 64 * i + 64 ==> #[trigger] padded_byte(a, x) == padded_byte(b, x + 64 * (j - i)),
    ensures
        block_spec(a, i) == block_spec(b, j),
{
    assert forall|w: int| 0 <= w < 16 implies #[trigger] le_word(a, 64 * i + 4 * w) == le_word(b, 64 * j + 4 * w) by {
        assert(padded_byte(a, 64 * i + 4 * w) == padded_byte(b, 64 * j + 4 * w));
        assert(padded_byte(a, 64 * i + 4 * w + 1) == padded_byte(b, 64 * j + 4 * w + 1));
        assert(padded_byte(a, 64 * i + 4 * w + 2) == padded_byte(b, 64 * j + 4 * w + 2));
        assert(padded_byte(a, 64 * i + 4 * w + 3) == padded_byte(b, 64 * j + 4 * w + 3));
    }
    assert(block_spec(a, i) =~= block_spec(b, j));
}

/// The chaining value after `k` blocks depends on the first `64 k` bytes only.
pub proof fn lemma_chain_prefix(h: Seq<u32>, a: Seq<u8>, b: Seq<u8>, t0: int, k: nat)
    requires
        forall|x: int| 0 <= x < 64 * k ==> #[trigger] padded_byte(a, x) == padded_byte(b, x),
    ensures
        chain_spec(h, a, t0, k) == chain_spec(h, b, t0, k),
    decreases k,
{
    if k > 0 {
        lemma_chain_prefix(h, a, b, t0, (k - 1) as nat);
        lemma_block_eq(a, k - 1, b, k - 1);
    }
}

/// Chaining over `a + b`, `a` being `ka` whole blocks, is chaining over `a` then over `b` from counter `64 ka`.
pub proof fn lemma_chain_concat(h: Seq<u32>, a: Seq<u8>, b: Seq<u8>, t0: int, ka: nat, k: nat)
    requires
        a.len() == 64 * ka,
    ensures
        chain_spec(h, a + b, t0, ka + k) == chain_spec(chain_spec(h, a, t0, ka), b, t0 + 64 * ka, k),
    decreases k,
{
    if k == 0 {
        assert forall|x: int| 0 <= x < 64 * ka implies #[trigger] padded_byte(a + b, x) == padded_byte(a, x) by {}
        lemma_chain_prefix(h, a + b, a, t0, ka);
    } else {
        lemma_chain_concat(h, a, b, t0, ka, (k - 1) as nat);
        assert forall|x: int| 64 * (ka + k - 1) <= x < 64 * (ka + k - 1) + 64 implies #[trigger] padded_byte(a + b, x)
            == padded_byte(b, x + 64 * ((k - 1) - (ka + k - 1))) by {}
        lemma_block_eq(a + b, ka + k - 1, b, k - 1);
        assert(((ka + k) - 1) as nat == ka + (k - 1) as nat);
    }
}

/// Continuation: finishing `a + b` from `h`, `a` being `ka` whole blocks and `b` not empty, is finishing `b` from the
/// chaining value after `a`, at counter offset `64 ka`.
pub proof fn lemma_finish_concat(h: Seq<u32>, a: Seq<u8>, b: Seq<u8>, t0: int, ka: nat)
    requires
        a.len() == 64 * ka,
        b.len() > 0,
    ensures
        finish_spec(h, a + b, t0) == finish_spec(chain_spec(h, a, t0, ka), b, t0 + 64 * ka),
{
    let db = block_count(b.len() as int);
    let dab = block_count((a + b).len() as int);
    assert(dab == ka + db);
    lemma_chain_concat(h, a, b, t0, ka, (db - 1) as nat);
    assert((dab - 1) as nat == ka + (db - 1) as nat);
    assert forall|x: int| 64 * (dab - 1) <= x < 64 * (dab - 1) + 64 implies #[trigger] padded_byte(a + b, x)
        == padded_byte(b, x + 64 * ((db - 1) - (dab - 1))) by {}
    lemma_block_eq(a + b, dab - 1, b, db - 1);
}

/// `n` zero bytes.
pub open spec fn zeros(n: nat) -> Seq<u8> {
    Seq::new(n, |i: int| 0u8)
}

/// The claim of `zero_prefix_state`'s doc: continuing from the chaining value after `z` zero blocks, at counter
/// offset `64 z`, gives the hash of the whole image, the `64 z` zero bytes then `rest` (not empty).
pub proof fn lemma_zero_prefix_continuation(z: nat, rest: Seq<u8>)
    requires
        rest.len() > 0,
    ensures
        finish_spec(chain_spec(param_iv(), zeros(64 * z), 0, z), rest, 64 * z as int) == blake2s_spec(zeros(64 * z) + rest),
{
    lemma_finish_concat(param_iv(), zeros(64 * z), rest, 0, z);
}

// ---------------------------------------------------------------------------------------------
// Production: bytes, the one-shot and streaming hashes
// ---------------------------------------------------------------------------------------------
/// Four bytes assembled with shifts are their little-endian word.
proof fn lemma_le_word(b0: u8, b1: u8, b2: u8, b3: u8)
    ensures
        (b0 as u32 | (b1 as u32) << 8u32 | (b2 as u32) << 16u32 | (b3 as u32) << 24u32) == (b0 as int + 0x100 * b1
            + 0x1_0000 * b2 + 0x100_0000 * b3) as u32,
{
    assert((b0 as u32 | (b1 as u32) << 8u32 | (b2 as u32) << 16u32 | (b3 as u32) << 24u32) == add(
        add(add(b0 as u32, mul(b1 as u32, 0x100u32)), mul(b2 as u32, 0x1_0000u32)),
        mul(b3 as u32, 0x100_0000u32),
    )) by (bit_vector);
}

/// The four bytes of a word, by shifts and truncation.
proof fn lemma_word_bytes(x: u32)
    ensures
        x as u8 == word_byte(x, 0),
        (x >> 8u32) as u8 == word_byte(x, 1),
        (x >> 16u32) as u8 == word_byte(x, 2),
        (x >> 24u32) as u8 == word_byte(x, 3),
{
    assert(x as u8 == (x % 0x100) as u8 && (x >> 8u32) as u8 == (x / 0x100 % 0x100) as u8 && (x >> 16u32) as u8 == (x
        / 0x1_0000 % 0x100) as u8 && (x >> 24u32) as u8 == (x / 0x100_0000 % 0x100) as u8) by (bit_vector);
}

/// Read a 64-byte block as 16 little-endian words.
///
/// Verus form: `array::from_fn` over `u32::from_le_bytes(block[4 * i..4 * i + 4].try_into().unwrap())` is an index
/// loop assembling each word from its four bytes with shifts.
pub fn block_words(block: &[u8; BLOCK_LEN]) -> (words: [u32; 16])
    ensures
        words@ == block_spec(block@, 0),
{
    let mut words = [0u32; 16];
    for i in 0..16
        invariant
            forall|j: int| 0 <= j < i ==> #[trigger] words[j] == le_word(block@, 4 * j),
    {
        words[i] = block[4 * i] as u32 | (block[4 * i + 1] as u32) << 8 | (block[4 * i + 2] as u32) << 16
            | (block[4 * i + 3] as u32) << 24;
        proof {
            lemma_le_word(block[4 * i as int], block[4 * i + 1], block[4 * i + 2], block[4 * i + 3]);
        }
    }
    assert(words@ =~= block_spec(block@, 0));
    words
}

/// Serialize a chaining value as the 32-byte digest.
///
/// Verus form: the loop over `out.as_chunks_mut::<4>()` zipped with `h`, storing `word.to_le_bytes()`, is an index
/// loop writing each word's four bytes with shifts.
pub fn state_bytes(h: &[u32; 8]) -> (out: [u8; OUT_LEN])
    ensures
        out@ == digest_spec(h@),
{
    let mut out = [0u8; OUT_LEN];
    for i in 0..8
        invariant
            forall|j: int| 0 <= j < 4 * i ==> #[trigger] out[j] == word_byte(h[j / 4], j % 4),
    {
        out[4 * i] = h[i] as u8;
        out[4 * i + 1] = (h[i] >> 8) as u8;
        out[4 * i + 2] = (h[i] >> 16) as u8;
        out[4 * i + 3] = (h[i] >> 24) as u8;
        proof {
            lemma_word_bytes(h[i as int]);
        }
    }
    assert(out@ =~= digest_spec(h@));
    out
}

/// `PARAM_IV` is the RFC's parameter block XORed into the IV.
proof fn lemma_param_iv()
    ensures
        PARAM_IV@ == param_iv(),
{
    assert(0x6A09_E667u32 ^ 0x0101_0000u32 ^ 32u32 == 0x6A09_E667u32 ^ 0x0101_0000u32 ^ (0u32 << 8u32) ^ 32u32)
        by (bit_vector);
    assert(PARAM_IV@ =~= param_iv());
}

/// One step of the whole-block loop of `hash` and `hash_from_state`: compressing block `b` of `n` gives the chaining
/// value after `b + 1` blocks, or the final one after the last.
pub open spec fn whole_blocks_state(h: Seq<u32>, d: Seq<u8>, t0: int, b: nat) -> Seq<u32> {
    if b * 64 < d.len() {
        chain_spec(h, d, t0, b)
    } else {
        f_spec(chain_spec(h, d, t0, (b - 1) as nat), block_spec(d, b - 1), t0 + 64 * b, true)
    }
}

/// The block of a whole-block message copied out of it is that block.
proof fn lemma_copied_block(d: Seq<u8>, b: int, block: Seq<u8>)
    requires
        0 <= b,
        64 * b + 64 <= d.len(),
        block == d.subrange(64 * b, 64 * b + 64),
    ensures
        block_spec(block, 0) == block_spec(d, b),
{
    assert forall|x: int| 64 * 0 <= x < 64 * 0 + 64 implies #[trigger] padded_byte(block, x) == padded_byte(d, x + 64 * (b - 0)) by {}
    lemma_block_eq(block, 0, d, b);
}

/// One-shot unkeyed BLAKE2s-256.
///
/// Verus form: the loop over `data.as_chunks::<BLOCK_LEN>()` with `enumerate` is an index loop that copies block `b`
/// into an array with `copy_from_slice`.
pub fn hash(data: &[u8]) -> (digest: [u8; OUT_LEN])
    ensures
        digest@ == blake2s_spec(data@),
{
    // Whole blocks, the shape hashed in bulk, need no buffering.
    if !data.is_empty() && data.len().is_multiple_of(BLOCK_LEN) {
        let mut h = PARAM_IV;
        let n = data.len() / BLOCK_LEN;
        proof {
            lemma_param_iv();
        }
        for b in 0..n
            invariant
                n * 64 == data.len(),
                n > 0,
                h@ == whole_blocks_state(param_iv(), data@, 0, b as nat),
        {
            let mut block = [0u8; BLOCK_LEN];
            block.copy_from_slice(&data[b * BLOCK_LEN..(b + 1) * BLOCK_LEN]);
            let t = ((b + 1) * BLOCK_LEN) as u64;
            proof {
                lemma_copied_block(data@, b as int, block@);
            }
            compress(&mut h, &block_words(&block), t, b + 1 == n);
        }
        return state_bytes(&h);
    }
    let mut hasher = Hasher::new();
    hasher.update(data);
    hasher.finalize()
}

/// Streaming BLAKE2s-256.
///
/// The final block carries the final flag, so a full buffer is held back until more input arrives.
///
/// Verus form: the ghost field `msg` is added for the proof; it is erased from the compiled struct.
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Hasher {
    h: [u32; 8],
    buf: [u8; BLOCK_LEN],
    /// Bytes currently in `buf`, in `0..=BLOCK_LEN`.
    buf_len: usize,
    /// Bytes already compressed.
    counter: u64,
    /// Every byte passed to `update` so far.
    msg: Ghost<Seq<u8>>,
}

impl Hasher {
    /// The bytes passed to `update` so far.
    pub closed spec fn absorbed(&self) -> Seq<u8> {
        self.msg@
    }

    /// The streaming invariant: the absorbed bytes are the compressed blocks (whole, counted by `counter`, chained
    /// into `h`) then the `buf_len` buffered bytes, at least one once anything is absorbed.
    pub closed spec fn wf(&self) -> bool {
        let msg = self.msg@;
        &&& self.buf_len <= BLOCK_LEN
        &&& msg.len() == self.counter + self.buf_len
        &&& msg.len() < 0x1_0000_0000_0000_0000
        &&& self.counter % 64 == 0
        &&& msg.len() > 0 ==> self.buf_len > 0
        &&& self.h@ == chain_spec(param_iv(), msg, 0, (self.counter / 64) as nat)
        &&& forall|j: int| 0 <= j < self.buf_len ==> #[trigger] self.buf[j] == msg[self.counter + j]
    }

    pub const fn new() -> (hasher: Self)
        ensures
            hasher.wf(),
            hasher.absorbed() == Seq::<u8>::empty(),
    {
        proof {
            lemma_param_iv();
        }
        Self { h: PARAM_IV, buf: [0u8; BLOCK_LEN], buf_len: 0, counter: 0, msg: Ghost(Seq::empty()) }
    }

    /// The total length stays below `2^64`, the range of the RFC's counter.
    ///
    /// The returned reference is `self`, for chaining: the hasher's final value is the one left behind it.
    pub fn update(&mut self, mut data: &[u8]) -> (this: &mut Self)
        requires
            old(self).wf(),
            old(self).absorbed().len() + data.len() < 0x1_0000_0000_0000_0000,
        ensures
            this.wf(),
            this.absorbed() == old(self).absorbed() + data@,
            *final(this) == *final(self),
    {
        let ghost total = self.msg@ + data@;
        while !data.is_empty()
            invariant
                self.wf(),
                self.msg@ + data@ == total,
                total.len() < 0x1_0000_0000_0000_0000,
            decreases data.len(),
        {
            if self.buf_len == BLOCK_LEN {
                // More input follows, so this buffered block is not the last.
                let ghost msg = self.msg@;
                proof {
                    assert forall|x: int| 64 * 0 <= x < 64 * 0 + 64 implies #[trigger] padded_byte(self.buf@, x)
                        == padded_byte(msg, x + 64 * (self.counter / 64 - 0)) by {}
                    lemma_block_eq(self.buf@, 0, msg, self.counter as int / 64);
                }
                self.counter += BLOCK_LEN as u64;
                compress(&mut self.h, &block_words(&self.buf), self.counter, false);
                self.buf_len = 0;
            }
            let take = (BLOCK_LEN - self.buf_len).min(data.len());
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            let ghost old_msg = self.msg@;
            self.msg = Ghost(self.msg@ + data@.subrange(0, take as int));
            proof {
                assert forall|x: int| 0 <= x < 64 * (self.counter / 64) implies #[trigger] padded_byte(old_msg, x)
                    == padded_byte(self.msg@, x) by {}
                lemma_chain_prefix(param_iv(), old_msg, self.msg@, 0, (self.counter / 64) as nat);
            }
            data = &data[take..];
        }
        self
    }

    /// Verus form: `block[self.buf_len..].fill(0)` is a loop.
    pub fn finalize(&self) -> (digest: [u8; OUT_LEN])
        requires
            self.wf(),
        ensures
            digest@ == blake2s_spec(self.absorbed()),
    {
        let mut h = self.h;
        let mut block = self.buf;
        let mut i = self.buf_len;
        while i < BLOCK_LEN
            invariant
                self.buf_len <= i <= BLOCK_LEN,
                forall|j: int| 0 <= j < self.buf_len ==> #[trigger] block[j] == self.buf[j],
                forall|j: int| self.buf_len <= j < i ==> #[trigger] block[j] == 0,
            decreases BLOCK_LEN - i,
        {
            block[i] = 0;
            i += 1;
        }
        let t = self.counter + self.buf_len as u64;
        let ghost msg = self.msg@;
        proof {
            let k = self.counter as int / 64;
            assert(block_count(msg.len() as int) - 1 == k);
            assert forall|x: int| 64 * 0 <= x < 64 * 0 + 64 implies #[trigger] padded_byte(block@, x)
                == padded_byte(msg, x + 64 * (k - 0)) by {}
            lemma_block_eq(block@, 0, msg, k);
        }
        compress(&mut h, &block_words(&block), t, true);
        state_bytes(&h)
    }
}

/// The chaining value after `n_blocks` all-zero blocks from the unkeyed IV.
///
/// PCS leaves share such a prefix, their absent interleaving lanes.
///
/// The committer absorbs it once and starts every leaf here.
///
/// Digests are unchanged: a prefix's compressions depend on nothing after them ([`lemma_zero_prefix_continuation`]).
pub fn zero_prefix_state(n_blocks: usize) -> (h: [u32; 8])
    requires
        n_blocks * 64 <= usize::MAX,
    ensures
        h@ == chain_spec(param_iv(), zeros(64 * n_blocks as nat), 0, n_blocks as nat),
{
    let mut h = PARAM_IV;
    proof {
        lemma_param_iv();
    }
    for b in 0..n_blocks
        invariant
            n_blocks * 64 <= usize::MAX,
            h@ == chain_spec(param_iv(), zeros(64 * n_blocks as nat), 0, b as nat),
    {
        proof {
            let z = zeros(64 * n_blocks as nat);
            assert forall|w: int| 0 <= w < 16 implies #[trigger] le_word(z, 64 * b + 4 * w) == 0 by {}
            // The spec of the exec array `[0u32; 16]`.
            let zero = vstd::array::spec_array_fill_for_copy_type::<u32, 16>(0u32);
            assert(zero@.len() == 16);
            assert(block_spec(z, b as int) =~= zero@);
        }
        compress(&mut h, &[0u32; 16], ((b + 1) * BLOCK_LEN) as u64, false);
    }
    h
}

/// The one-shot hash, continued from a chaining value.
///
/// - `data` is the rest of the image, a nonzero whole number of blocks.
/// - `t_offset` counts the bytes already absorbed into `state`.
///
/// Verus form: the `assert!` on `data` is a `requires`, as is the counter's range; the loop over
/// `data.as_chunks::<BLOCK_LEN>()` with `enumerate` is an index loop copying block `b` out with `copy_from_slice`.
pub fn hash_from_state(data: &[u8], state: &[u32; 8], t_offset: u64) -> (digest: [u8; OUT_LEN])
    requires
        data.len() > 0 && data.len() % 64 == 0,
        t_offset + data.len() < 0x1_0000_0000_0000_0000,
    ensures
        digest@ == finish_spec(state@, data@, t_offset as int),
{
    let mut h = *state;
    let n = data.len() / BLOCK_LEN;
    for b in 0..n
        invariant
            n * 64 == data.len(),
            n > 0,
            t_offset + data.len() < 0x1_0000_0000_0000_0000,
            h@ == whole_blocks_state(state@, data@, t_offset as int, b as nat),
    {
        let mut block = [0u8; BLOCK_LEN];
        block.copy_from_slice(&data[b * BLOCK_LEN..(b + 1) * BLOCK_LEN]);
        let t = t_offset + ((b + 1) * BLOCK_LEN) as u64;
        proof {
            lemma_copied_block(data@, b as int, block@);
        }
        compress(&mut h, &block_words(&block), t, b + 1 == n);
    }
    state_bytes(&h)
}

}
