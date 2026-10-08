//! Batched BLAKE2s: portable compression copies against the RFC 7693 model in `blake2s`.
//!
//! Lane arithmetic contracts are proved for `Scalar8`. Safe array layout models connect transposed
//! states and messages to lane-wise RFC compression; production pointer operations, the batch
//! driver, dispatch and SIMD instructions are not verified.
use crate::blake2s::*;
use vstd::prelude::*;

/// The G function over LITERAL state and message indices.
///
/// `$m` is the transposed block, so each message operand is a load at a constant offset.
///
/// Verus form: an inline helper gives each G a separate proof context.
macro_rules! g {
    ($v:ident, $m:ident, $a:expr, $b:expr, $c:expr, $d:expr, $x:expr, $y:expr) => {
        ::vstd::prelude::verus_exec_expr! {
            mix($v, $m, $a, $b, $c, $d, $x, $y)
        }
    };
}

/// One round with the message schedule `s`: columns, then diagonals.
///
/// Verus form: the ghost lines (snapshots of `$v` between the G's, and [`round_ok`] at the end) are added.
macro_rules! round {
    ($v:ident, $m:ident, [$s0:expr, $s1:expr, $s2:expr, $s3:expr, $s4:expr, $s5:expr, $s6:expr, $s7:expr,
      $s8:expr, $s9:expr, $s10:expr, $s11:expr, $s12:expr, $s13:expr, $s14:expr, $s15:expr]) => {
        ::vstd::prelude::verus_exec_expr! { {
            let ghost v0 = *$v;
            g!($v, $m, 0, 4, 8, 12, $s0, $s1);
            let ghost v1 = *$v;
            g!($v, $m, 1, 5, 9, 13, $s2, $s3);
            let ghost v2 = *$v;
            g!($v, $m, 2, 6, 10, 14, $s4, $s5);
            let ghost v3 = *$v;
            g!($v, $m, 3, 7, 11, 15, $s6, $s7);
            let ghost v4 = *$v;
            g!($v, $m, 0, 5, 10, 15, $s8, $s9);
            let ghost v5 = *$v;
            g!($v, $m, 1, 6, 11, 12, $s10, $s11);
            let ghost v6 = *$v;
            g!($v, $m, 2, 7, 8, 13, $s12, $s13);
            let ghost v7 = *$v;
            g!($v, $m, 3, 4, 9, 14, $s14, $s15);
            proof {
                lemma_round_ok(v0, v1, v2, v3, v4, v5, v6, v7, *$v, *$m,
                    seq![$s0, $s1, $s2, $s3, $s4, $s5, $s6, $s7, $s8, $s9, $s10, $s11, $s12, $s13, $s14, $s15]);
            }
        } }
    };
}

/// The ten rounds as out-of-line functions, for interleaving groups.
///
/// Verus form: the functions carry their specification, inside `verus!`.
macro_rules! round_fns {
    ($($name:ident [$($s:expr),*],)*) => {
        ::vstd::prelude::verus! {
        $(
            #[inline(never)]
            fn $name<S: Lanes32>(v: &mut [S; 16], m: &[S; 16])
                ensures
                    round_ok(*final(v), *old(v), *m, seq![$($s),*]),
            {
                round!(v, m, [$($s),*])
            }
        )*
        }
    };
}

round_fns! {
    round_0 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    round_1 [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    round_2 [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    round_3 [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    round_4 [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    round_5 [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    round_6 [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    round_7 [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    round_8 [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    round_9 [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
}

/// Production's `round_all!`, local to `compress_groups`: each round over every group, in turn.
///
/// Verus form: each group loop is an inline helper with the work vectors' initial ghost snapshot and
/// a round-indexed contract. Its invariant advances groups before `g` by one round.
macro_rules! round_all {
    ($v:ident, $m:ident, $v0:ident, $($name:ident $advance:ident $k:literal),*) => {
        $(
            ::vstd::prelude::verus_exec_expr! { {
                #[inline(always)]
                fn $advance<S: Lanes32, const G: usize>(
                    v: &mut [[S; 16]; G], m: [&[S; 16]; G], Ghost(v0): Ghost<[[S; 16]; G]>)
                    requires
                        groups_rounds_ok(*old(v), v0, m, $k as nat),
                    ensures
                        groups_rounds_ok(*final(v), v0, m, ($k + 1) as nat),
                {
                    proof { reveal(groups_rounds_ok); }
                    for g in 0..G
                        invariant
                            forall|j: int| 0 <= j < g ==> #[trigger] rounds_ok(v[j], v0[j], *m[j], ($k + 1) as nat),
                            forall|j: int| g <= j < G ==> #[trigger] rounds_ok(v[j], v0[j], *m[j], $k as nat),
                    {
                        let ghost before = v[g as int];
                        $name(&mut v[g], m[g]);
                        proof {
                            lemma_round_step(before, v[g as int], *m[g as int], v0[g as int], $k);
                        }
                    }
                }
                $advance(&mut $v, $m, Ghost($v0));
            } }
        )*
    };
}

verus! {

/// Two additions modulo `2^32` are one.
pub broadcast proof fn lemma_add_mod_twice(x: u32, y: u32, z: u32)
    ensures
        #[trigger] add_mod(add_mod(x, y, 0), z, 0) == add_mod(x, y, z),
{
}

/// One state word across all lanes of a group: a vector of `WIDTH` 32-bit lanes.
///
/// Each backend supplies the lane arithmetic, specified lane by lane through [`Lanes32::lane`].
///
/// Verus form: only the lane arithmetic is copied. The raw-pointer methods (`load`, `store`, the block `transpose` and
/// `store_digests`), the walk's tuning constants (`GROUPS`, `TRANSPOSE_AHEAD`) and the default `compress_groups`, which
/// forwards to the free [`compress_groups`] (a trait method's specification cannot name the trait's own bound), are not.
pub trait Lanes32: Copy + Sized {
    /// Lanes per vector.
    const WIDTH: usize;

    /// Lane `l` of the vector, for `0 <= l < WIDTH`.
    spec fn lane(&self, l: int) -> u32;

    /// Every lane set to `x`.
    fn splat(x: u32) -> (r: Self)
        ensures
            forall|l: int| 0 <= l < Self::WIDTH ==> #[trigger] r.lane(l) == x;

    /// Lane-wise wrapping addition.
    fn add(self, o: Self) -> (r: Self)
        ensures
            forall|l: int| 0 <= l < Self::WIDTH ==> #[trigger] r.lane(l) == add_mod(self.lane(l), o.lane(l), 0);

    /// Lane-wise xor.
    fn xor(self, o: Self) -> (r: Self)
        ensures
            forall|l: int| 0 <= l < Self::WIDTH ==> #[trigger] r.lane(l) == self.lane(l) ^ o.lane(l);

    /// Rotate every lane right by `N`, one of BLAKE2s's 16, 12, 8, 7.
    fn rotr<const N: u32>(self) -> (r: Self)
        requires
            0 < N < 32,
        ensures
            forall|l: int| 0 <= l < Self::WIDTH ==> #[trigger] r.lane(l) == rotr(self.lane(l), N);
}

/// Lane `l` of a transposed chaining value: that lane's own 8 words.
///
/// Opaque, as [`col16`].
#[verifier::opaque]
pub open spec fn col8<S: Lanes32>(h: [S; 8], l: int) -> Seq<u32> {
    Seq::new(8, |i: int| h[i].lane(l))
}

/// Lane `l` of a transposed work vector or block: that lane's own 16 words.
///
/// Opaque: the round-level proofs relate whole lanes; only one G, `init` and the feed-forward look at single words.
#[verifier::opaque]
pub open spec fn col16<S: Lanes32>(v: [S; 16], l: int) -> Seq<u32> {
    Seq::new(16, |i: int| v[i].lane(l))
}

/// The main statement of the batched compression: in every group `g` and lane `l`, the chaining value `after` is the
/// RFC compression of that lane's chaining value `before` with that lane's block of `m[g]`.
pub open spec fn compresses_lanes<S: Lanes32, const G: usize>(
    before: [[S; 8]; G],
    after: [[S; 8]; G],
    m: [&[S; 16]; G],
    t: u64,
    last: bool,
) -> bool {
    forall|g: int, l: int|
        0 <= g < G && 0 <= l < S::WIDTH ==> #[trigger] col8(after[g], l) == f_spec(
            col8(before[g], l),
            col16(*m[g], l),
            t as int,
            last,
        )
}

/// A round with the schedule `s` written out: [`round_spec`] with `s = sigma(i)`.
pub open spec fn round_sched(v: Seq<u32>, m: Seq<u32>, s: Seq<int>) -> Seq<u32> {
    let v = g_spec(v, 0, 4, 8, 12, m[s[0]], m[s[1]]);
    let v = g_spec(v, 1, 5, 9, 13, m[s[2]], m[s[3]]);
    let v = g_spec(v, 2, 6, 10, 14, m[s[4]], m[s[5]]);
    let v = g_spec(v, 3, 7, 11, 15, m[s[6]], m[s[7]]);
    let v = g_spec(v, 0, 5, 10, 15, m[s[8]], m[s[9]]);
    let v = g_spec(v, 1, 6, 11, 12, m[s[10]], m[s[11]]);
    let v = g_spec(v, 2, 7, 8, 13, m[s[12]], m[s[13]]);
    g_spec(v, 3, 4, 9, 14, m[s[14]], m[s[15]])
}

// ---------------------------------------------------------------------------------------------
// The portable backend
// ---------------------------------------------------------------------------------------------
/// The portable backend, and the reference the SIMD ones are checked against.
///
/// Dispatch is compile time, so only tests use it where a SIMD backend exists.
#[derive(Clone, Copy)]
pub struct Scalar8(pub [u32; 8]);

/// Safe word-level form of the portable block/state transpose.
/// Array indexing replaces pointer gathers and vector loads; allocation and pointer safety are not modeled.
pub fn transpose_words<const W: usize>(rows: &[[u32; W]; 8]) -> (out: [Scalar8; W])
    ensures
        forall|w: int, l: int| 0 <= w < W && 0 <= l < 8 ==> #[trigger] out[w].0[l] == rows[l][w],
{
    let mut out = [Scalar8([0u32; 8]); W];
    for l in 0..8
        invariant
            forall|w: int, j: int| 0 <= w < W && 0 <= j < l ==> #[trigger] out[w].0[j] == rows[j][w],
    {
        for w in 0..W
            invariant
                l < 8,
                forall|i: int, j: int| 0 <= i < W && 0 <= j < l ==> #[trigger] out[i].0[j] == rows[j][i],
                forall|i: int| 0 <= i < w ==> #[trigger] out[i].0[l as int] == rows[l as int][i],
        {
            out[w].0[l] = rows[l][w];
        }
    }
    out
}

/// Safe byte-array form of the portable digest scatter, reusing the verified little-endian encoder.
pub fn store_digests(h: &[Scalar8; 8]) -> (out: [[u8; 32]; 8])
    ensures
        forall|l: int| 0 <= l < 8 ==> #[trigger] out[l]@ == digest_spec(col8(*h, l)),
{
    let mut out = [[0u8; 32]; 8];
    for l in 0..8
        invariant
            forall|j: int| 0 <= j < l ==> #[trigger] out[j]@ == digest_spec(col8(*h, j)),
    {
        let mut words = [0u32; 8];
        for w in 0..8
            invariant
                l < 8,
                forall|i: int| 0 <= i < w ==> #[trigger] words[i] == h[i].0[l as int],
        {
            words[w] = h[w].0[l];
        }
        proof {
            reveal(col8);
            assert(words@ =~= col8(*h, l as int));
        }
        out[l] = state_bytes(&words);
    }
    out
}

impl Lanes32 for Scalar8 {
    const WIDTH: usize = 8;

    open spec fn lane(&self, l: int) -> u32 {
        self.0[l]
    }

    #[inline(always)]
    fn splat(x: u32) -> (r: Self) {
        Self([x; 8])
    }

    /// Verus form: `array::from_fn` is an index loop.
    #[inline(always)]
    fn add(self, o: Self) -> (r: Self) {
        let mut r = [0u32; 8];
        for i in 0..8
            invariant
                forall|j: int| 0 <= j < i ==> #[trigger] r[j] == add_mod(self.0[j], o.0[j], 0),
        {
            r[i] = self.0[i].wrapping_add(o.0[i]);
            proof {
                lemma_add_mod2(self.0[i as int], o.0[i as int]);
            }
        }
        Self(r)
    }

    /// Verus form: `array::from_fn` is an index loop.
    #[inline(always)]
    fn xor(self, o: Self) -> (r: Self) {
        let mut r = [0u32; 8];
        for i in 0..8
            invariant
                forall|j: int| 0 <= j < i ==> #[trigger] r[j] == self.0[j] ^ o.0[j],
        {
            r[i] = self.0[i] ^ o.0[i];
        }
        Self(r)
    }

    /// Verus form: `array::from_fn` is an index loop.
    #[inline(always)]
    fn rotr<const N: u32>(self) -> (r: Self) {
        let mut r = [0u32; 8];
        for i in 0..8
            invariant
                0 < N < 32,
                forall|j: int| 0 <= j < i ==> #[trigger] r[j] == rotr(self.0[j], N),
        {
            r[i] = self.0[i].rotate_right(N);
        }
        Self(r)
    }
}

// ---------------------------------------------------------------------------------------------
// Rounds and the compression
// ---------------------------------------------------------------------------------------------
/// In every lane, `after` is G on `before` at state words `a, b, c, d` with message words `x, y` of `m`.
///
/// Opaque, as [`round_ok`] and [`rounds_ok`]: each step's statement stays an atom in the long straight-line bodies,
/// so the solver does not chain back through every earlier step.
#[verifier::opaque]
pub open spec fn g_ok<S: Lanes32>(
    after: [S; 16],
    before: [S; 16],
    m: [S; 16],
    a: int,
    b: int,
    c: int,
    d: int,
    x: int,
    y: int,
) -> bool {
    forall|l: int|
        0 <= l < S::WIDTH ==> #[trigger] col16(after, l) == g_spec(col16(before, l), a, b, c, d, col16(m, l)[x], col16(m, l)[y])
}

/// In every lane, `after` is one round with schedule `s` on `before`.
#[verifier::opaque]
pub open spec fn round_ok<S: Lanes32>(after: [S; 16], before: [S; 16], m: [S; 16], s: Seq<int>) -> bool {
    forall|l: int| 0 <= l < S::WIDTH ==> #[trigger] col16(after, l) == round_sched(col16(before, l), col16(m, l), s)
}

/// In every lane, `v` is rounds `0..k` on `v0`.
#[verifier::opaque]
pub open spec fn rounds_ok<S: Lanes32>(v: [S; 16], v0: [S; 16], m: [S; 16], k: nat) -> bool {
    forall|l: int| 0 <= l < S::WIDTH ==> #[trigger] col16(v, l) == rounds_spec(col16(v0, l), col16(m, l), k)
}

/// Keep the inter-round group invariant opaque between independently verified group loops.
#[verifier::opaque]
pub open spec fn groups_rounds_ok<S: Lanes32, const G: usize>(
    v: [[S; 16]; G], v0: [[S; 16]; G], m: [&[S; 16]; G], k: nat) -> bool {
    forall|j: int| 0 <= j < G ==> #[trigger] rounds_ok(v[j], v0[j], *m[j], k)
}

proof fn lemma_g_ok<S: Lanes32>(after: [S; 16], before: [S; 16], m: [S; 16], a: int, b: int, c: int, d: int, x: int, y: int)
    requires
        forall|l: int| 0 <= l < S::WIDTH ==> #[trigger] col16(after, l) == g_spec(col16(before, l), a, b, c, d, col16(m, l)[x], col16(m, l)[y]),
    ensures
        g_ok(after, before, m, a, b, c, d, x, y),
{
    reveal(g_ok);
}

/// The production G operations, isolated so lane arithmetic facts do not accumulate across rounds.
#[inline(always)]
fn mix<S: Lanes32>(v: &mut [S; 16], m: &[S; 16], a: usize, b: usize, c: usize, d: usize, x: usize, y: usize)
    requires
        a < 16, b < 16, c < 16, d < 16, x < 16, y < 16,
        a != b, a != c, a != d, b != c, b != d, c != d,
    ensures
        g_ok(*final(v), *old(v), *m, a as int, b as int, c as int, d as int, x as int, y as int),
{
    let ghost before = *v;
    v[a] = v[a].add(v[b]).add(m[x]);
    v[d] = v[d].xor(v[a]).rotr::<16>();
    v[c] = v[c].add(v[d]);
    v[b] = v[b].xor(v[c]).rotr::<12>();
    v[a] = v[a].add(v[b]).add(m[y]);
    v[d] = v[d].xor(v[a]).rotr::<8>();
    v[c] = v[c].add(v[d]);
    v[b] = v[b].xor(v[c]).rotr::<7>();
    proof {
        assert forall|l: int| 0 <= l < S::WIDTH implies #[trigger] col16(*v, l) == g_spec(
            col16(before, l), a as int, b as int, c as int, d as int, col16(*m, l)[x as int], col16(*m, l)[y as int]) by {
            broadcast use lemma_add_mod_twice;
            reveal(g_spec);
            reveal(col16);
            assert(col16(*v, l) =~= g_spec(col16(before, l), a as int, b as int, c as int, d as int,
                m[x as int].lane(l), m[y as int].lane(l)));
        }
        lemma_g_ok(*v, before, *m, a as int, b as int, c as int, d as int, x as int, y as int);
    }
}

/// The eight G's of a round, columns then diagonals, make the round.
proof fn lemma_round_ok<S: Lanes32>(
    v0: [S; 16],
    v1: [S; 16],
    v2: [S; 16],
    v3: [S; 16],
    v4: [S; 16],
    v5: [S; 16],
    v6: [S; 16],
    v7: [S; 16],
    v8: [S; 16],
    m: [S; 16],
    s: Seq<int>,
)
    requires
        s.len() == 16,
        g_ok(v1, v0, m, 0, 4, 8, 12, s[0], s[1]),
        g_ok(v2, v1, m, 1, 5, 9, 13, s[2], s[3]),
        g_ok(v3, v2, m, 2, 6, 10, 14, s[4], s[5]),
        g_ok(v4, v3, m, 3, 7, 11, 15, s[6], s[7]),
        g_ok(v5, v4, m, 0, 5, 10, 15, s[8], s[9]),
        g_ok(v6, v5, m, 1, 6, 11, 12, s[10], s[11]),
        g_ok(v7, v6, m, 2, 7, 8, 13, s[12], s[13]),
        g_ok(v8, v7, m, 3, 4, 9, 14, s[14], s[15]),
    ensures
        round_ok(v8, v0, m, s),
{
    reveal(g_ok);
    reveal(round_ok);
    assert forall|l: int| 0 <= l < S::WIDTH implies #[trigger] col16(v8, l) == round_sched(col16(v0, l), col16(m, l), s) by {
        assert(col16(v1, l) == g_spec(col16(v0, l), 0, 4, 8, 12, col16(m, l)[s[0]], col16(m, l)[s[1]]));
        assert(col16(v2, l) == g_spec(col16(v1, l), 1, 5, 9, 13, col16(m, l)[s[2]], col16(m, l)[s[3]]));
        assert(col16(v3, l) == g_spec(col16(v2, l), 2, 6, 10, 14, col16(m, l)[s[4]], col16(m, l)[s[5]]));
        assert(col16(v4, l) == g_spec(col16(v3, l), 3, 7, 11, 15, col16(m, l)[s[6]], col16(m, l)[s[7]]));
        assert(col16(v5, l) == g_spec(col16(v4, l), 0, 5, 10, 15, col16(m, l)[s[8]], col16(m, l)[s[9]]));
        assert(col16(v6, l) == g_spec(col16(v5, l), 1, 6, 11, 12, col16(m, l)[s[10]], col16(m, l)[s[11]]));
        assert(col16(v7, l) == g_spec(col16(v6, l), 2, 7, 8, 13, col16(m, l)[s[12]], col16(m, l)[s[13]]));
    }
}

/// A round with the production schedule of round `k`, after rounds `0..k`, gives rounds `0..k + 1`, in every lane.
proof fn lemma_round_step<S: Lanes32>(before: [S; 16], after: [S; 16], m: [S; 16], v0: [S; 16], k: int)
    requires
        0 <= k < 10,
        rounds_ok(before, v0, m, k as nat),
        round_ok(after, before, m, sigma(k)),
    ensures
        rounds_ok(after, v0, m, (k + 1) as nat),
{
    reveal(round_ok);
    reveal(rounds_ok);
    assert forall|l: int| 0 <= l < S::WIDTH implies #[trigger] col16(after, l) == rounds_spec(col16(v0, l), col16(m, l), (k + 1) as nat) by {
        assert(col16(before, l) == rounds_spec(col16(v0, l), col16(m, l), k as nat));
        assert(col16(after, l) == round_sched(col16(before, l), col16(m, l), sigma(k)));
    }
}

/// Bitwise identities of the work vector's initialization.
proof fn lemma_xor_zero(x: u32)
    by (bit_vector)
    ensures
        x ^ 0u32 == x,
        0u32.wrapping_sub(1u32) == 0xFFFF_FFFFu32,
{
}

/// The working state of one compression (RFC 7693, section 3.2).
///
/// ```text
///     v[0..8]    chaining value h
///     v[8..16]   IV, with v[12] ^= t_lo, v[13] ^= t_hi, v[14] = !v[14] on the final block
/// ```
///
/// Verus form: `(last as u32).wrapping_neg()` is `0u32.wrapping_sub(last as u32)` (vstd specifies `wrapping_sub`, not
/// `wrapping_neg`), and the `array::from_fn` is the array written out.
#[inline(always)]
fn init<S: Lanes32>(h: &[S; 8], t: u64, last: bool) -> (v: [S; 16])
    ensures
        forall|l: int| 0 <= l < S::WIDTH ==> #[trigger] col16(v, l) == init_spec(col8(*h, l), t as int, last),
{
    // All ones on the final block, zero otherwise.
    let f0 = 0u32.wrapping_sub(last as u32);
    let row = [
        IV[0],
        IV[1],
        IV[2],
        IV[3],
        IV[4] ^ t as u32,
        IV[5] ^ (t >> 32) as u32,
        IV[6] ^ f0,
        IV[7],
    ];
    let v = [
        h[0],
        h[1],
        h[2],
        h[3],
        h[4],
        h[5],
        h[6],
        h[7],
        S::splat(row[0]),
        S::splat(row[1]),
        S::splat(row[2]),
        S::splat(row[3]),
        S::splat(row[4]),
        S::splat(row[5]),
        S::splat(row[6]),
        S::splat(row[7]),
    ];
    proof {
        lemma_cast_t(t);
        lemma_not_is_xor(IV[6]);
        lemma_xor_zero(IV[6]);
        assert(IV@ =~= iv());
        assert forall|l: int| 0 <= l < S::WIDTH implies #[trigger] col16(v, l) == init_spec(col8(*h, l), t as int, last) by {
            reveal(col16);
            reveal(col8);
            assert(col16(v, l) =~= init_spec(col8(*h, l), t as int, last));
        }
    }
    v
}

/// Compress `G` groups.
///
/// One group runs its ten rounds inline, in registers.
///
/// Several groups keep their states in memory, one out-of-line call per round.
///
/// Each call fits the register file, and the calls of a round fill each other's stalls.
///
/// Verus form: not `unsafe` (`m` holds references, so there is nothing for the caller to uphold); the `array::from_fn`
/// building `v` is a loop over the groups, from an array of splats; ghost lines between the rounds; the `G > 1` arm's
/// local `round_all!` macro becomes inline group-loop helpers with round-indexed contracts and invariants.
#[inline(always)]
#[verifier::rlimit(30)]
pub fn compress_groups<S: Lanes32, const G: usize>(h: &mut [[S; 8]; G], m: [&[S; 16]; G], t: u64, last: bool)
    ensures
        compresses_lanes(*old(h), *final(h), m, t, last),
{
    let mut v: [[S; 16]; G] = [[S::splat(0); 16]; G];
    for g in 0..G
        invariant
            *h == *old(h),
            forall|j: int, l: int| 0 <= j < g && 0 <= l < S::WIDTH ==> #[trigger] col16(v[j], l) == init_spec(col8(h[j], l), t as int, last),
    {
        v[g] = init(&h[g], t, last);
    }
    let ghost v0 = v;
    // `G` is a constant, so only one of the two arms survives monomorphization.
    if G == 1 {
        let (v, m) = (&mut v[0], m[0]);
        let ghost s = *v;
        proof {
            assert(rounds_ok(*v, s, *m, 0)) by {
                reveal(rounds_ok);
            }
        }
        let ghost b0 = *v;
        round!(v, m, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]);
        proof { lemma_round_step(b0, *v, *m, s, 0); }
        let ghost b1 = *v;
        round!(v, m, [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3]);
        proof { lemma_round_step(b1, *v, *m, s, 1); }
        let ghost b2 = *v;
        round!(v, m, [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4]);
        proof { lemma_round_step(b2, *v, *m, s, 2); }
        let ghost b3 = *v;
        round!(v, m, [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8]);
        proof { lemma_round_step(b3, *v, *m, s, 3); }
        let ghost b4 = *v;
        round!(v, m, [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13]);
        proof { lemma_round_step(b4, *v, *m, s, 4); }
        let ghost b5 = *v;
        round!(v, m, [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9]);
        proof { lemma_round_step(b5, *v, *m, s, 5); }
        let ghost b6 = *v;
        round!(v, m, [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11]);
        proof { lemma_round_step(b6, *v, *m, s, 6); }
        let ghost b7 = *v;
        round!(v, m, [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10]);
        proof { lemma_round_step(b7, *v, *m, s, 7); }
        let ghost b8 = *v;
        round!(v, m, [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5]);
        proof { lemma_round_step(b8, *v, *m, s, 8); }
        let ghost b9 = *v;
        round!(v, m, [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]);
        proof { lemma_round_step(b9, *v, *m, s, 9); }
    } else {
        proof {
            assert forall|j: int| 0 <= j < G implies #[trigger] rounds_ok(v[j], v0[j], *m[j], 0) by {
                reveal(rounds_ok);
            }
            reveal(groups_rounds_ok);
            assert(groups_rounds_ok(v, v0, m, 0));
        }
        round_all!(
            v, m, v0,
            round_0 advance_0 0, round_1 advance_1 1, round_2 advance_2 2, round_3 advance_3 3,
            round_4 advance_4 4, round_5 advance_5 5, round_6 advance_6 6, round_7 advance_7 7,
            round_8 advance_8 8, round_9 advance_9 9
        );
    }
    proof {
        reveal(groups_rounds_ok);
        assert(forall|j: int| 0 <= j < G ==> #[trigger] rounds_ok(v[j], v0[j], *m[j], 10));
    }
    // Feed-forward: h[i] ^= v[i] ^ v[i + 8].
    for g in 0..G
        invariant
            forall|j: int, l: int| 0 <= j < g && 0 <= l < S::WIDTH ==> #[trigger] col8(h[j], l) == f_spec(
                col8(old(h)[j], l), col16(*m[j], l), t as int, last),
            forall|j: int| g <= j < G ==> #[trigger] h[j] == old(h)[j],
            forall|j: int| 0 <= j < G ==> #[trigger] rounds_ok(v[j], v0[j], *m[j], 10),
            forall|j: int, l: int| 0 <= j < G && 0 <= l < S::WIDTH ==> #[trigger] col16(v0[j], l) == init_spec(
                col8(old(h)[j], l), t as int, last),
    {
        for i in 0..8
            invariant
                g < G,
                forall|j: int, l: int| 0 <= j < g && 0 <= l < S::WIDTH ==> #[trigger] col8(h[j], l) == f_spec(
                    col8(old(h)[j], l), col16(*m[j], l), t as int, last),
                forall|j: int| g < j < G ==> #[trigger] h[j] == old(h)[j],
                forall|j: int| 0 <= j < G ==> #[trigger] rounds_ok(v[j], v0[j], *m[j], 10),
                forall|j: int, l: int| 0 <= j < G && 0 <= l < S::WIDTH ==> #[trigger] col16(v0[j], l) == init_spec(
                    col8(old(h)[j], l), t as int, last),
                forall|k: int, l: int| 0 <= k < i && 0 <= l < S::WIDTH ==> #[trigger] h[g as int][k].lane(l) == old(
                    h)[g as int][k].lane(l) ^ v[g as int][k].lane(l) ^ v[g as int][k + 8].lane(l),
                forall|k: int| i <= k < 8 ==> #[trigger] h[g as int][k] == old(h)[g as int][k],
        {
            h[g][i] = h[g][i].xor(v[g][i]).xor(v[g][i + 8]);
        }
        proof {
            assert forall|l: int| 0 <= l < S::WIDTH implies #[trigger] col8(h[g as int], l) == f_spec(
                col8(old(h)[g as int], l), col16(*m[g as int], l), t as int, last) by {
                reveal(f_spec);
                reveal(rounds_ok);
                assert(rounds_ok(v[g as int], v0[g as int], *m[g as int], 10));
                assert(col16(v[g as int], l) == rounds_spec(col16(v0[g as int], l), col16(*m[g as int], l), 10));
                assert(col16(v0[g as int], l) == init_spec(col8(old(h)[g as int], l), t as int, last));
                reveal(col16);
                reveal(col8);
                assert(col8(h[g as int], l) =~= f_spec(col8(old(h)[g as int], l), col16(*m[g as int], l), t as int, last));
            }
        }
    }
}

/// Safe adapter composing state/block transposition, one-group compression and digest scatter.
/// This adapter models the layout; it is not a copy or proof of the production raw-pointer driver.
pub fn compress_rows(states: &[[u32; 8]; 8], messages: &[[u32; 16]; 8], t: u64, last: bool)
    -> (out: [[u8; 32]; 8])
    ensures
        forall|l: int| 0 <= l < 8 ==> #[trigger] out[l]@ == digest_spec(
            f_spec(states[l]@, messages[l]@, t as int, last)),
{
    let mut h = [transpose_words(states)];
    let block = transpose_words(messages);
    let ghost initial = h[0];
    proof {
        reveal(col8);
        reveal(col16);
        assert forall|l: int| #![trigger col8(initial, l)] #![trigger col16(block, l)]
            0 <= l < 8 implies col8(initial, l) == states[l]@ && col16(block, l) == messages[l]@ by {
            assert(col8(initial, l) =~= states[l]@);
            assert(col16(block, l) =~= messages[l]@);
        }
    }
    compress_groups(&mut h, [&block], t, last);
    store_digests(&h[0])
}

}
