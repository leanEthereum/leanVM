// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! The zerocheck's multilinear rounds, after the univariate skip.
//!
//! Past the skip, the zerocheck is a sumcheck over the `n = m - k_skip` remaining variables:
//!
//! ```text
//!     sum_x eq(r, x) * (a(x) b(x) + c(x))        a, b, c folded at the skip challenge z
//! ```
//!
//! The quadratic `a b` and the linear `c` ride the same rounds, so all three claims land at one point.
//!
//! Round `t` binds the lowest unbound variable: positions `2k` and `2k + 1` pair up as its `X = 0` and `X = 1`.
//! Each kernel returns the bare `(G(1), G(inf))` of the round's inner polynomial `G`.
//! The prover sends them, and the verifier derives `G(0)` from the running claim:
//!
//! ```text
//!     claim = (1 + r_t) G(0) + r_t G(1)
//! ```
//!
//! Every pass sends two rounds, the second as a quadratic in the first's challenge.
//!
//! - **Bit passes** read the packed bits, folding them on the fly, while a folded table would outweigh them.
//! - The last bit pass also stores the folded tables.
//! - **Table passes** fold the challenges pending on the stored tables, then send two rounds from the result.
//!
//! The naive fold-then-sum routes cross-check every kernel in the tests.

use std::mem::MaybeUninit;

use parallel::Chunks;
use primitives::bit_fold::{BLOCK, BitFold};
use primitives::field::{F192, F192Unreduced};
use primitives::multilinear::{SplitEq, eq_table};
use primitives::stream::Stream;

use super::Padding;
use super::round1::EQ_HIGH_VARS;

/// Eq variables in the per-task half of a bit pass's split eq table.
///
/// - `2^10` entries are 24 KiB, so the table stays in L1 beside the fold's matrices.
/// - The remaining variables index the tasks, one reduced product each.
const EQ_LO_VARS: usize = 10;

/// Four independent products.
///
/// A tuple keeps the scalar and NEON paths in registers, while VPCLMULQDQ batches them in one register.
#[inline(always)]
fn mul_quad(a: (F192, F192, F192, F192), b: (F192, F192, F192, F192)) -> (F192, F192, F192, F192) {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
    {
        let r = primitives::field::mul4([a.0, a.1, a.2, a.3], [b.0, b.1, b.2, b.3]);
        (r[0], r[1], r[2], r[3])
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2")))]
    (a.0 * b.0, a.1 * b.1, a.2 * b.2, a.3 * b.3)
}

/// Four independent products, left unreduced for a caller summing them.
#[inline(always)]
fn mul_quad_unreduced(
    a: (F192, F192, F192, F192),
    b: (F192, F192, F192, F192),
) -> (F192Unreduced, F192Unreduced, F192Unreduced, F192Unreduced) {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
    {
        let r = primitives::field::mul_unreduced4([a.0, a.1, a.2, a.3], [b.0, b.1, b.2, b.3]);
        (r[0], r[1], r[2], r[3])
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2")))]
    (
        a.0.mul_unreduced(b.0),
        a.1.mul_unreduced(b.1),
        a.2.mul_unreduced(b.2),
        a.3.mul_unreduced(b.3),
    )
}

/// The packed `a` and `b` bits, 64 skip bits per row, the row index running over the positions past the skip.
///
/// The kernels never read `c`: an honest witness has `c = a AND b`, derived from the rows already loaded.
#[derive(Clone, Copy, Debug)]
pub(crate) struct PackedWitness<'a> {
    /// The `A z` bits.
    pub a: &'a [u8],
    /// The `B z` bits.
    pub b: &'a [u8],
}

impl<'a> PackedWitness<'a> {
    /// The two witnesses cut into rows of `CHUNKS` bytes, one per position at this level.
    fn rows<const CHUNKS: usize>(self) -> [&'a [[u8; CHUNKS]]; 2] {
        // A position at this level is `CHUNKS` bytes of each witness.
        let rows = [self.a, self.b].map(|packed| {
            let (rows, rest) = packed.as_chunks::<CHUNKS>();
            assert!(rest.is_empty(), "packed witness is whole rows");
            rows
        });
        // The passes halve the positions per round, so there is a power of two of them.
        let n_pos = rows[0].len();
        assert_eq!(rows[1].len(), n_pos, "a and b have one length");
        assert!(n_pos.is_power_of_two(), "a power-of-two number of positions");
        rows
    }

    /// The last `bytes` bytes of both witnesses.
    fn suffix(self, bytes: usize) -> Self {
        Self {
            a: &self.a[self.a.len() - bytes..],
            b: &self.b[self.b.len() - bytes..],
        }
    }
}

/// The `c = a AND b` rows of up to 64 positions, into the first `a.len()` rows of `c`.
#[inline(always)]
fn and_rows<const CHUNKS: usize>(a: &[[u8; CHUNKS]], b: &[[u8; CHUNKS]], c: &mut [[u8; CHUNKS]; BLOCK]) {
    for ((c, a), b) in c
        .as_flattened_mut()
        .iter_mut()
        .zip(a.as_flattened())
        .zip(b.as_flattened())
    {
        *c = a & b;
    }
}

/// The folded `a`, `b`, `c` values of up to 64 consecutive positions.
///
/// A task folds every block into one of these, so no block pays for zeroing or moving its tables.
struct FoldedBlock {
    a: [F192; BLOCK],
    b: [F192; BLOCK],
    c: [F192; BLOCK],
}

impl FoldedBlock {
    const ZERO: Self = Self {
        a: [F192::ZERO; BLOCK],
        b: [F192::ZERO; BLOCK],
        c: [F192::ZERO; BLOCK],
    };

    /// Fold positions `first..first + len` of each witness into the first `len` values.
    #[inline(always)]
    fn fold<const CHUNKS: usize>(&mut self, fold: &BitFold, rows: [&[[u8; CHUNKS]]; 2], first: usize, len: usize) {
        let [a, b] = rows.map(|r| &r[first..first + len]);
        let mut c = [[0u8; CHUNKS]; BLOCK];
        and_rows(a, b, &mut c);
        fold.fold_block(a, &mut self.a);
        fold.fold_block(b, &mut self.b);
        fold.fold_block(&c[..len], &mut self.c);
    }

    /// Quad `i`'s values of one table.
    #[inline(always)]
    fn quad(table: &[F192; BLOCK], i: usize) -> [F192; 4] {
        table[4 * i..4 * i + 4].try_into().expect("a quad")
    }
}

/// Where the zero padding of a batched witness lets a kernel skip whole groups of positions.
///
/// A group spans `2^group_log` witness bits.
/// Group `g` lies wholly in a block's zero padding iff `(g & mask) >= live`.
///
/// - Such a group folds to zero, so it adds nothing to a message.
/// - A group straddling the boundary counts as live: its padding part is honestly zero.
/// - With no whole padding group, the mask is zero and every group is live.
#[derive(Clone, Copy, Debug)]
struct LiveGroups {
    mask: usize,
    live: usize,
}

impl LiveGroups {
    const fn new(padding: &Padding, group_log: usize) -> Self {
        let every = Self {
            mask: 0,
            live: usize::MAX,
        };
        // A group covering whole blocks holds data whenever its blocks do.
        if padding.k_log <= group_log {
            return every;
        }
        // Within a block, the groups from the first one wholly past the useful bits on are zero.
        let per_block = 1usize << (padding.k_log - group_log);
        let live = padding.useful_bits.div_ceil(1 << group_log);
        if live >= per_block {
            return every;
        }
        Self {
            mask: per_block - 1,
            live,
        }
    }

    /// Whether group `g` may hold a nonzero bit.
    #[inline(always)]
    const fn contains(self, g: usize) -> bool {
        (g & self.mask) < self.live
    }
}

/// Two consecutive multilinear rounds from one pass.
///
/// Round `t + 1` binds its variable after the verifier samples `rho`, the challenge of round `t`.
///
/// Its polynomial is quadratic in that `rho`, so one pass stores its three coefficients per evaluation point.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct RoundPair {
    /// Round `t`'s `(G(1), G(inf))`.
    pub first: (F192, F192),
    /// Round `t + 1` at `Y = 1` and `Y = inf`, each as `[S_0, S_1, S_2]`.
    ///
    /// ```text
    ///     G(Y) = (1 + rho) S_0 + rho S_1 + rho (1 + rho) S_2
    /// ```
    second: [[F192; 3]; 2],
}

impl RoundPair {
    /// Round `t + 1`'s `(G(1), G(inf))`, once round `t`'s challenge `rho` is known.
    pub(crate) fn second(&self, rho: F192) -> (F192, F192) {
        let [one, inf] = self
            .second
            .map(|[s0, s1, s2]| s0 + rho * (s0 + s1) + rho * (F192::ONE + rho) * s2);
        (one, inf)
    }

    /// Both rounds from the eq-weighted sums of the quad terms, `r_v` the eq challenge of the second round's variable.
    fn from_sums(sums: [F192; 8], r_v: F192) -> Self {
        // Slots 0, 1 hold round t's G(1) at v = 0, 1, and slots 2, 3 its G(inf).
        // Round t + 1 reads slots 4, 1, 3 at Y = 1 and 5, 6, 7 at Y = inf.
        let split_v = |v0: F192, v1: F192| v0 + r_v * (v0 + v1);
        Self {
            first: (split_v(sums[0], sums[1]), split_v(sums[2], sums[3])),
            second: [[sums[4], sums[1], sums[3]], [sums[5], sums[6], sums[7]]],
        }
    }
}

/// One quad's terms of two consecutive rounds, before its eq weight.
///
/// The quad is positions `4k + u + 2v`, `u` the first round's variable and `v` the second's.
///
/// ```text
///     position   4k     4k+1   4k+2   4k+3
///     (u, v)     (0,0)  (1,0)  (0,1)  (1,1)
/// ```
///
/// Round `t + 1` folds `u` at `rho` first, so each of its values is `f(rho, Y) = f(0, Y) + rho * (f(0, Y) + f(1, Y))`.
///
/// Expanding the product in `rho` gives the three sums of the second round:
///
/// ```text
///     S_0 = sum eq * a(0, Y) b(0, Y)      S_1 = sum eq * a(1, Y) b(1, Y)
///     S_2 = sum eq * (a(0, Y) + a(1, Y)) (b(0, Y) + b(1, Y))
/// ```
///
/// Round `t` needs its sums split by `v`, and two of them coincide with round `t + 1`'s.
/// So eight products per quad cover both rounds, the same count as two single rounds.
///
/// Returns the eight products in the slots the pair's sums are read from.
#[inline(always)]
fn quad_pair_terms(
    [a0, a1, a2, a3]: [F192; 4],
    [b0, b1, b2, b3]: [F192; 4],
    [_, c1, c2, c3]: [F192; 4],
) -> [(F192, F192, F192, F192); 2] {
    // Leading coefficients along `u` (positions 0,1 and 2,3) and along `v` (0,2 and 1,3).
    let (du0, du1, dv0, dv1) = (a0 + a1, a2 + a3, a0 + a2, a1 + a3);
    let (eu0, eu1, ev0, ev1) = (b0 + b1, b2 + b3, b0 + b2, b1 + b3);
    let (p1, p2, p3, q0) = mul_quad((a1, a2, a3, du0), (b1, b2, b3, eu0));
    let (q1, r0, r1, r2) = mul_quad((du1, dv0, dv1, du0 + du1), (eu1, ev0, ev1, eu0 + eu1));
    [(p1 + c1, p3 + c3, q0, q1), (p2 + c2, r0, r1, r2)]
}

/// Add one quad's eq-weighted terms to the eight sums, unreduced: a task reduces each sum once.
#[inline(always)]
fn add_quad(acc: &mut [F192Unreduced; 8], eq: F192, [lo, hi]: [(F192, F192, F192, F192); 2]) {
    let e = (eq, eq, eq, eq);
    let (s0, s1, s2, s3) = mul_quad_unreduced(e, lo);
    let (s4, s5, s6, s7) = mul_quad_unreduced(e, hi);
    for (acc, s) in acc.iter_mut().zip([s0, s1, s2, s3, s4, s5, s6, s7]) {
        *acc ^= s;
    }
}

/// Rounds `t` and `t + 1` straight from the packed bits, the folded tables never stored.
///
/// With `rho_1..rho_t` bound, `fold` weights each position's `2^t` rows (see its level constructor).
///
/// Each round's polynomial, with `r_eq` the eq challenges of the variables round `t` does not bind:
///
/// ```text
///     G(X) = sum_x' eq(r_eq, x') * (a(X, x') * b(X, x') + c(X, x'))
/// ```
///
/// The linear `c` term reaches `G(1)` only.
pub(crate) fn bit_pass(bits: PackedWitness<'_>, fold: &BitFold, r_eq: &[F192], padding: &Padding) -> RoundPair {
    // A position at level `t` is `8 * 2^t` bytes: one kernel per row width, its loops fully unrolled.
    let sums = match fold.n_chunks() {
        8 => bit_pass_kernel::<8>(bits, fold, r_eq, padding, None),
        16 => bit_pass_kernel::<16>(bits, fold, r_eq, padding, None),
        32 => bit_pass_kernel::<32>(bits, fold, r_eq, padding, None),
        64 => bit_pass_kernel::<64>(bits, fold, r_eq, padding, None),
        128 => bit_pass_kernel::<128>(bits, fold, r_eq, padding, None),
        n => panic!("no bit pass for {n}-byte rows"),
    };
    RoundPair::from_sums(sums, r_eq[0])
}

/// The same two rounds, also storing the level-`t` folded `(a, b, c)` tables for the passes that follow.
pub(crate) fn bit_pass_storing(
    bits: PackedWitness<'_>,
    fold: &BitFold,
    r_eq: &[F192],
    padding: &Padding,
) -> (RoundPair, [Vec<F192>; 3]) {
    // Every slot is written by the kernel, padding and tail included, so the tables start uninitialized.
    let n_pos = bits.a.len() / fold.n_chunks();
    let mut out: [Box<[MaybeUninit<F192>]>; 3] = std::array::from_fn(|_| Box::new_uninit_slice(n_pos));
    let outs = Some(out.each_mut().map(|o| &mut o[..]));
    let sums = match fold.n_chunks() {
        8 => bit_pass_kernel::<8>(bits, fold, r_eq, padding, outs),
        16 => bit_pass_kernel::<16>(bits, fold, r_eq, padding, outs),
        32 => bit_pass_kernel::<32>(bits, fold, r_eq, padding, outs),
        64 => bit_pass_kernel::<64>(bits, fold, r_eq, padding, outs),
        128 => bit_pass_kernel::<128>(bits, fold, r_eq, padding, outs),
        n => panic!("no bit pass for {n}-byte rows"),
    };
    // SAFETY: the kernel writes every slot, padding and tail included.
    let tables = out.map(|o| unsafe { o.assume_init() }.into_vec());
    (RoundPair::from_sums(sums, r_eq[0]), tables)
}

/// The two-round pass over rows of `CHUNKS` bytes: the eight sums the pair is read from.
///
/// `out`, when given, receives every position's folded values, one slot each.
///
/// The identical tail is summed once from its last group, whose stored values are copied over the rest of it.
fn bit_pass_kernel<const CHUNKS: usize>(
    bits: PackedWitness<'_>,
    fold: &BitFold,
    r_eq: &[F192],
    padding: &Padding,
    mut out: Option<[&mut [MaybeUninit<F192>]; 3]>,
) -> [F192; 8] {
    let rows = bits.rows::<CHUNKS>();
    let n_quads = rows[0].len() / 4;
    assert!(n_quads >= 1, "two rounds need four positions");
    assert_eq!(r_eq.len(), n_quads.trailing_zeros() as usize + 1);
    if let Some(out) = &out {
        assert!(out.iter().all(|o| o.len() == 4 * n_quads), "one output per position");
    }

    // `r_eq[0]` weights round `t`'s split by `v`; the rest weight the quads.
    let SplitEq {
        low: eq_lo,
        high: eq_hi,
        ..
    } = SplitEq::with_low_vars(&r_eq[1..], EQ_LO_VARS);
    let lo_size = eq_lo.len();

    // A quad covers 64 skip bits times its 4 * 2^t bound rows.
    let quad_log = (32 * CHUNKS).trailing_zeros() as usize;
    let live = LiveGroups::new(padding, quad_log);
    // The quads before the tail, in whole folded blocks of sixteen.
    let m = quad_log + n_quads.trailing_zeros() as usize;
    let tail = padding.tail(m, quad_log, quad_log + 4, r_eq);
    let head_quads = tail.map_or(n_quads, |t| t.head >> quad_log);
    let is_live = |quad: usize| quad < head_quads && live.contains(quad);

    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "gfni",
        target_feature = "avx512bw",
        target_feature = "avx512vbmi",
        target_feature = "avx512f",
        target_feature = "vpclmulqdq"
    ))]
    let eq_planes = (out.is_none() && lo_size >= BLOCK / 4).then(|| planar::planes(&eq_lo));

    // One task per high eq index: `lo_size` quads, `4 * lo_size` outputs of each table.
    let chunks = out.as_mut().map(|o| o.each_mut().map(|o| Chunks::new(o, 4 * lo_size)));

    let mut sums = parallel::map_reduce(
        head_quads.div_ceil(lo_size),
        || [F192::ZERO; 8],
        |hi| {
            #[cfg(all(
                target_arch = "x86_64",
                target_feature = "gfni",
                target_feature = "avx512bw",
                target_feature = "avx512vbmi",
                target_feature = "avx512f",
                target_feature = "vpclmulqdq"
            ))]
            if let Some(eq_planes) = &eq_planes {
                // SAFETY: the target features are enabled at compile time.
                let acc = unsafe { planar::quad_sums(fold, rows, hi * lo_size, eq_planes, is_live) };
                return acc.map(|s| eq_hi[hi] * s.reduce());
            }
            // SAFETY: task `hi` takes chunk `hi` of each output once, and the buffers outlive the dispatch.
            let mut outs = chunks.as_ref().map(|c| c.each_ref().map(|c| unsafe { c.get(hi) }));
            let stream = Stream::new();
            let mut acc = [F192Unreduced::ZERO; 8];
            let mut f = FoldedBlock::ZERO;
            // Sixteen quads per folded block.
            for lo_first in (0..lo_size).step_by(BLOCK / 4) {
                let n = (lo_size - lo_first).min(BLOCK / 4);
                let quad_first = hi * lo_size + lo_first;
                // The tail is summed and stored after the dispatch.
                if quad_first >= head_quads {
                    break;
                }
                let dst = 4 * lo_first..4 * (lo_first + n);
                // A block wholly in padding folds to zero.
                if !(quad_first..quad_first + n).any(is_live) {
                    if let Some(outs) = &mut outs {
                        for o in outs.iter_mut() {
                            o[dst.clone()].fill(MaybeUninit::new(F192::ZERO));
                        }
                    }
                    continue;
                }
                f.fold(fold, rows, 4 * quad_first, 4 * n);
                for i in 0..n {
                    let terms = quad_pair_terms(
                        FoldedBlock::quad(&f.a, i),
                        FoldedBlock::quad(&f.b, i),
                        FoldedBlock::quad(&f.c, i),
                    );
                    add_quad(&mut acc, eq_lo[lo_first + i], terms);
                }
                // Publish the block without a read: nothing touches these tables before the next pass.
                if let Some(outs) = &mut outs {
                    for (o, t) in outs.iter_mut().zip([&f.a, &f.b, &f.c]) {
                        stream.write(&mut o[dst.clone()], &t[..4 * n]);
                    }
                }
            }
            acc.map(|s| eq_hi[hi] * s.reduce())
        },
        |x, y| std::array::from_fn(|i| x[i] + y[i]),
    );

    if let Some(tail) = tail {
        // The last group is summed, and stored in place, then copied over the rest of the tail.
        let group_len = 1 << (tail.group_log - quad_log + 2);
        let group_sums = bit_pass_kernel::<CHUNKS>(
            bits.suffix(group_len * CHUNKS),
            fold,
            &r_eq[..tail.r_inner],
            &padding.without_tail(),
            out.as_mut()
                .map(|o| o.each_mut().map(|o| &mut o[4 * n_quads - group_len..])),
        );
        for (s, g) in sums.iter_mut().zip(group_sums) {
            *s += tail.weight * g;
        }
        if let Some(out) = out {
            copy_group(out, 4 * head_quads, group_len);
        }
    }
    sums
}

/// One round straight from the folded tables, `(G(1), G(inf))`, for the small tables at the end.
///
/// Positions `2x` and `2x + 1` pair up as the round's `X = 0` and `X = 1`, and `r_eq` weights the pairs:
///
/// ```text
///     G(1)   = sum_x eq(r_eq, x) * (a_1 b_1 + c_1)
///     G(inf) = sum_x eq(r_eq, x) * (a_0 + a_1)(b_0 + b_1)        the leading coefficient, in characteristic 2
/// ```
pub(crate) fn single_round([a, b, c]: [&[F192]; 3], r_eq: &[F192]) -> (F192, F192) {
    let n = a.len();
    assert!(n.is_power_of_two() && n >= 2);
    assert!(b.len() == n && c.len() == n, "a, b, c have one length");
    assert_eq!(r_eq.len(), n.trailing_zeros() as usize - 1);
    // One eq weight per pair, the pairs' `X = 1` and leading terms summed under it.
    let eq = eq_table(r_eq);
    let (mut g1, mut g_inf) = (F192::ZERO, F192::ZERO);
    for (x, &e) in eq.iter().enumerate() {
        let (a0, a1, b0, b1, c1) = (a[2 * x], a[2 * x + 1], b[2 * x], b[2 * x + 1], c[2 * x + 1]);
        g1 += e * (a1 * b1 + c1);
        g_inf += e * (a0 + a1) * (b0 + b1);
    }
    (g1, g_inf)
}

/// Bind a table's low variable at `chi`, in place: `v[x] = v[2x] + chi (v[2x] + v[2x + 1])`, halving it.
pub(crate) fn bind_low(v: &mut Vec<F192>, chi: F192) {
    let half = v.len() / 2;
    assert!(
        v.len() == 2 * half && half.is_power_of_two(),
        "a table of at least two, a power of two"
    );
    // Slot `x` is written after slots `2x` and `2x + 1` are read, so the bind runs in place.
    for x in 0..half {
        let (v0, v1) = (v[2 * x], v[2 * x + 1]);
        v[x] = v0 + chi * (v0 + v1);
    }
    v.truncate(half);
}

/// Rounds `t` and `t + 1` from the stored tables, folding the challenges still pending on them first.
///
/// - `ins` are the `(a, b, c)` tables, one or two variables short of level `t`.
/// - `pending` are those variables' challenges, lowest first; each output folds `2^pending.len()` inputs.
/// - `outs` receive the level-`t` tables, every slot written.
/// - `r_eq` are the eq challenges of the variables round `t` does not bind.
/// - Each output covers `2^out_log` bits of the witness `padding` describes.
///
/// ```text
///     two pending:          read n values at level t - 2, write n / 4 at level t, send rounds t and t + 1
///     one round at a time:  n + n / 2 + n / 2 + n / 4 for the same two rounds
/// ```
///
/// The rounds are built from each quad of folded values while they are in registers, as in the bit pass.
pub(crate) fn table_pass(
    ins: [&[F192]; 3],
    outs: [&mut [MaybeUninit<F192>]; 3],
    pending: &[F192],
    r_eq: &[F192],
    padding: &Padding,
    out_log: usize,
) -> RoundPair {
    let sums = match *pending {
        [rho] => table_pass_kernel::<1>(ins, outs, [rho, F192::ZERO], r_eq, padding, out_log),
        [rho_0, rho_1] => table_pass_kernel::<2>(ins, outs, [rho_0, rho_1], r_eq, padding, out_log),
        _ => panic!("one or two pending challenges"),
    };
    RoundPair::from_sums(sums, r_eq[0])
}

/// The table pass for `K` pending challenges, `rhos[..K]`: the eight sums the pair is read from.
///
/// The identical tail's outputs are copies of its last group's.
fn table_pass_kernel<const K: usize>(
    ins: [&[F192]; 3],
    mut outs: [&mut [MaybeUninit<F192>]; 3],
    rhos: [F192; 2],
    r_eq: &[F192],
    padding: &Padding,
    out_log: usize,
) -> [F192; 8] {
    let n_out = ins[0].len() >> K;
    assert!(ins.iter().all(|t| t.len() == n_out << K), "a, b, c have one length");
    assert!(
        outs.iter().all(|t| t.len() == n_out),
        "each output is the folded length"
    );
    let n_quads = n_out / 4;
    assert!(n_quads >= 1, "two rounds need four positions");
    assert_eq!(r_eq.len(), n_quads.trailing_zeros() as usize + 1);

    // `r_eq[0]` weights round `t`'s split by `v`; the rest weight the quads.
    // At most `2^7` high eq indices, one task each: enough for every worker at every table size.
    let SplitEq {
        low: eq_lo,
        high: eq_hi,
        ..
    } = SplitEq::with_high_vars(&r_eq[1..], EQ_HIGH_VARS);
    let lo_size = eq_lo.len();

    // The quads before the tail, in the pairs the outputs are published in.
    let quad_log = out_log + 2;
    let m = quad_log + n_quads.trailing_zeros() as usize;
    let tail = padding.tail(m, quad_log, quad_log + 1, r_eq);
    let head_quads = tail.map_or(n_quads, |t| t.head >> quad_log);

    // One task per high eq index: `lo_size` quads, `4 * lo_size` outputs of each table.
    let (chunk_in, chunk_out) = ((4 * lo_size) << K, 4 * lo_size);
    let chunks = outs.each_mut().map(|o| Chunks::new(o, chunk_out));

    // The weights of the composed fold, `rho_0`, `rho_1` and `rho_0 rho_1`, one per lane.
    let splat = |w: F192| (w, w, w, w);
    let [w0, w1, w01] = [rhos[0], rhos[1], rhos[0] * rhos[1]].map(splat);

    // Four outputs of one table, each folded from its `2^K` inputs in one step:
    //
    //     one pending:   z = x_0 + rho_0 (x_0 + x_1)
    //     two pending:   z = x_0 + rho_0 (x_0 + x_1) + rho_1 (x_0 + x_2) + rho_0 rho_1 (x_0 + x_1 + x_2 + x_3)
    //
    // The two-pending form is the two binds expanded, so its products are independent rather than a chain.
    let fold_quad = |g: &[F192]| -> [F192; 4] {
        // Input `i` of output `j`.
        let g = &g[..4 << K];
        let x = |j: usize, i: usize| g[(j << K) + i];
        let lane = |f: &dyn Fn(usize) -> F192| (f(0), f(1), f(2), f(3));
        let d = mul_quad(lane(&|j| x(j, 0) + x(j, 1)), w0);
        let z = (x(0, 0) + d.0, x(1, 0) + d.1, x(2, 0) + d.2, x(3, 0) + d.3);
        if K == 1 {
            return [z.0, z.1, z.2, z.3];
        }
        let e = mul_quad(lane(&|j| x(j, 0) + x(j, 2)), w1);
        let f = mul_quad(lane(&|j| x(j, 0) + x(j, 1) + x(j, 2) + x(j, 3)), w01);
        [z.0 + e.0 + f.0, z.1 + e.1 + f.1, z.2 + e.2 + f.2, z.3 + e.3 + f.3]
    };

    let mut sums = parallel::map_reduce(
        head_quads.div_ceil(lo_size),
        || [F192::ZERO; 8],
        |hi| {
            // SAFETY: task `hi` takes chunk `hi` of each output once, and the buffers outlive the dispatch.
            let mut outs = chunks.each_ref().map(|c| unsafe { c.get(hi) });
            let ins = ins.map(|t| &t[hi * chunk_in..(hi + 1) * chunk_in]);
            let stream = Stream::new();
            let mut acc = [F192Unreduced::ZERO; 8];
            // Two quads of a table are eight outputs, three whole cache lines, published at once.
            let mut staged = [[F192::ZERO; 8]; 3];
            let n_q = lo_size.min(head_quads - hi * lo_size);
            for q in 0..n_q {
                let [a, b, c] = ins.map(|t| fold_quad(&t[(4 * q) << K..(4 * (q + 1)) << K]));
                add_quad(&mut acc, eq_lo[q], quad_pair_terms(a, b, c));

                // Publish the folded values without a read: nothing touches them before the next pass.
                let half = 4 * (q % 2);
                for (stage, folded) in staged.iter_mut().zip([a, b, c]) {
                    stage[half..half + 4].copy_from_slice(&folded);
                }
                if q % 2 == 1 {
                    for (out, stage) in outs.iter_mut().zip(&staged) {
                        stream.write(&mut out[4 * (q - 1)..4 * (q + 1)], stage);
                    }
                } else if q + 1 == n_q {
                    // An odd last quad is stored alone.
                    for (out, stage) in outs.iter_mut().zip(&staged) {
                        out[4 * q..4 * q + 4].write_copy_of_slice(&stage[..4]);
                    }
                }
            }
            acc.map(|s| eq_hi[hi] * s.reduce())
        },
        |x, y| std::array::from_fn(|i| x[i] + y[i]),
    );

    if let Some(tail) = tail {
        // The last group is folded in place, then copied over the rest of the tail.
        let group_len = 1 << (tail.group_log - out_log);
        let group_ins = ins.map(|t| &t[t.len() - (group_len << K)..]);
        let group_sums = table_pass_kernel::<K>(
            group_ins,
            outs.each_mut().map(|o| &mut o[n_out - group_len..]),
            rhos,
            &r_eq[..tail.r_inner],
            &padding.without_tail(),
            out_log,
        );
        for (s, g) in sums.iter_mut().zip(group_sums) {
            *s += tail.weight * g;
        }
        copy_group(outs, head_quads * 4, group_len);
    }
    sums
}

/// Copy each table's last `group_len` values over its values from `head` on.
fn copy_group(tables: [&mut [MaybeUninit<F192>]; 3], head: usize, group_len: usize) {
    // Whole groups per copy task, about `2^12` values.
    let task = group_len.max(1 << 12);
    for t in tables {
        let tail = &mut t[head..];
        let (body, group) = tail.split_at_mut(tail.len() - group_len);
        let group = &*group;
        parallel::chunks_mut(body, task, |_, dst| {
            for d in dst.chunks_exact_mut(group_len) {
                d.copy_from_slice(group);
            }
        });
    }
}

/// The bit pass on coefficient planes, eight quads to a packing, so no product packs or unpacks a value.
///
/// The fold leaves each table's values as three registers per quad position, one per coefficient:
///
/// ```text
///     plane k, register uv + 4g, word l   =   coefficient k of position 4 (8g + l) + uv
/// ```
///
/// That is exactly the field packing's own layout, eight elements a register per coefficient.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi",
    target_feature = "avx512f",
    target_feature = "vpclmulqdq"
))]
mod planar {
    use core::arch::x86_64::__m512i;

    use primitives::bit_fold::{BLOCK, BitFold};
    use primitives::field::gf2_64x3::x86_64::{F192x8, F192x8Sum};
    use primitives::field::{F192, F192Unreduced};

    /// The eq table, eight consecutive weights a packing, one register per coefficient.
    pub(super) fn planes(values: &[F192]) -> Vec<F192x8> {
        let (groups, rest) = values.as_chunks::<8>();
        assert!(rest.is_empty(), "whole groups of eight");
        groups
            .iter()
            .map(|g| {
                // SAFETY: eight words are one register, and any bit pattern is a valid one.
                let plane =
                    |k: fn(&F192) -> u64| unsafe { core::mem::transmute::<[u64; 8], __m512i>(g.each_ref().map(k)) };
                F192x8([plane(|e| e.c0), plane(|e| e.c1), plane(|e| e.c2)])
            })
            .collect()
    }

    /// The eight pair sums over the quads from `quad_first`, sixteen quads per pair of eq packings.
    ///
    /// The eq weight multiplies the four `a` values first, so every term is a product of two operands:
    ///
    /// ```text
    ///     eq (a_1 b_1 + c_1) = (eq a_1) b_1 + eq c_1          eq (a_0 + a_1)(b_0 + b_1) = (eq a_0 + eq a_1)(b_0 + b_1)
    /// ```
    ///
    /// Fifteen products per quad: the four `eq a` reduced, the eleven terms summed unreduced.
    #[inline]
    #[target_feature(
        enable = "avx512f",
        enable = "avx512bw",
        enable = "avx512vbmi",
        enable = "gfni",
        enable = "vpclmulqdq"
    )]
    pub(super) fn quad_sums<const CHUNKS: usize>(
        fold: &BitFold,
        rows: [&[[u8; CHUNKS]]; 2],
        quad_first: usize,
        eq: &[F192x8],
        live: impl Fn(usize) -> bool,
    ) -> [F192Unreduced; 8] {
        let mut acc = [F192x8Sum::zero(); 8];
        // Sixteen quads per folded block, two packings of eight.
        for (b, eq) in eq.as_chunks::<2>().0.iter().enumerate() {
            let q0 = quad_first + (BLOCK / 4) * b;
            // A block wholly in padding folds to zero.
            if !(q0..q0 + BLOCK / 4).any(&live) {
                continue;
            }

            // Fold the block's `a`, `b` and `c = a AND b` rows straight into planes.
            let [ra, rb]: [&[[u8; CHUNKS]; BLOCK]; 2] =
                rows.map(|t| t[4 * q0..4 * q0 + BLOCK].try_into().expect("a block"));
            let mut rc = [[0u8; CHUNKS]; BLOCK];
            super::and_rows(ra, rb, &mut rc);
            let [pa, pb, pc] = [ra, rb, &rc].map(|t| fold.fold_quads::<CHUNKS>(t));

            for (g, &e) in eq.iter().enumerate() {
                // Position `uv` of the eight quads `8g ..`, as one packing.
                let at = |p: &[[__m512i; 8]; 3], uv: usize| F192x8(p.each_ref().map(|plane| plane[uv + 4 * g]));
                let [a0, a1, a2, a3] = [0, 1, 2, 3].map(|uv| e.mul(at(&pa, uv)));
                let [b0, b1, b2, b3] = [0, 1, 2, 3].map(|uv| at(&pb, uv));
                let [c1, c2, c3] = [1, 2, 3].map(|uv| at(&pc, uv));

                // The leading coefficients along `u` and along `v`, as in the scalar terms.
                let (du0, du1, dv0, dv1) = (a0.add(a1), a2.add(a3), a0.add(a2), a1.add(a3));
                let (eu0, eu1, ev0, ev1) = (b0.add(b1), b2.add(b3), b0.add(b2), b1.add(b3));

                // The eight sums, in the slots the pair is read from.
                acc[0].mul_add(a1, b1);
                acc[0].mul_add(e, c1);
                acc[1].mul_add(a3, b3);
                acc[1].mul_add(e, c3);
                acc[2].mul_add(du0, eu0);
                acc[3].mul_add(du1, eu1);
                acc[4].mul_add(a2, b2);
                acc[4].mul_add(e, c2);
                acc[5].mul_add(dv0, ev0);
                acc[6].mul_add(dv1, ev1);
                acc[7].mul_add(du0.add(du1), eu0.add(eu1));
            }
        }
        acc.map(|s| s.total())
    }
}

#[cfg(test)]
mod tests {
    use primitives::multilinear::skip_lagrange_weights;
    use primitives::test_util::Rng;

    use super::*;
    use crate::zerocheck::round1::tests::pack_bits;

    const K_SKIP: usize = crate::zerocheck::K_SKIP;

    /// The bits of a cube folded at `z` over the skip: one value per position past it.
    fn fold_at_z(bits: &[bool], lagrange: &[F192]) -> Vec<F192> {
        (bits.chunks(1 << K_SKIP))
            .map(|row| (row.iter().zip(lagrange)).fold(F192::ZERO, |acc, (&bit, &w)| if bit { acc + w } else { acc }))
            .collect()
    }

    /// A random honest witness over `2^m` bits, `c = a AND b`: the bits, then `a` and `b` packed.
    fn random_witness(rng: &mut Rng, m: usize) -> ([Vec<bool>; 3], [Vec<u8>; 2]) {
        let (a, b) = (rng.bits(1 << m), rng.bits(1 << m));
        let c = a.iter().zip(&b).map(|(x, y)| x & y).collect();
        let packed = [pack_bits(&a), pack_bits(&b)];
        ([a, b, c], packed)
    }

    fn packed(p: &[Vec<u8>; 2]) -> PackedWitness<'_> {
        PackedWitness { a: &p[0], b: &p[1] }
    }

    /// Bind every table's low variable at `chi`.
    fn bind_all(tables: &mut [Vec<F192>; 3], chi: F192) {
        for t in tables {
            bind_low(t, chi);
        }
    }

    /// One round of the stored tables.
    fn round_of(t: &[Vec<F192>; 3], r_eq: &[F192]) -> (F192, F192) {
        single_round([&t[0], &t[1], &t[2]], r_eq)
    }

    #[test]
    fn single_round_is_the_round_polynomial() {
        // Invariant: G(0), G(1) and G(inf) interpolate the round polynomial, which has degree two.
        //
        //     G(X) = sum_x eq(r_eq, x) (a(X, x) b(X, x) + c(X, x))
        //     G(X) = G(0) (1 + X) + G(1) X + G(inf) X (1 + X)          in characteristic 2
        let mut rng = Rng::new(55);
        let t: [Vec<F192>; 3] = std::array::from_fn(|_| rng.ext_vec(16));
        let r_eq = rng.ext_vec(3);
        let eq = eq_table(&r_eq);
        let at = |x: F192| {
            (eq.iter().enumerate()).fold(F192::ZERO, |acc, (i, &e)| {
                let [a, b, c] = t.each_ref().map(|v| v[2 * i] + x * (v[2 * i] + v[2 * i + 1]));
                acc + e * (a * b + c)
            })
        };
        let (g1, g_inf) = round_of(&t, &r_eq);
        let g0 = at(F192::ZERO);
        assert_eq!(g1, at(F192::ONE));
        let x = rng.ext();
        assert_eq!(at(x), g0 * (F192::ONE + x) + g1 * x + g_inf * x * (F192::ONE + x));
    }

    #[test]
    fn bit_passes_match_the_naive_route() {
        // Invariant: both bit passes send round t, and round t + 1 once rho_t is known; the storing one stores level t.
        //
        // Naive route: fold the bits at z over the skip, bind rho_1..rho_t one at a time, then sum each round.
        for m in [13, 14, 15] {
            let mut rng = Rng::new(0xB17_0000 + m as u64);
            let (bits, packed_bits) = random_witness(&mut rng, m);
            let r_rest = rng.ext_vec(m - K_SKIP);
            let rho = rng.ext_vec(m - K_SKIP);
            let lagrange = skip_lagrange_weights(K_SKIP, rng.ext());
            let dense = Padding::dense(m);

            // Level 0 of the naive route.
            let mut tables = bits.each_ref().map(|b| fold_at_z(b, &lagrange));
            for t in 0..=4 {
                let fold = BitFold::at_level(&lagrange, &rho[..t]);
                let r_eq = &r_rest[t + 1..];
                let expected = round_of(&tables, r_eq);

                let pair = bit_pass(packed(&packed_bits), &fold, r_eq, &dense);
                let (stored_pair, stored) = bit_pass_storing(packed(&packed_bits), &fold, r_eq, &dense);
                assert_eq!(stored, tables, "stored tables, m={m}, t={t}");

                bind_all(&mut tables, rho[t]);
                let next = round_of(&tables, &r_rest[t + 2..]);
                for (pair, name) in [(pair, "pass"), (stored_pair, "storing pass")] {
                    assert_eq!(pair.first, expected, "{name} round t, m={m}, t={t}");
                    assert_eq!(pair.second(rho[t]), next, "{name} round t + 1, m={m}, t={t}");
                }
            }
        }
    }

    #[test]
    fn bit_passes_skip_padding_exactly() {
        // Invariant: on blocks whose bits past the useful ones are zero, skipping them changes no message or table.
        //
        // Fixture state, (m, k_log, useful): BLAKE2s, an odd boundary, and two blocks per row at level 4.
        for (m, k_log, useful) in [(17usize, 14usize, 16_000usize), (17, 14, 15_409), (18, 15, 31_401)] {
            let mut rng = Rng::new(0xFADE_F00D + (k_log * 31 + useful) as u64);
            let mut bit = |i: usize| i % (1 << k_log) < useful && rng.bit();
            let a: Vec<bool> = (0..1 << m).map(&mut bit).collect();
            let b: Vec<bool> = (0..1 << m).map(&mut bit).collect();
            let packed_bits = [pack_bits(&a), pack_bits(&b)];
            let padding = Padding {
                k_log,
                useful_bits: useful,
                live_blocks: usize::MAX,
            };
            let lagrange = skip_lagrange_weights(K_SKIP, rng.ext());
            let r_rest = rng.ext_vec(m - K_SKIP);
            let rho = rng.ext_vec(4);
            for t in 0..=4 {
                let fold = BitFold::at_level(&lagrange, &rho[..t]);
                let r_eq = &r_rest[t + 1..];
                let run = |p: &Padding| {
                    (
                        bit_pass(packed(&packed_bits), &fold, r_eq, p),
                        bit_pass_storing(packed(&packed_bits), &fold, r_eq, p),
                    )
                };
                assert_eq!(run(&Padding::dense(m)), run(&padding), "m={m}, useful={useful}, t={t}");
            }
        }
    }

    #[test]
    fn a_table_pass_is_one_round_at_a_time() {
        // Invariant: folding the pending challenges and sending two rounds in one pass is the tables and messages of
        // folding and summing one round at a time.
        //
        // Fixture state: one or two pending challenges, from one quad of outputs up to 2^10 of them.
        let mut rng = Rng::new(0x7AB1E);
        for k in [1, 2] {
            for log_out in [2, 3, 6, 12] {
                let tables: [Vec<F192>; 3] = std::array::from_fn(|_| rng.ext_vec(1 << (log_out + k)));
                let pending = rng.ext_vec(k);
                let r_eq = rng.ext_vec(log_out - 1);
                let rho_t = rng.ext();

                // Reference: bind each pending challenge, sum round t, bind rho_t, sum round t + 1.
                let mut naive = tables.clone();
                for &rho in &pending {
                    bind_all(&mut naive, rho);
                }
                let level = naive.clone();
                let first = round_of(&naive, &r_eq);
                bind_all(&mut naive, rho_t);
                let second = round_of(&naive, &r_eq[1..]);

                // The pass under test.
                let mut outs: [Box<[MaybeUninit<F192>]>; 3] =
                    std::array::from_fn(|_| Box::new_uninit_slice(1 << log_out));
                let pair = table_pass(
                    tables.each_ref().map(Vec::as_slice),
                    outs.each_mut().map(|o| &mut o[..]),
                    &pending,
                    &r_eq,
                    &Padding::dense(log_out),
                    0,
                );
                // SAFETY: the pass writes every slot of its outputs.
                let outs = outs.map(|o| unsafe { o.assume_init() }.into_vec());
                assert_eq!(outs, level, "tables, k={k}, log_out={log_out}");
                assert_eq!(pair.first, first, "round t, k={k}, log_out={log_out}");
                assert_eq!(pair.second(rho_t), second, "round t + 1, k={k}, log_out={log_out}");
            }
        }
    }
}
