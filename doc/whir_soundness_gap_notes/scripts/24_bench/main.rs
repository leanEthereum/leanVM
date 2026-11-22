//! Scratch benchmark of the DEEP fold's point evaluations (researcher 24). Not part of the repository.
//!
//! bench24 <threads> <kappa> <n_lanes> <reps> [k-kernel] [e-kernel] [sweep|nosweep]
//!
//! The stack is `n_lanes` lanes of `2^kappa` words of K, lane `u` at `u << kappa`, as `whir::commit` takes it.
//! A point is `(theta, zeta)` in E^2; its answer is `sum_u theta^e(u) P_u(zeta)`, `P_u` the lane in the novel basis.

#[global_allocator]
static ALLOCATOR: allocator::Jemalloc = allocator::Jemalloc;

use core::arch::aarch64::*;
use core::mem::transmute;
use primitives::field::gf2_64::mul_wide;
use primitives::field::neon::xor3_u64;
use primitives::field::{F64, F128, F128Unreduced, Weights8, dot_base, mul_by_g};
use primitives::multilinear::mle_eval_par;
use std::hint::black_box;
use std::time::Instant;

const ELL: usize = 6;
const S_MAX: usize = 16;

fn mix(i: u64) -> u64 {
    let mut z = i.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

struct Rng(u64);
impl Rng {
    fn u(&mut self) -> u64 {
        self.0 += 1;
        mix(self.0)
    }
    fn e(&mut self) -> F128 {
        F128::new(self.u(), self.u())
    }
}

// ---------------------------------------------------------------------------------------------------------
// Novel basis at a point of E (crates/verifier/src/whir.rs, `Subspace`, with the argument in E)
// ---------------------------------------------------------------------------------------------------------

struct Subspace {
    roots: Vec<F64>,
    inverses: Vec<F64>,
}

impl Subspace {
    fn new(mu: usize) -> Self {
        let mut roots = vec![F64(1)];
        let mut layer: Vec<F64> = (1..=mu).map(|i| F64(1 << i)).collect();
        for _ in 0..mu {
            let root = roots[roots.len() - 1];
            for v in &mut layer {
                *v = v.square() + root * *v;
            }
            roots.push(layer.remove(0));
        }
        let inverses = roots.iter().map(|r| r.inv()).collect();
        Self { roots, inverses }
    }

    /// `What_i(zeta)` for `i <= mu`.
    fn at(&self, zeta: F128) -> Vec<F128> {
        let mut basis = zeta;
        let mut values = Vec::with_capacity(self.roots.len());
        for (&root, &inverse) in self.roots.iter().zip(&self.inverses) {
            values.push(basis.mul_base(inverse));
            basis = basis.square() + basis.mul_base(root);
        }
        values
    }
}

#[derive(Clone)]
struct Pt {
    theta: F128,
    zeta: F128,
    what: Vec<F128>,
}

fn points(sub: &Subspace, rng: &mut Rng, s: usize) -> Vec<Pt> {
    (0..s)
        .map(|_| {
            let (theta, zeta) = (rng.e(), rng.e());
            Pt {
                theta,
                zeta,
                what: sub.at(zeta),
            }
        })
        .collect()
}

/// `out[c] = prod_{k: c_k = 1} factors[k]`: the novel-basis weights `X_c(zeta)` from `What_k(zeta)`.
fn tensor(factors: &[F128]) -> Vec<F128> {
    let mut out = Vec::with_capacity(1 << factors.len());
    out.push(F128::ONE);
    for &f in factors {
        for i in 0..out.len() {
            let v = out[i] * f;
            out.push(v);
        }
    }
    out
}

/// The lane weights after `j` of `ell` rounds: lane `u' = (u_{j+1}, .., u_ell)`, `u_{j+1}` its bit 0, weighs
/// `theta^{e_j(u')}`, `e_j(u') = sum_{k > j} (1 - u_k) 2^(k-1)`.
fn lane_weights(theta: F128, j: usize, ell: usize) -> Vec<F128> {
    let mut t = theta;
    for _ in 0..j {
        t = t.square();
    }
    let mut out = vec![F128::ONE];
    for _ in j..ell {
        let mut next: Vec<F128> = out.iter().map(|&w| w * t).collect();
        next.extend_from_slice(&out);
        out = next;
        t = t.square();
    }
    out
}

// ---------------------------------------------------------------------------------------------------------
// Kernels
// ---------------------------------------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq)]
enum Kernel {
    /// Rows of `2^l` elements, one `dot_base` (K) or one unreduced-product sum (E) per point and row.
    Portable { l: usize },
    /// Rows of `2^l` elements cut into blocks of `b` 64-bit words; per block, every point in turn.
    Neon { l: usize, b: usize },
    /// Rows of `2^l` words of K, folded variable by variable per point.
    Fold { l: usize },
    /// Rows of `2^l` elements; the points in groups of at most `g`, each group one walk of the row with the group's
    /// accumulators in registers.
    Inter { l: usize, g: usize },
    /// [`Kernel::Inter`] for rows of E, with three multiplications per element and point.
    Kara { l: usize, g: usize },
}

impl Kernel {
    fn l(self) -> usize {
        match self {
            Kernel::Portable { l } | Kernel::Neon { l, .. } | Kernel::Fold { l } | Kernel::Inter { l, .. } | Kernel::Kara { l, .. } => l,
        }
    }
    fn parse(spec: &str) -> Self {
        let (kind, rest) = spec.split_at(1);
        let mut it = rest.split('.').map(|x| x.parse::<usize>().unwrap());
        let l = it.next().unwrap();
        match kind {
            "p" => Kernel::Portable { l },
            "f" => Kernel::Fold { l },
            "n" => Kernel::Neon {
                l,
                b: it.next().unwrap(),
            },
            "i" => Kernel::Inter {
                l,
                g: it.next().unwrap(),
            },
            "k" => Kernel::Kara {
                l,
                g: it.next().unwrap(),
            },
            _ => panic!("kernel spec"),
        }
    }
    fn name(self) -> String {
        match self {
            Kernel::Portable { l } => format!("p{l}"),
            Kernel::Fold { l } => format!("f{l}"),
            Kernel::Neon { l, b } => format!("n{l}.{b}"),
            Kernel::Inter { l, g } => format!("i{l}.{g}"),
            Kernel::Kara { l, g } => format!("k{l}.{g}"),
        }
    }
}

#[inline(always)]
fn clmul_lo(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
    // SAFETY: aes is enabled at compile time (target-cpu=native on Apple silicon).
    unsafe { transmute::<u128, uint64x2_t>(vmull_p64(vgetq_lane_u64::<0>(a), vgetq_lane_u64::<0>(b))) }
}

#[inline(always)]
fn clmul_hi(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
    // SAFETY: as above.
    unsafe { transmute::<u128, uint64x2_t>(vmull_high_p64(vreinterpretq_p64_u64(a), vreinterpretq_p64_u64(b))) }
}

/// A 128-bit carry-less polynomial modulo `x^64 + x^4 + x^3 + x + 1`.
#[inline(always)]
fn reduce128(d: [u64; 2]) -> u64 {
    let t = mul_wide(d[1], 0x1B);
    d[0] ^ (t as u64) ^ (mul_wide((t >> 64) as u64, 0x1B) as u64)
}

/// One row against every point's weights, the fused inner kernel.
///
/// `row` is 64-bit words: two words of K, or the two limbs of one element of E, per 128-bit load. `wts` holds four
/// words per load, in the order the row is walked: for each block of `b` words, for each point, for each load.
///
/// ```text
///     K:  [w_2i.c0, w_2i+1.c0 | w_2i.c1, w_2i+1.c1]      load = (k_2i, k_2i+1)
///     E:  [w.c0,    w.c1      | w.c1,    w.c0 + x w.c1]  load = (a.c0, a.c1)
/// ```
///
/// Either way the `y^0` coefficient of the sum is the two half products against the first pair and the `y^1`
/// coefficient the two against the second: four PMULL and two EOR3 per load and point, no shuffle, one reduction
/// per row and point.
///
/// # Safety
/// `row.len()` is a multiple of `b`, `b` is even, and `wts.len() == 2 * row.len() * s`.
#[inline(always)]
unsafe fn row_dots_neon(row: &[u64], wts: &[u64], s: usize, b: usize, out: &mut [F128; S_MAX]) {
    unsafe {
        let zero = vdupq_n_u64(0);
        let mut acc = [[zero; 2]; S_MAX];
        let loads = b / 2;
        let mut k = row.as_ptr();
        let mut w = wts.as_ptr();
        for _ in 0..row.len() / b {
            for a in acc[..s].iter_mut() {
                let (mut a0, mut a1) = (a[0], a[1]);
                if loads == 1 {
                    let kk = vld1q_u64(k);
                    let (w0, w1) = (vld1q_u64(w), vld1q_u64(w.add(2)));
                    a0 = xor3_u64(a0, clmul_lo(kk, w0), clmul_hi(kk, w0));
                    a1 = xor3_u64(a1, clmul_lo(kk, w1), clmul_hi(kk, w1));
                } else {
                    // Two chains per coefficient, so the loop is bound by the multiplier and not by the XOR latency.
                    let (mut b0, mut b1) = (zero, zero);
                    let mut i = 0;
                    while i < loads {
                        let kk = vld1q_u64(k.add(2 * i));
                        let (w0, w1) = (vld1q_u64(w.add(4 * i)), vld1q_u64(w.add(4 * i + 2)));
                        a0 = xor3_u64(a0, clmul_lo(kk, w0), clmul_hi(kk, w0));
                        a1 = xor3_u64(a1, clmul_lo(kk, w1), clmul_hi(kk, w1));
                        let kk = vld1q_u64(k.add(2 * i + 2));
                        let (w0, w1) = (vld1q_u64(w.add(4 * i + 4)), vld1q_u64(w.add(4 * i + 6)));
                        b0 = xor3_u64(b0, clmul_lo(kk, w0), clmul_hi(kk, w0));
                        b1 = xor3_u64(b1, clmul_lo(kk, w1), clmul_hi(kk, w1));
                        i += 2;
                    }
                    a0 = veorq_u64(a0, b0);
                    a1 = veorq_u64(a1, b1);
                }
                *a = [a0, a1];
                w = w.add(4 * loads);
            }
            k = k.add(b);
        }
        for m in 0..s {
            let d0 = transmute::<uint64x2_t, [u64; 2]>(acc[m][0]);
            let d1 = transmute::<uint64x2_t, [u64; 2]>(acc[m][1]);
            out[m] = F128::new(reduce128(d0), reduce128(d1));
        }
    }
}

/// One walk of a row for a group of `G` points: every 128-bit load of the row meets the group's `G` weights, and
/// the accumulators stay in registers, each its own dependency chain. `U` consecutive loads keep accumulators of
/// their own, so a small group still has enough chains to keep the multiplier busy.
///
/// `wts` holds four words per load and point, `[load][point]`, in the layout of [`row_dots_neon`].
///
/// # Safety
/// `wts` points at `2 * row.len() * G` words, and `row.len()` is a multiple of `2 * U`.
#[inline(always)]
unsafe fn group_dots<const G: usize, const U: usize>(row: &[u64], wts: *const u64, out: &mut [F128]) {
    unsafe {
        let zero = vdupq_n_u64(0);
        let (mut a0, mut a1) = ([[zero; G]; U], [[zero; G]; U]);
        let (mut k, mut w) = (row.as_ptr(), wts);
        for _ in 0..row.len() / (2 * U) {
            for u in 0..U {
                let kk = vld1q_u64(k.add(2 * u));
                for m in 0..G {
                    let at = w.add(4 * (u * G + m));
                    let (w0, w1) = (vld1q_u64(at), vld1q_u64(at.add(2)));
                    a0[u][m] = xor3_u64(a0[u][m], clmul_lo(kk, w0), clmul_hi(kk, w0));
                    a1[u][m] = xor3_u64(a1[u][m], clmul_lo(kk, w1), clmul_hi(kk, w1));
                }
            }
            k = k.add(2 * U);
            w = w.add(4 * G * U);
        }
        for m in 0..G {
            let (mut d0, mut d1) = (a0[0][m], a1[0][m]);
            for u in 1..U {
                d0 = veorq_u64(d0, a0[u][m]);
                d1 = veorq_u64(d1, a1[u][m]);
            }
            let d0 = transmute::<uint64x2_t, [u64; 2]>(d0);
            let d1 = transmute::<uint64x2_t, [u64; 2]>(d1);
            out[m] = F128::new(reduce128(d0), reduce128(d1));
        }
    }
}

/// [`group_dots`] for a row of E with three multiplications per element and point instead of four.
///
/// With `a = a0 + a1 y` the element and `b = b0 + b1 y` the weight, `y^2 = x y + 1`:
///
/// ```text
///     p = a0 b0,  q = a1 b1,  r = (a0 + a1)(b0 + b1)
///     a b = (p + q) + (r + p + q + x q) y
/// ```
///
/// The sums of `p + q`, of `q` and of `r` are accumulated unreduced, and `x` times the sum of `q` is taken once
/// per row. `wts` holds `[b0, b1 | b0 + b1, 0]` per load and point.
///
/// # Safety
/// As [`group_dots`].
#[inline(always)]
unsafe fn group_dots_kara<const G: usize, const U: usize>(row: &[u64], wts: *const u64, out: &mut [F128]) {
    unsafe {
        let zero = vdupq_n_u64(0);
        let (mut a0, mut aq, mut ar) = ([[zero; G]; U], [[zero; G]; U], [[zero; G]; U]);
        let (mut k, mut w) = (row.as_ptr(), wts);
        for _ in 0..row.len() / (2 * U) {
            for u in 0..U {
                let kk = vld1q_u64(k.add(2 * u));
                let ks = veorq_u64(kk, vextq_u64::<1>(kk, kk));
                for m in 0..G {
                    let at = w.add(4 * (u * G + m));
                    let (wa, wb) = (vld1q_u64(at), vld1q_u64(at.add(2)));
                    let q = clmul_hi(kk, wa);
                    a0[u][m] = xor3_u64(a0[u][m], clmul_lo(kk, wa), q);
                    aq[u][m] = veorq_u64(aq[u][m], q);
                    ar[u][m] = veorq_u64(ar[u][m], clmul_lo(ks, wb));
                }
            }
            k = k.add(2 * U);
            w = w.add(4 * G * U);
        }
        for m in 0..G {
            let (mut d0, mut dq, mut dr) = (a0[0][m], aq[0][m], ar[0][m]);
            for u in 1..U {
                d0 = veorq_u64(d0, a0[u][m]);
                dq = veorq_u64(dq, aq[u][m]);
                dr = veorq_u64(dr, ar[u][m]);
            }
            let y0 = reduce128(transmute::<uint64x2_t, [u64; 2]>(d0));
            let q = reduce128(transmute::<uint64x2_t, [u64; 2]>(dq));
            let r = reduce128(transmute::<uint64x2_t, [u64; 2]>(veorq_u64(dr, d0)));
            out[m] = F128::new(y0, r ^ mul_by_g(F64(q)).0);
        }
    }
}

/// A row against `s` points, in groups of at most `g` ([`group_dots`], or [`group_dots_kara`]); `wts` from
/// [`inter_weights`].
///
/// # Safety
/// `wts.len() == 2 * row.len() * s`, and `row.len()` is a multiple of 8.
#[inline(always)]
unsafe fn row_dots_inter(row: &[u64], wts: &[u64], s: usize, g: usize, kara: bool, out: &mut [F128; S_MAX]) {
    macro_rules! dispatch {
        ($f:ident, $gs:expr, $w:expr, $o:expr) => {
            match $gs {
                1 => $f::<1, 4>(row, $w, $o),
                2 => $f::<2, 2>(row, $w, $o),
                3 => $f::<3, 1>(row, $w, $o),
                4 => $f::<4, 1>(row, $w, $o),
                5 => $f::<5, 1>(row, $w, $o),
                6 => $f::<6, 1>(row, $w, $o),
                7 => $f::<7, 1>(row, $w, $o),
                8 => $f::<8, 1>(row, $w, $o),
                9 => $f::<9, 1>(row, $w, $o),
                10 => $f::<10, 1>(row, $w, $o),
                11 => $f::<11, 1>(row, $w, $o),
                12 => $f::<12, 1>(row, $w, $o),
                _ => unreachable!(),
            }
        };
    }
    let mut m0 = 0;
    while m0 < s {
        let gs = g.min(s - m0);
        // SAFETY: the group at point `m0` starts at `2 * row.len() * m0` and holds `2 * row.len() * gs` words.
        let w = unsafe { wts.as_ptr().add(2 * row.len() * m0) };
        let o = &mut out[m0..m0 + gs];
        unsafe {
            if kara {
                dispatch!(group_dots_kara, gs, w, o)
            } else {
                dispatch!(group_dots, gs, w, o)
            }
        }
        m0 += gs;
    }
}

/// The four words of load `load` of a low table, for a row of K (two weights) or of E (one weight).
fn load_words(w: &[F128], ext: bool, load: usize) -> [u64; 4] {
    if ext {
        let e = w[load];
        [e.c0, e.c1, e.c1, e.c0 ^ mul_by_g(F64(e.c1)).0]
    } else {
        let (e, o) = (w[2 * load], w[2 * load + 1]);
        [e.c0, o.c0, e.c1, o.c1]
    }
}

/// The weights of [`row_dots_inter`]: `[group][load][point of the group]`.
fn inter_weights(low: &[Vec<F128>], ext: bool, g: usize, kara: bool) -> Vec<u64> {
    let loads = if ext { low[0].len() } else { low[0].len() / 2 };
    let mut out = Vec::with_capacity(4 * loads * low.len());
    for group in low.chunks(g) {
        for load in 0..loads {
            for w in group {
                if kara {
                    let e = w[load];
                    out.extend_from_slice(&[e.c0, e.c1, e.c0 ^ e.c1, 0]);
                } else {
                    out.extend_from_slice(&load_words(w, ext, load));
                }
            }
        }
    }
    out
}

/// The weights of [`row_dots_neon`] for the low tables `low[m]` (`2^l` weights each).
fn neon_weights(low: &[Vec<F128>], ext: bool, b: usize) -> Vec<u64> {
    let n = low[0].len();
    let row_words = if ext { 2 * n } else { n };
    assert!(b >= 2 && b.is_multiple_of(2) && row_words.is_multiple_of(b));
    if !ext {
        assert!(b == 2 || b.is_multiple_of(4));
    }
    let mut out = Vec::with_capacity(2 * row_words * low.len());
    for blk in 0..row_words / b {
        for w in low {
            for i in 0..b / 2 {
                out.extend_from_slice(&load_words(w, ext, blk * (b / 2) + i));
            }
        }
    }
    out
}

enum Tables {
    PortableK(Vec<Vec<Weights8>>),
    PortableE(Vec<Vec<F128>>),
    Neon { wts: Vec<u64>, b: usize },
    Inter { wts: Vec<u64>, g: usize, kara: bool },
    Fold(Vec<Vec<F128>>),
}

/// The per-lane evaluations `P_u(zeta_m)` of every `step`-th lane, in ONE pass over the data:
/// `out[(u / step) * s + m]`.
///
/// `data` is lanes of `2^kappa` elements, of K (`ext == false`, one word each) or of E (two words each). The weight
/// of coefficient `c` at point `m` is `X_c(zeta_m) = low_m[c mod 2^l] * high_m[c >> l]`; a row is `2^l` elements
/// of one lane, read once for all points.
fn lane_evals(data: &[u64], ext: bool, kappa: usize, step: usize, pts: &[Pt], kernel: Kernel) -> Vec<F128> {
    let s = pts.len();
    assert!(s >= 1 && s <= S_MAX);
    let ew = if ext { 2 } else { 1 };
    let l = kernel.l().min(kappa);
    assert!(l >= 3);
    let (row_words, lane_words) = (ew << l, ew << kappa);
    assert!(data.len().is_multiple_of(lane_words));
    let used = (data.len() / lane_words).div_ceil(step);
    let rpl = 1usize << (kappa - l);
    let low: Vec<Vec<F128>> = pts.iter().map(|p| tensor(&p.what[..l])).collect();
    let high_m: Vec<Vec<F128>> = pts.iter().map(|p| tensor(&p.what[l..kappa])).collect();
    let mut high = Vec::with_capacity(rpl * s);
    for h in 0..rpl {
        high.extend(high_m.iter().map(|t| t[h]));
    }
    let tables = match kernel {
        Kernel::Portable { .. } if !ext => Tables::PortableK(
            low.iter()
                .map(|t| t.as_chunks::<8>().0.iter().map(Weights8::new).collect())
                .collect(),
        ),
        Kernel::Portable { .. } => Tables::PortableE(low),
        Kernel::Neon { b, .. } => {
            let b = b.min(row_words);
            Tables::Neon {
                wts: neon_weights(&low, ext, b),
                b,
            }
        }
        Kernel::Inter { g, .. } => Tables::Inter {
            wts: inter_weights(&low, ext, g, false),
            g,
            kara: false,
        },
        Kernel::Kara { g, .. } => {
            assert!(ext);
            Tables::Inter {
                wts: inter_weights(&low, ext, g, true),
                g,
                kara: true,
            }
        }
        Kernel::Fold { .. } => {
            assert!(!ext);
            Tables::Fold(pts.iter().map(|p| p.what[..l].to_vec()).collect())
        }
    };
    let acc = parallel::map_reduce_with_state(
        used * rpl,
        || vec![F128::ZERO; if matches!(kernel, Kernel::Fold { .. }) { 1 << (l - 1) } else { 0 }],
        || vec![F128Unreduced::ZERO; used * s],
        |buf, acc, r| {
            let (ui, h) = (r / rpl, r % rpl);
            let at = ui * step * lane_words + h * row_words;
            let row = &data[at..at + row_words];
            let mut d = [F128::ZERO; S_MAX];
            match &tables {
                Tables::PortableK(low) => {
                    // SAFETY: `F64` is a transparent `u64`.
                    let row = unsafe { core::slice::from_raw_parts(row.as_ptr().cast::<F64>(), row.len()) };
                    for m in 0..s {
                        d[m] = dot_base(&low[m], row).reduce();
                    }
                }
                Tables::PortableE(low) => {
                    // SAFETY: `F128` is two `u64` limbs, `repr(C)`.
                    let row = unsafe { core::slice::from_raw_parts(row.as_ptr().cast::<F128>(), row.len() / 2) };
                    for m in 0..s {
                        let sum = low[m]
                            .iter()
                            .zip(row)
                            .fold(F128Unreduced::ZERO, |a, (&w, &f)| a ^ w.mul_unreduced(f));
                        d[m] = sum.reduce();
                    }
                }
                // SAFETY: the weights were laid out for rows of `row_words` words and blocks of `b`.
                Tables::Neon { wts, b } => unsafe { row_dots_neon(row, wts, s, *b, &mut d) },
                // SAFETY: the weights were laid out for rows of `row_words` words and `s` points.
                Tables::Inter { wts, g, kara } => unsafe { row_dots_inter(row, wts, s, *g, *kara, &mut d) },
                Tables::Fold(what) => {
                    for m in 0..s {
                        let w = &what[m];
                        for (i, o) in buf.iter_mut().enumerate() {
                            *o = F128::new(row[2 * i], 0) + w[0].mul_base(F64(row[2 * i + 1]));
                        }
                        let mut len = buf.len();
                        for &wk in &w[1..] {
                            len /= 2;
                            for i in 0..len {
                                buf[i] = buf[2 * i] + wk * buf[2 * i + 1];
                            }
                        }
                        d[m] = buf[0];
                    }
                }
            }
            for m in 0..s {
                acc[ui * s + m] ^= high[h * s + m].mul_unreduced(d[m]);
            }
        },
        |mut a, b| {
            a.iter_mut().zip(b).for_each(|(a, b)| *a ^= b);
            a
        },
    );
    acc.into_iter().map(F128Unreduced::reduce).collect()
}

/// The answers `y_m = sum_u theta_m^{e_j(u)} P_u(zeta_m)` from the per-lane evaluations of a tuple after `j` rounds
/// (or of the first halves of a tuple after `j - 1` rounds, which are indexed alike).
fn answers(vals: &[F128], pts: &[Pt], j: usize) -> Vec<F128> {
    let s = pts.len();
    pts.iter()
        .enumerate()
        .map(|(m, p)| {
            let lw = lane_weights(p.theta, j, ELL);
            vals.chunks_exact(s)
                .enumerate()
                .map(|(ui, v)| lw[ui] * v[m])
                .sum()
        })
        .collect()
}

/// Every carried scalar `phi^(j)_m`, `j = 1..=ell`, of points sampled at the commitment, from the per-lane
/// evaluations alone: the lane values fold like an opened row, at `zeta_m` instead of a domain point.
fn carried_from_lanes(vals: &[F128], pts: &[Pt], ell: usize, ch: &[(F128, F128)]) -> Vec<Vec<F128>> {
    let s = pts.len();
    pts.iter()
        .enumerate()
        .map(|(m, p)| {
            let mut v: Vec<F128> = (0..1usize << ell)
                .map(|u| vals.get(u * s + m).copied().unwrap_or(F128::ZERO))
                .collect();
            (1..=ell)
                .map(|j| {
                    let lw = lane_weights(p.theta, j, ell);
                    let phi: F128 = lw.iter().enumerate().map(|(u, &w)| w * v[2 * u]).sum();
                    let (alpha, beta) = ch[j - 1];
                    let a = alpha + beta * p.zeta;
                    v = (0..v.len() / 2).map(|u| v[2 * u + 1] + a * v[2 * u]).collect();
                    phi
                })
                .collect()
        })
        .collect()
}

// ---------------------------------------------------------------------------------------------------------
// Self-test
// ---------------------------------------------------------------------------------------------------------

fn novel_eval(coeffs: &[F128], what: &[F128]) -> F128 {
    coeffs
        .iter()
        .enumerate()
        .map(|(c, &p)| {
            let mut w = p;
            for (i, &f) in what.iter().enumerate() {
                if c >> i & 1 == 1 {
                    w *= f;
                }
            }
            assert!(c >> what.len() == 0);
            w
        })
        .sum()
}

/// `X * H` in the novel basis (the verifier's test helper).
fn times_x(coeffs: &[F128], roots: &[F64]) -> Vec<F128> {
    let a: Vec<F64> = (0..roots.len() - 1)
        .map(|i| roots[i + 1] * roots[i].square().inv())
        .collect();
    let mut out = vec![F128::ZERO; coeffs.len() + 1];
    for (c, &h) in coeffs.iter().enumerate() {
        let t = c.trailing_ones() as usize;
        assert!(t <= a.len());
        let mut product = F64(1);
        for (j, &a_j) in a.iter().enumerate().take(t) {
            out[c & !((1 << j) - 1)] += h.mul_base(product);
            product = product * a_j;
        }
        out[c + 1] += h.mul_base(product);
    }
    out
}

fn selftest() {
    let mut rng = Rng(77);
    // 1. Every kernel against the definition.
    let (kappa, n_lanes) = (12, 5);
    let sub = Subspace::new(kappa + 3);
    let pts = points(&sub, &mut rng, 3);
    let stack: Vec<u64> = (0..n_lanes << kappa).map(|_| rng.u()).collect();
    let ext: Vec<u64> = (0..2 * n_lanes << kappa).map(|_| rng.u()).collect();
    let reference = |data: &[u64], is_ext: bool| -> Vec<F128> {
        let ew = if is_ext { 2 } else { 1 };
        let mut out = Vec::new();
        for u in 0..n_lanes {
            for p in &pts {
                let lane: Vec<F128> = (0..1usize << kappa)
                    .map(|c| {
                        let at = (u << kappa) * ew + c * ew;
                        F128::new(data[at], if is_ext { data[at + 1] } else { 0 })
                    })
                    .collect();
                out.push(novel_eval(&lane, &p.what[..kappa]));
            }
        }
        out
    };
    let (ref_k, ref_e) = (reference(&stack, false), reference(&ext, true));
    let every_other =
        |r: &[F128]| -> Vec<F128> { r.chunks_exact(3).step_by(2).flatten().copied().collect::<Vec<_>>() };
    for spec in [
        "p10", "p8", "p3", "n10.1024", "n10.64", "n10.4", "n10.2", "n8.2", "n7.128", "n12.2", "n12.4096", "f10", "f4", "i10.12", "i8.3", "i8.2", "i7.1", "i9.6", "i12.4", "k9.12", "k7.4", "k7.3", "k8.2", "k6.1",
    ] {
        let k = Kernel::parse(spec);
        if !matches!(k, Kernel::Kara { .. }) {
            assert_eq!(lane_evals(&stack, false, kappa, 1, &pts, k), ref_k, "K {spec}");
            assert_eq!(lane_evals(&stack, false, kappa, 2, &pts, k), every_other(&ref_k), "K step {spec}");
        }
        if !matches!(k, Kernel::Fold { .. }) {
            assert_eq!(lane_evals(&ext, true, kappa, 1, &pts, k), ref_e, "E {spec}");
            assert_eq!(lane_evals(&ext, true, kappa, 2, &pts, k), every_other(&ref_e), "E step {spec}");
        }
    }
    // 2. The carried scalars from the lane values, against real affine folds of the lanes (note 14, Lemma E).
    let (kappa, ell) = (5, 3);
    let sub = Subspace::new(kappa + 4);
    let p = &points(&sub, &mut rng, 1)[0];
    let mut lanes: Vec<Vec<F128>> = (0..1 << ell)
        .map(|_| (0..1 << kappa).map(|_| F128::new(rng.u(), 0)).collect())
        .collect();
    let ch: Vec<(F128, F128)> = (0..ell).map(|_| (rng.e(), rng.e())).collect();
    let vals: Vec<F128> = lanes.iter().map(|l| novel_eval(l, &p.what)).collect();
    let derived = carried_from_lanes(&vals, core::slice::from_ref(p), ell, &ch);
    let ev = |lanes: &[Vec<F128>], j: usize| -> F128 {
        let lw = lane_weights(p.theta, j, ell);
        lanes.iter().zip(&lw).map(|(l, &w)| w * novel_eval(l, &p.what)).sum()
    };
    let mut v = ev(&lanes, 0);
    let mut theta_pow = p.theta;
    for j in 1..=ell {
        let firsts: Vec<Vec<F128>> = lanes.iter().step_by(2).cloned().collect();
        let phi = ev(&firsts, j);
        assert_eq!(phi, derived[0][j - 1], "phi of round {j}");
        let (alpha, beta) = ch[j - 1];
        lanes = lanes
            .as_chunks::<2>()
            .0
            .iter()
            .map(|[f, g]| {
                let xf = times_x(f, &sub.roots);
                (0..xf.len())
                    .map(|c| {
                        let at = |v: &[F128]| v.get(c).copied().unwrap_or(F128::ZERO);
                        at(g) + alpha * at(f) + beta * xf[c]
                    })
                    .collect()
            })
            .collect();
        v += (theta_pow + alpha + beta * p.zeta) * phi;
        assert_eq!(v, ev(&lanes, j), "carried value after round {j}");
        theta_pow = theta_pow.square();
    }
    assert_eq!(lanes.len(), 1);
    println!("selftest ok");
}

// ---------------------------------------------------------------------------------------------------------
// Harness
// ---------------------------------------------------------------------------------------------------------

struct Out {
    shape: String,
    threads: usize,
    reps: usize,
}

#[repr(C)]
struct Timespec {
    sec: i64,
    nsec: i64,
}

unsafe extern "C" {
    fn clock_gettime(clock: i32, ts: *mut Timespec) -> i32;
}

/// The process's CPU time in milliseconds, all threads (macOS's `CLOCK_PROCESS_CPUTIME_ID`).
fn cpu_ms() -> f64 {
    let mut ts = Timespec { sec: 0, nsec: 0 };
    // SAFETY: `ts` is a valid `timespec`.
    unsafe { clock_gettime(12, &mut ts) };
    ts.sec as f64 * 1e3 + ts.nsec as f64 * 1e-6
}

impl Out {
    /// Best, median and worst wall time of `reps` runs, and the least CPU time of one, in milliseconds.
    fn time<T>(&self, label: &str, mut f: impl FnMut() -> T) -> f64 {
        let mut cpu = f64::MAX;
        let mut t: Vec<f64> = (0..self.reps)
            .map(|_| {
                let (c0, t0) = (cpu_ms(), Instant::now());
                black_box(f());
                let wall = t0.elapsed().as_secs_f64() * 1e3;
                cpu = cpu.min(cpu_ms() - c0);
                wall
            })
            .collect();
        t.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let (min, med, max) = (t[0], t[t.len() / 2], t[t.len() - 1]);
        println!(
            "R\t{}\t{}\t{}\t{:.3}\t{:.3}\t{:.3}\t{:.3}",
            self.shape, self.threads, label, min, med, max, cpu
        );
        min
    }
}

fn random_words(n: usize, seed: u64) -> Vec<u64> {
    let mut v = vec![0u64; n];
    parallel::fill(&mut v, |i| mix(i as u64 ^ seed));
    v
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let arg = |i: usize, d: &str| args.get(i).cloned().unwrap_or_else(|| d.to_string());
    let threads: usize = arg(1, "0").parse().unwrap();
    let kappa: usize = arg(2, "20").parse().unwrap();
    let n_lanes: usize = arg(3, "40").parse().unwrap();
    let reps: usize = arg(4, "11").parse().unwrap();
    let kk = Kernel::parse(&arg(5, "i8.12"));
    let ke = Kernel::parse(&arg(6, "i7.12"));
    let mode = arg(7, "all");
    let sweep = mode == "sweep" || mode == "all";
    parallel::set_num_threads(threads);
    parallel::init();
    selftest();
    let threads = parallel::num_threads();
    let out = Out {
        shape: format!("k{kappa}x{n_lanes}"),
        threads,
        reps,
    };
    let mut rng = Rng(24);
    let sub = Subspace::new(kappa + 1);
    let pts = points(&sub, &mut rng, 12);
    let stack = random_words(n_lanes << kappa, 1);
    // SAFETY: `F64` is a transparent `u64`.
    let stack_k = unsafe { core::slice::from_raw_parts(stack.as_ptr().cast::<F64>(), stack.len()) };

    // (a) today's OOD sample: the stack's MLE at one point of kappa + 6 variables.
    let mle_point: Vec<F128> = (0..kappa + ELL).map(|_| rng.e()).collect();
    let a = out.time("a.mle_eval_par", || mle_eval_par(stack_k, &mle_point));

    // (b) s points as s separate passes, each the kernel today's OOD uses (rows of 2^10, `dot_base`).
    let p10 = Kernel::Portable { l: 10 };
    let separate = |s: usize, k: Kernel| {
        pts[..s]
            .iter()
            .map(|p| answers(&lane_evals(&stack, false, kappa, 1, core::slice::from_ref(p), k), core::slice::from_ref(p), 0)[0])
            .collect::<Vec<_>>()
    };
    for s in [1, 3, 6, 12] {
        out.time(&format!("b.separate.p10.s{s}"), || separate(s, p10));
    }
    for s in [1, 12] {
        out.time(&format!("b.separate.{}.s{s}", kk.name()), || separate(s, kk));
    }

    // (c) the same points in one pass.
    let fused = |s: usize, k: Kernel| {
        let vals = lane_evals(&stack, false, kappa, 1, &pts[..s], k);
        (answers(&vals, &pts[..s], 0), vals)
    };
    assert_eq!(fused(12, kk).0, separate(12, p10));
    if sweep {
        let kspecs = std::env::var("KSPECS").unwrap_or_else(|_| {
            "p10,n10.1024,i10.12,i9.12,i8.12,i7.12,i8.6,i7.6,i8.4,i7.4,i8.3,i7.3,i8.2,i8.1".to_string()
        });
        for spec in kspecs.split(',') {
            let k = Kernel::parse(spec);
            for s in [1, 3, 6, 12] {
                out.time(&format!("c.fused.{spec}.s{s}"), || fused(s, k));
            }
        }
        if std::env::var("KSPECS").is_err() {
            out.time("c.fused.f10.s12", || fused(12, Kernel::Fold { l: 10 }));
        }
    }
    for s in [1, 2, 3, 6, 8, 12] {
        out.time(&format!("c.best.{}.s{s}", kk.name()), || fused(s, kk));
    }
    if !sweep {
        for spec in ["p10", "n10.1024", "i8.12", "i8.3", "i10.4"] {
            out.time(&format!("c.fused.{spec}.s12"), || fused(12, Kernel::parse(spec)));
        }
    }

    // The folded lanes after rounds 1..5, E-valued: ceil(n_lanes / 2^j) lanes of 2^kappa coefficients (the j
    // coefficients a lane gains from the folds are left out). Random contents: no kernel here is data dependent.
    let folded: Vec<Vec<u64>> = (1..ELL)
        .map(|j| random_words(n_lanes.div_ceil(1 << j) << (kappa + 1), 10 + j as u64))
        .collect();
    let ext_pass = |j: usize, step: usize, s: usize, k: Kernel| {
        let vals = lane_evals(&folded[j - 1], true, kappa, step, &pts[..s], k);
        (answers(&vals, &pts[..s], if step == 2 { j + 1 } else { j }), vals)
    };
    assert_eq!(ext_pass(2, 1, 3, ke).0, ext_pass(2, 1, 3, Kernel::Portable { l: 9 }).0);
    if sweep {
        let especs = std::env::var("ESPECS")
            .unwrap_or_else(|_| "p9,n9.1024,i7.12,i7.4,i7.3,k9.12,k8.12,k7.12,k7.6,k7.4,k8.4,k7.3,k6.4".to_string());
        for spec in especs.split(',') {
            let k = Kernel::parse(spec);
            for (j, s) in [(1, 1), (1, 6), (1, 12), (3, 2)] {
                out.time(&format!("d.ext.{spec}.T{j}.s{s}"), || ext_pass(j, 1, s, k));
            }
        }
    }

    if mode == "sweep" {
        return;
    }
    if mode == "rr" {
        // Round robin: one run of each item per round, so that ratios within a round see the same machine load.
        // Each item runs `n` times back to back and reports the mean, with `n` chosen so that every item lasts
        // about as long: a loaded machine serves a short burst faster than sustained work.
        let rr_div: usize = std::env::var("RR_DIV").map_or(1, |v| v.parse().unwrap());
        let once = |label: &str, round: usize, f: &mut dyn FnMut()| {
            let n = match label {
                "a" | "fused1" | "ext.T1.s1" => 16,
                "level1.s9" => 24,
                "fused3" => 12,
                "ladder.rest" => 10,
                "fused6" => 6,
                "fused12" | "fused12.p10" => 3,
                _ => 2,
            };
            let n = (n / rr_div).max(1);
            let t0 = Instant::now();
            for _ in 0..n {
                f();
            }
            let ms = t0.elapsed().as_secs_f64() * 1e3 / n as f64;
            println!("RR\t{}\t{}\t{round}\t{label}\t{ms:.3}", out.shape, threads);
        };
        let ladder = [(1usize, 1usize), (2, 1), (3, 2), (4, 1), (5, 1)];
        let level1 = random_words(2 << kappa, 99);
        let l1 = match ke {
            Kernel::Inter { l, g } => Kernel::Inter { l: l.min(kappa - 4), g },
            k => k,
        };
        // Today's OOD evaluation `a` runs before and after every item, so each ratio is against its neighbours.
        let mut a = || {
            black_box(mle_eval_par(stack_k, &mle_point));
        };
        for round in 0..reps {
            once("a", round, &mut a);
            once("fused12", round, &mut || {
                black_box(fused(12, kk));
            });
            once("a", round, &mut a);
            once("fused6", round, &mut || {
                black_box(fused(6, kk));
            });
            once("a", round, &mut a);
            once("ladder.rest", round, &mut || {
                black_box(ladder.map(|(j, s)| ext_pass(j, 1, s, ke).0));
            });
            once("a", round, &mut a);
            once("fused3", round, &mut || {
                black_box(fused(3, kk));
            });
            once("a", round, &mut a);
            once("fused1", round, &mut || {
                black_box(fused(1, kk));
            });
            once("a", round, &mut a);
            once("sep12.p10", round, &mut || {
                black_box(separate(12, p10));
            });
            once("a", round, &mut a);
            once("fused12.p10", round, &mut || {
                black_box(fused(12, p10));
            });
            once("a", round, &mut a);
            once("ext.T1.s1", round, &mut || {
                black_box(ext_pass(1, 1, 1, ke));
            });
            once("a", round, &mut a);
            once("naive12", round, &mut || {
                black_box(lane_evals(&stack, false, kappa, 2, &pts, kk));
                for j in 1..ELL {
                    black_box(lane_evals(&folded[j - 1], true, kappa, 2, &pts, ke));
                }
            });
            once("a", round, &mut a);
            once("level1.s9", round, &mut || {
                black_box(lane_evals(&level1, true, kappa - 4, 1, &pts[..9], l1));
            });
            once("a", round, &mut a);
        }
        return;
    }

    // (d) the ladder for a list budget of 2^40: 6 points on the stack, then 1, 1, 2, 1, 1 on the folded lanes.
    let ladder = [(1usize, 1usize), (2, 1), (3, 2), (4, 1), (5, 1)];
    let d_first = out.time("d.ladder.first6", || fused(6, kk));
    let d_rest = out.time("d.ladder.rest", || {
        ladder.map(|(j, s)| ext_pass(j, 1, s, ke).0)
    });
    for (j, s) in ladder {
        out.time(&format!("d.ladder.T{j}.s{s}"), || ext_pass(j, 1, s, ke));
    }
    out.time("d.ladder.total", || (fused(6, kk), ladder.map(|(j, s)| ext_pass(j, 1, s, ke).0)));

    // (e) the carried scalars, as passes of their own: per round and point, one evaluation of the first halves.
    let naive = |first: usize, held: [usize; 5]| {
        let r1 = answers(&lane_evals(&stack, false, kappa, 2, &pts[..first], kk), &pts[..first], 1);
        let rest: Vec<Vec<F128>> = (1..ELL)
            .map(|j| {
                let s = held[j - 1];
                answers(&lane_evals(&folded[j - 1], true, kappa, 2, &pts[..s], ke), &pts[..s], j + 1)
            })
            .collect();
        (r1, rest)
    };
    let e_d12 = out.time("e.naive.batch12", || naive(12, [12; 5]));
    out.time("e.naive.batch12.round1", || lane_evals(&stack, false, kappa, 2, &pts, kk));
    out.time("e.naive.batch6", || naive(6, [6; 5]));
    out.time("e.naive.batch3", || naive(3, [3; 5]));
    let e_ladder = out.time("e.naive.ladder", || naive(6, [7, 8, 10, 11, 12]));
    // (e') the same scalars from the per-lane evaluations the fused pass already returns.
    let vals12 = fused(12, kk).1;
    let ch: Vec<(F128, F128)> = (0..ELL).map(|_| (rng.e(), rng.e())).collect();
    out.time("e.derived.batch12", || carried_from_lanes(&vals12, &pts, ELL, &ch));
    // Round 1's scalars are the first halves' answers: the derived ones against a pass over the even lanes.
    let direct = answers(&lane_evals(&stack, false, kappa, 2, &pts, kk), &pts, 1);
    let derived = carried_from_lanes(&vals12, &pts, ELL, &ch);
    assert!(direct.iter().zip(&derived).all(|(d, v)| *d == v[0]));

    // (g) the conversion at the level's end: the s point claims join the next level's weight, each as the tensor
    // `W_zeta(c) = X_c(zeta)` over the 2^kappa low coefficients, scaled by a power of lambda.
    let mut w = vec![F128::ZERO; 1 << kappa];
    let mut convert = |s: usize| {
        let l = 8;
        let lambda = pts[0].theta;
        let low: Vec<Vec<F128>> = pts[..s].iter().map(|p| tensor(&p.what[..l])).collect();
        let mut scale = F128::ONE;
        let high: Vec<Vec<F128>> = pts[..s]
            .iter()
            .map(|p| {
                scale *= lambda;
                tensor(&p.what[l..kappa]).iter().map(|&h| h * scale).collect()
            })
            .collect();
        parallel::chunks_mut(&mut w, 1 << l, |h, row| {
            for (c, o) in row.iter_mut().enumerate() {
                let sum = (0..s).fold(F128Unreduced::ZERO, |a, m| a ^ high[m][h].mul_unreduced(low[m][c]));
                *o += sum.reduce();
            }
        });
    };
    for s in [6, 12] {
        out.time(&format!("g.convert.s{s}"), || convert(s));
    }

    // (f) later levels: level 1's message is 2^kappa elements of E in 16 lanes (D: 9 points; ladder: 6, then 1, 1, 1
    // on halves), and each further level is a sixteenth of the one before.
    let level1 = random_words(2 << kappa, 99);
    let k1 = match ke {
        Kernel::Neon { l, b } => Kernel::Neon { l: l.min(kappa - 4), b },
        Kernel::Inter { l, g } => Kernel::Inter { l: l.min(kappa - 4), g },
        Kernel::Kara { l, g } => Kernel::Kara { l: l.min(kappa - 4), g },
        k => k,
    };
    for s in [6, 9] {
        out.time(&format!("f.level1.s{s}"), || lane_evals(&level1, true, kappa - 4, 1, &pts[..s], k1));
    }
    if kappa >= 12 {
        let level2 = random_words(2 << (kappa - 4), 98);
        let k2 = match k1 {
            Kernel::Neon { l, b } => Kernel::Neon { l: l.min(kappa - 8), b },
            Kernel::Inter { l, g } => Kernel::Inter { l: l.min(kappa - 8), g },
            Kernel::Kara { l, g } => Kernel::Kara { l: l.min(kappa - 8), g },
            k => k,
        };
        out.time("f.level2.s9", || lane_evals(&level2, true, kappa - 8, 1, &pts[..9], k2));
    }
    println!(
        "S\t{}\t{}\ta={a:.3}\tladder={:.3}\tnaive12={e_d12:.3}\tnaive_ladder={e_ladder:.3}",
        out.shape,
        threads,
        d_first + d_rest
    );
}
