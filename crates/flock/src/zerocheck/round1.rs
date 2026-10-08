// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! The zerocheck's round-1 message: the univariate skip.
//!
//! Each row of 64 witness bits is a polynomial's values on the skip domain `S`.
//! The message is that polynomial's eq-weighted sum, evaluated on the coset `Lambda`:
//!
//! ```text
//!     P_AB(l) = sum_x eq(r, x) * phi_8(a(l, x) * b(l, x))        l in Lambda, x a row
//!     P_C(l)  = sum_x eq(r, x) * phi_8(c(l, x))
//! ```
//!
//! Here `a(l, x)` is the extension of row `x` of `a`, a byte of GF(2^8), and `phi_8` embeds it into F192.
//!
//! The sweep groups the eq weights into three factors, by the protocol's choice of the first seven coordinates:
//!
//! 1. **Small eq**, the three innermost.
//!    The fixed challenges `phi_8([0xF7, 0x53, 0xB5])` make `eq_small[K] = C_s * x^K` in GF(2^8).
//!    A row's eight K-rows sum by powers of `x` in the byte field; the caller restores the constant `C_s`.
//! 2. **Medium eq**, the next four.
//!    The fixed challenges `gamma^(2^i) / (1 + gamma^(2^i))` make `eq_med[b] = gamma^b / D`.
//!    A window's sixteen medium bytes per lane convert to F192 by GF(2)-linear maps of the weights `gamma^b`.
//! 3. **Outer eq**, the sampled rest, with `1 / D` folded into its low half once.
//!
//! So the sweep's output is the naive message divided by `C_s`:
//!
//! ```text
//!     C_s * (ab[l] + c_lifted[l]) = naive_ab[l] + naive_c[l]
//! ```
//!
//! ## The product
//!
//! One medium position's `A B` bytes: its eight K-rows extended to `Lambda`, multiplied, and summed by powers of `x`.
//!
//! ```text
//!     out[l] = sum_K x^K * LDE(a_K)[l] * LDE(b_K)[l]        in GF(2^8), l in Lambda
//! ```
//!
//! - aarch64: the table lookups, products and shifts fused in NEON registers.
//! - AVX-512 with GFNI: one register per row, the products by `gf2p8mulb`.
//! - AVX2: two registers per row, the products by GFNI or by shifts and adds.
//! - Elsewhere: the scalar route, which is also every kernel's reference.
//!
//! ## The convert
//!
//! The convert: a window's medium bytes to F192, summed per lane under their medium and eq weights.
//!
//! ```text
//!     partial[lane] += eq_lo * sum_b gamma^b * phi_8(byte_b[lane])
//! ```
//!
//! The map from a lane's sixteen bytes to F192 is GF(2)-linear, so each target picks its fastest linear map:
//!
//! - AVX-512 with GFNI: one 8x8 bit matrix per (medium position, output byte), the eq weight baked in.
//! - AVX2: the same byte-sliced shape, 32 lanes wide, then one product per lane by the eq weight.
//! - Elsewhere: a 256-entry table per medium position, then one product per lane.

use std::sync::OnceLock;

#[cfg(target_arch = "aarch64")]
use core::arch::aarch64::*;
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
use core::arch::x86_64::*;

use primitives::bits::bit_transpose_64bytes;
#[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "gfni")))]
use primitives::field::gf2_8::avx2::gf8_mul_vec32;
use primitives::field::gf2_8::gf8_reduce;
#[cfg(target_arch = "aarch64")]
use primitives::field::gf2_8::neon::{gf8_mul_vec16, gf8_reduce_vec16};
use primitives::field::{F8, F192, phi8_192};
use primitives::multilinear::SplitEq;

use super::multilinear::PackedWitness;
use super::ntt::InvNttTableByteSingleGf8;
use super::{K_SKIP, N_INNER, Padding};

/// Evaluations per row: the size of the skip domain.
const ELL: usize = 1 << K_SKIP;

/// Bytes per K-row: 64 skip bits.
const N_CHUNKS: usize = ELL / 8;

/// Medium eq coordinates, so medium positions per window.
const N_MEDIUM: usize = 4;

/// Medium positions per window.
const N_MEDIUM_VALUES: usize = 1 << N_MEDIUM;

/// The bits of one window, the sweep's smallest cube: the skip, then the seven fixed coordinates.
const WINDOW_LOG: usize = K_SKIP + N_INNER;

/// Bytes of a medium position in a window: eight K-rows.
const MEDIUM_BYTES: usize = 8 * N_CHUNKS;

/// Most high variables of a split eq table capped on its high side: few high weights keep the outer products cheap.
pub(crate) const EQ_HIGH_VARS: usize = 7;

/// The three small challenges, as bytes, then embedded by `phi_8`.
///
/// These values make `eq_small[K] = C_s * x^K`.
///
/// With the four medium challenges they are the seven fixed zerocheck coordinates `a`.
/// Soundness requires their `2^7` eq weights `eq(a, b)` to be linearly independent over GF(2).
/// That is the hypothesis of `lem:fixed-zerocheck`.
/// That is strictly stronger than independence of the seven coordinates themselves.
///
/// - The zerocheck needs it, or a witness aligned with the fixed subspace could cancel the round-1 message.
/// - WHIR's level-0 list collapse needs it, for its bound on two candidates' extensions agreeing at `r`.
const SMALL_CHAL_F8: [u8; 3] = [0xF7, 0x53, 0xB5];

/// `C_s` as a byte, pinned by the cross-check against the naive message.
const C_S_F8: u8 = 0x1C;

/// `C_s = phi_8(0x1C)`: the naive message is the sweep's times this constant.
pub(crate) fn c_s() -> F192 {
    phi8_192(F8(C_S_F8))
}

/// The three small challenges in F192.
pub(crate) fn small_challenges() -> [F192; 3] {
    SMALL_CHAL_F8.map(|byte| phi8_192(F8(byte)))
}

/// The medium generator `gamma`, fixed by the protocol in the tower basis.
const fn medium_generator() -> F192 {
    F192::new(0x243f_6a88_85a3_08d3, 0x1319_8a2e_0370_7344, 0xa409_3822_299f_31d0)
}

/// `gamma, gamma^2, gamma^4, gamma^8`.
fn medium_squares() -> [F192; N_MEDIUM] {
    let mut g = [medium_generator(); N_MEDIUM];
    for i in 1..N_MEDIUM {
        g[i] = g[i - 1].square();
    }
    g
}

/// The four medium challenges `gamma^(2^i) / (1 + gamma^(2^i))`.
pub(crate) fn medium_challenges() -> [F192; N_MEDIUM] {
    medium_squares().map(|g| g * (F192::ONE + g).inv())
}

/// `1 / D`, `D = prod_i (1 + gamma^(2^i))`: it cancels the medium eq's normalization.
fn d_inv() -> F192 {
    static D_INV: OnceLock<F192> = OnceLock::new();
    *D_INV.get_or_init(|| {
        let d = medium_squares()
            .into_iter()
            .fold(F192::ONE, |acc, g| acc * (F192::ONE + g));
        d.inv()
    })
}

/// `gamma^b` for each medium position `b`.
fn gamma_powers() -> &'static [F192; N_MEDIUM_VALUES] {
    static POWERS: OnceLock<[F192; N_MEDIUM_VALUES]> = OnceLock::new();
    POWERS.get_or_init(|| {
        // Each power is the one before times the generator.
        let mut pow = [F192::ONE; N_MEDIUM_VALUES];
        for b in 1..N_MEDIUM_VALUES {
            pow[b] = pow[b - 1] * medium_generator();
        }
        pow
    })
}

/// Extend F192 values from `S` to `Lambda`, by the byte transform's butterflies lifted through `phi_8`.
pub(crate) fn extend(on_s: &[F192], table: &InvNttTableByteSingleGf8) -> Vec<F192> {
    let mut out = on_s.to_vec();
    table.extend_lifted(&mut out);
    out
}

/// Which medium positions of a window can hold a nonzero bit.
///
/// A window is `2^13` bits, sixteen medium positions of 512 bits.
/// A block of `2^k_log >= 2^13` bits spans whole windows, so its zero padding empties whole positions.
#[derive(Clone, Debug)]
struct MediumCounts {
    /// Masks a window index to its window within a block.
    mask: usize,
    /// For each window of a block, its medium positions before the padding.
    counts: Vec<u8>,
}

impl MediumCounts {
    fn new(padding: &Padding) -> Self {
        // A block below a window cannot skip at window granularity: every position counts.
        if padding.k_log < WINDOW_LOG {
            return Self {
                mask: 0,
                counts: vec![N_MEDIUM_VALUES as u8],
            };
        }
        let windows = 1usize << (padding.k_log - WINDOW_LOG);
        let counts = (0..windows)
            .map(|w| {
                let left = padding.useful_bits.saturating_sub(w << WINDOW_LOG);
                left.div_ceil(8 * MEDIUM_BYTES).min(N_MEDIUM_VALUES) as u8
            })
            .collect();
        Self {
            mask: windows - 1,
            counts,
        }
    }

    /// The live medium positions of window `x_outer`.
    fn of(&self, x_outer: usize) -> usize {
        usize::from(self.counts[x_outer & self.mask])
    }
}

/// One worker's scratch and running sums.
struct WorkerState {
    /// The current high index's per-lane sums.
    convert: Convert,
    /// One window's `A B` bytes, a row per medium position.
    ab_rows: [[u8; ELL]; N_MEDIUM_VALUES],
    /// One window's transposed `C` bytes, a row per medium position.
    c_rows: [[u8; ELL]; N_MEDIUM_VALUES],
    /// The worker's sums over its high indices, `A B` then `C`.
    sums: [[F192; ELL]; 2],
}

impl WorkerState {
    const fn new() -> Self {
        Self {
            convert: Convert::new(),
            ab_rows: [[0; ELL]; N_MEDIUM_VALUES],
            c_rows: [[0; ELL]; N_MEDIUM_VALUES],
            sums: [[F192::ZERO; ELL]; 2],
        }
    }

    /// Two workers' sums added.
    fn merge(mut self, other: &Self) -> Self {
        for (x, y) in self.sums.iter_mut().flatten().zip(other.sums.iter().flatten()) {
            *x += *y;
        }
        self
    }
}

/// One circuit's round-1 message, padding-aware.
pub(crate) struct Round1<'a> {
    /// The circuit's packed `a` and `b`; `c = a AND b` is derived.
    bits: PackedWitness<'a>,
    /// The base-two logarithm of the cube's bits.
    m: usize,
    /// The eq coordinates past the skip: the seven fixed ones, then the outer ones.
    r: &'a [F192],
    /// The byte extension from `S` to `Lambda`.
    lde: &'a InvNttTableByteSingleGf8,
    /// Where the witness is zero or repeats itself.
    padding: Padding,
}

impl<'a> Round1<'a> {
    /// The message of a cube of `2^m` bits at the eq coordinates `r`.
    ///
    /// # Panics
    ///
    /// When the cube is below a window, or the lengths disagree with `m`.
    pub(crate) fn new(
        bits: PackedWitness<'a>,
        m: usize,
        r: &'a [F192],
        lde: &'a InvNttTableByteSingleGf8,
        padding: &Padding,
    ) -> Self {
        // A window is the sweep's unit: the skip and the seven fixed coordinates.
        assert!(m >= WINDOW_LOG, "the sweep needs at least one {WINDOW_LOG}-bit window");
        assert_eq!(bits.a.len(), (1 << m) / 8);
        assert_eq!(bits.b.len(), (1 << m) / 8);
        assert_eq!(r.len(), m - K_SKIP);
        assert_eq!(lde.k, K_SKIP);
        Self {
            bits,
            m,
            r,
            lde,
            padding: *padding,
        }
    }

    /// The `A B` and `C` halves on `Lambda`, both short of the factor `C_s`.
    ///
    /// Medium positions wholly in every block's zero padding are skipped: they would add literal zeros.
    /// The identical tail of blocks is summed once, its last group weighted by the tail's eq mass.
    pub(crate) fn message(&self) -> (Vec<F192>, Vec<F192>) {
        // Phase 1: the windows before the tail, and the outer eq split into a low and a high half.
        let tail = self.padding.tail(self.m, WINDOW_LOG, WINDOW_LOG, self.r);
        let n_windows = tail.map_or(1 << (self.m - WINDOW_LOG), |t| t.head >> WINDOW_LOG);
        let eq = SplitEq::with_high_vars(&self.r[N_INNER..], EQ_HIGH_VARS);
        let d_inv = d_inv();
        let sweep = Sweep {
            bits: self.bits,
            lde: self.lde,
            // `1 / D` rides the low half once, cancelling the medium eq's normalization.
            eq_lo: eq.low.iter().map(|&e| e * d_inv).collect(),
            n_lo: eq.low_log(),
            n_windows,
            medium: MediumCounts::new(&self.padding),
        };

        // Phase 2: one task per high eq index, each worker summing into its own state.
        let sums = parallel::fold_reduce(
            n_windows.div_ceil(sweep.eq_lo.len()),
            WorkerState::new,
            |state, x_hi| sweep.high(state, x_hi, eq.high[x_hi]),
            |a, b| a.merge(&b),
        )
        .sums;

        // Phase 3: `C` was summed on `S`, being linear: extend it to `Lambda` once.
        let mut ab = sums[0].to_vec();
        let mut c = extend(&sums[1], self.lde);

        // Phase 4: the tail's last group, once, at the tail's eq mass.
        if let Some(tail) = tail {
            let group = PackedWitness {
                a: tail.group(self.bits.a),
                b: tail.group(self.bits.b),
            };
            let r = &self.r[..tail.r_inner];
            let (group_ab, group_c) =
                Round1::new(group, tail.group_log, r, self.lde, &self.padding.without_tail()).message();
            for (x, y) in ab.iter_mut().zip(group_ab) {
                *x += tail.weight * y;
            }
            for (x, y) in c.iter_mut().zip(group_c) {
                *x += tail.weight * y;
            }
        }
        (ab, c)
    }
}

/// What every task of one sweep shares.
struct Sweep<'a> {
    /// The packed `a` and `b`.
    bits: PackedWitness<'a>,
    /// The byte extension from `S` to `Lambda`.
    lde: &'a InvNttTableByteSingleGf8,
    /// The low half of the outer eq table, times `1 / D`.
    eq_lo: Vec<F192>,
    /// The low half's variables.
    n_lo: usize,
    /// The windows before the tail.
    n_windows: usize,
    /// The live medium positions of each window.
    medium: MediumCounts,
}

impl Sweep<'_> {
    /// Add every window under high eq index `x_hi`, at weight `eq_hi`.
    fn high(&self, state: &mut WorkerState, x_hi: usize, eq_hi: F192) {
        state.convert = Convert::new();
        let first = x_hi << self.n_lo;
        let n = self.eq_lo.len().min(self.n_windows - first);
        for (x_lo, &eq_lo) in self.eq_lo[..n].iter().enumerate() {
            let x_outer = first | x_lo;
            // A full window has a constant trip count, which the unroll depends on.
            match self.medium.of(x_outer) {
                0 => {}
                N_MEDIUM_VALUES => self.window::<true>(state, x_outer, N_MEDIUM_VALUES, eq_lo),
                live => self.window::<false>(state, x_outer, live, eq_lo),
            }
        }

        // The outer fold by the high weight.
        let (ab, c) = state.convert.values();
        for (sum, values) in state.sums.iter_mut().zip([ab, c]) {
            for (s, v) in sum.iter_mut().zip(values) {
                *s += eq_hi * v;
            }
        }
    }

    /// Add window `x_outer`'s first `live` medium positions at weight `eq_lo`.
    ///
    /// ```text
    ///     window bytes   [ medium 0 | medium 1 | ... | medium 15 ]      64 bytes each: eight K-rows of eight
    /// ```
    #[inline(always)]
    fn window<const FULL: bool>(&self, state: &mut WorkerState, x_outer: usize, live: usize, eq_lo: F192) {
        let live = if FULL { N_MEDIUM_VALUES } else { live };
        let base = x_outer << (WINDOW_LOG - 3);
        for b_med in 0..live {
            let at = base + b_med * MEDIUM_BYTES;
            let [a, b]: [&[u8; MEDIUM_BYTES]; 2] =
                [self.bits.a, self.bits.b].map(|p| p[at..at + MEDIUM_BYTES].try_into().expect("a medium position"));
            // `A B`: extended, multiplied, and summed over the K-rows in the byte field.
            state.ab_rows[b_med] = product_bytes(a, b, self.lde);
            // `C = a AND b`, linear: transposed so lane `s` holds skip position `s` of each K-row, extended later.
            let c: [u8; MEDIUM_BYTES] = std::array::from_fn(|i| a[i] & b[i]);
            bit_transpose_64bytes(&c, &mut state.c_rows[b_med]);
        }
        state
            .convert
            .accumulate(&state.ab_rows[..live], &state.c_rows[..live], eq_lo);
    }
}

/// The `A B` bytes of one medium position, `a` and `b` its eight K-rows of eight bytes each.
#[inline]
fn product_bytes(a: &[u8; MEDIUM_BYTES], b: &[u8; MEDIUM_BYTES], table: &InvNttTableByteSingleGf8) -> [u8; ELL] {
    let mut out = [0; ELL];
    shift_reduce_inner_ab(a, b, table, &mut out);
    out
}

// For one medium position and its eight K-rows K in 0..8:
//   1. Look up the extended A, B rows at bytes `8K .. 8K + 8`.
//   2. y_K[lane] = ntt_a[lane] · ntt_b[lane]  (in F_8).
//   3. acc[lane] ^= (y_K[lane] as u16) << K   (no reduction yet).
// At the end, reduce each acc[lane] back to a u8 in F_8.
//
// Output `out[lane]` is the F_8 representative of Σ_K x^K · y_K[lane] mod p.

// Fused NEON inner kernel: inv_NTT apply + F_8 mul + shift_reduce, all in
// NEON registers (no Vec<F8> round-trip).
//
// `xor_apply_byte_into_8_regs::<BH, ODD>` handles one byte position (b ≥ 1).
// `BH` (= b >> 1) selects which chunk-index XOR to apply; `ODD` (= b & 1)
// switches on the within-chunk half-swap. Both const-generic so the compiler
// dead-code-eliminates the if-branch and folds the chunk-index XORs.
//
// `fused_apply_one_k::<K>` runs one full K-row: the initial b=0 plain load,
// 7 calls to the byte helper for b=1..7 (with the specific protocol BH/ODD
// pattern), one 16-lane F_8 mul per output chunk, and finally widen-shift-XOR
// into the per-(K, lane) 16-bit accumulators.

/// # Safety
/// `table_base` points to a `256 * 64`-byte table, and `BH < 4`.
#[cfg(target_arch = "aarch64")]
// `0 ^ BH` is the i = 0 case of the `i ^ BH` row-select pattern below; spelling
// it out keeps the four loads visibly parallel.
#[allow(clippy::identity_op)]
#[inline(always)]
#[expect(
    clippy::too_many_arguments,
    reason = "Separate NEON accumulators preserve the register layout of the fused kernel."
)]
unsafe fn xor_apply_byte_into_8_regs<const BH: usize>(
    table_base: *const u8,
    a_byte: u8,
    b_byte: u8,
    da0: &mut core::arch::aarch64::uint8x16_t,
    da1: &mut core::arch::aarch64::uint8x16_t,
    da2: &mut core::arch::aarch64::uint8x16_t,
    da3: &mut core::arch::aarch64::uint8x16_t,
    db0: &mut core::arch::aarch64::uint8x16_t,
    db1: &mut core::arch::aarch64::uint8x16_t,
    db2: &mut core::arch::aarch64::uint8x16_t,
    db3: &mut core::arch::aarch64::uint8x16_t,
) {
    // SAFETY: NEON is part of the aarch64 baseline; `table_base` is the caller's `256 * 64`-byte table, so row
    // `byte * 64` plus a chunk offset `(i ^ BH) * 16 < 64` (`BH < 4`) stays inside it.
    unsafe {
        let ra = table_base.add(a_byte as usize * 64);
        let rb = table_base.add(b_byte as usize * 64);
        let va0 = vld1q_u8(ra.add((0 ^ BH) * 16));
        let va1 = vld1q_u8(ra.add((1 ^ BH) * 16));
        let va2 = vld1q_u8(ra.add((2 ^ BH) * 16));
        let va3 = vld1q_u8(ra.add((3 ^ BH) * 16));
        let vb0 = vld1q_u8(rb.add((0 ^ BH) * 16));
        let vb1 = vld1q_u8(rb.add((1 ^ BH) * 16));
        let vb2 = vld1q_u8(rb.add((2 ^ BH) * 16));
        let vb3 = vld1q_u8(rb.add((3 ^ BH) * 16));
        *da0 = veorq_u8(*da0, va0);
        *da1 = veorq_u8(*da1, va1);
        *da2 = veorq_u8(*da2, va2);
        *da3 = veorq_u8(*da3, va3);
        *db0 = veorq_u8(*db0, vb0);
        *db1 = veorq_u8(*db1, vb1);
        *db2 = veorq_u8(*db2, vb2);
        *db3 = veorq_u8(*db3, vb3);
    }
}

/// Process one K-row: 8 byte positions of `a` and `b` via the inv_NTT table,
/// F_8 multiply, widen-shift by K, XOR into the four `(acc_lo, acc_hi)` pairs.
///
/// # Safety
/// `table_base` points to a `256 * 64`-byte table, and `a_row` and `b_row` to `N_CHUNKS` readable bytes each.
#[cfg(target_arch = "aarch64")]
#[inline(always)]
#[expect(
    clippy::too_many_arguments,
    reason = "Separate NEON accumulators preserve the register layout of the fused kernel."
)]
unsafe fn fused_apply_one_k<const K: i32>(
    table_base: *const u8,
    a_row: *const u8,
    b_row: *const u8,
    acc0_lo: &mut core::arch::aarch64::uint16x8_t,
    acc0_hi: &mut core::arch::aarch64::uint16x8_t,
    acc1_lo: &mut core::arch::aarch64::uint16x8_t,
    acc1_hi: &mut core::arch::aarch64::uint16x8_t,
    acc2_lo: &mut core::arch::aarch64::uint16x8_t,
    acc2_hi: &mut core::arch::aarch64::uint16x8_t,
    acc3_lo: &mut core::arch::aarch64::uint16x8_t,
    acc3_hi: &mut core::arch::aarch64::uint16x8_t,
) {
    // SAFETY: NEON is part of the aarch64 baseline; the caller guarantees `N_CHUNKS` readable bytes at `a_row` and
    // `b_row` and a `256 * 64`-byte table, and every load is a table row plus an offset below 64.
    unsafe {
        // `π_b(i') = i' ⊕ 8b` is a chunk-index XOR by `b >> 1`, which is a free
        // load offset, and for odd `b` a swap of each chunk's two 8-byte halves.
        // That swap is an involution and distributes over XOR, and it commutes
        // with the chunk reindexing, so the eight positions need one swap of the
        // accumulators between the odd group and the even group rather than one
        // per register per odd position: `E ⊕ S(O)` with the odds accumulated
        // plainly first. Four times fewer `ext`, and `ext` was the largest
        // single share of this body's vector work.
        let ra1 = table_base.add(*a_row.add(1) as usize * 64);
        let rb1 = table_base.add(*b_row.add(1) as usize * 64);
        let mut da0 = vld1q_u8(ra1);
        let mut da1 = vld1q_u8(ra1.add(16));
        let mut da2 = vld1q_u8(ra1.add(32));
        let mut da3 = vld1q_u8(ra1.add(48));
        let mut db0 = vld1q_u8(rb1);
        let mut db1 = vld1q_u8(rb1.add(16));
        let mut db2 = vld1q_u8(rb1.add(32));
        let mut db3 = vld1q_u8(rb1.add(48));

        // The rest of the odd positions, b = 3, 5, 7.
        macro_rules! apply {
            ($bh:literal, $b:literal) => {
                xor_apply_byte_into_8_regs::<$bh>(
                    table_base,
                    *a_row.add($b),
                    *b_row.add($b),
                    &mut da0,
                    &mut da1,
                    &mut da2,
                    &mut da3,
                    &mut db0,
                    &mut db1,
                    &mut db2,
                    &mut db3,
                )
            };
        }
        apply!(1, 3);
        apply!(2, 5);
        apply!(3, 7);

        // One swap for the whole odd group.
        da0 = vextq_u8::<8>(da0, da0);
        da1 = vextq_u8::<8>(da1, da1);
        da2 = vextq_u8::<8>(da2, da2);
        da3 = vextq_u8::<8>(da3, da3);
        db0 = vextq_u8::<8>(db0, db0);
        db1 = vextq_u8::<8>(db1, db1);
        db2 = vextq_u8::<8>(db2, db2);
        db3 = vextq_u8::<8>(db3, db3);

        // The even positions, b = 0, 2, 4, 6, which need no swap.
        apply!(0, 0);
        apply!(1, 2);
        apply!(2, 4);
        apply!(3, 6);

        // F_8 multiply lane-wise (4 × 16 lanes = 64 total).
        let y0 = gf8_mul_vec16(da0, db0);
        let y1 = gf8_mul_vec16(da1, db1);
        let y2 = gf8_mul_vec16(da2, db2);
        let y3 = gf8_mul_vec16(da3, db3);

        // Widen-shift by K, XOR into the 16-bit accumulators.
        *acc0_lo = veorq_u16(*acc0_lo, vshll_n_u8::<K>(vget_low_u8(y0)));
        *acc0_hi = veorq_u16(*acc0_hi, vshll_n_u8::<K>(vget_high_u8(y0)));
        *acc1_lo = veorq_u16(*acc1_lo, vshll_n_u8::<K>(vget_low_u8(y1)));
        *acc1_hi = veorq_u16(*acc1_hi, vshll_n_u8::<K>(vget_high_u8(y1)));
        *acc2_lo = veorq_u16(*acc2_lo, vshll_n_u8::<K>(vget_low_u8(y2)));
        *acc2_hi = veorq_u16(*acc2_hi, vshll_n_u8::<K>(vget_high_u8(y2)));
        *acc3_lo = veorq_u16(*acc3_lo, vshll_n_u8::<K>(vget_low_u8(y3)));
        *acc3_hi = veorq_u16(*acc3_hi, vshll_n_u8::<K>(vget_high_u8(y3)));
    }
}

#[cfg(target_arch = "aarch64")]
#[inline(always)]
fn shift_reduce_inner_ab_fused_neon(
    a_packed: &[u8; MEDIUM_BYTES],
    b_packed: &[u8; MEDIUM_BYTES],
    inv_table: &InvNttTableByteSingleGf8,
    out: &mut [u8; 64],
) {
    let byte_base_b = 0;
    let table_base = inv_table.data_ptr();

    // SAFETY: NEON is part of the aarch64 baseline. The table is `256 * 64` bytes, its `k` being `K_SKIP` (asserted
    // at the entry point). The row windows `byte_base_b + K * N_CHUNKS .. + N_CHUNKS` for `K < 8` lie in both packed
    // tables, whose lengths the entry point asserts against the windows it walks. `out` is 64 bytes.
    unsafe {
        let mut acc0_lo = vdupq_n_u16(0);
        let mut acc0_hi = vdupq_n_u16(0);
        let mut acc1_lo = vdupq_n_u16(0);
        let mut acc1_hi = vdupq_n_u16(0);
        let mut acc2_lo = vdupq_n_u16(0);
        let mut acc2_hi = vdupq_n_u16(0);
        let mut acc3_lo = vdupq_n_u16(0);
        let mut acc3_hi = vdupq_n_u16(0);

        // 8 K-iterations: each consumes N_CHUNKS = 8 packed witness bytes
        // for `a` and `b`. K is a const generic so `vshll_n_u8::<K>` specializes.
        macro_rules! do_k {
            ($k:literal) => {{
                let off = byte_base_b + $k * N_CHUNKS;
                fused_apply_one_k::<$k>(
                    table_base,
                    a_packed.as_ptr().add(off),
                    b_packed.as_ptr().add(off),
                    &mut acc0_lo,
                    &mut acc0_hi,
                    &mut acc1_lo,
                    &mut acc1_hi,
                    &mut acc2_lo,
                    &mut acc2_hi,
                    &mut acc3_lo,
                    &mut acc3_hi,
                );
            }};
        }
        do_k!(0);
        do_k!(1);
        do_k!(2);
        do_k!(3);
        do_k!(4);
        do_k!(5);
        do_k!(6);
        do_k!(7);

        // Reduce 16-bit accs → 16-byte F_8 results (4 × 16 lanes).
        let r0 = gf8_reduce_vec16(vreinterpretq_u8_u16(acc0_lo), vreinterpretq_u8_u16(acc0_hi));
        let r1 = gf8_reduce_vec16(vreinterpretq_u8_u16(acc1_lo), vreinterpretq_u8_u16(acc1_hi));
        let r2 = gf8_reduce_vec16(vreinterpretq_u8_u16(acc2_lo), vreinterpretq_u8_u16(acc2_hi));
        let r3 = gf8_reduce_vec16(vreinterpretq_u8_u16(acc3_lo), vreinterpretq_u8_u16(acc3_hi));

        let p = out.as_mut_ptr();
        vst1q_u8(p, r0);
        vst1q_u8(p.add(16), r1);
        vst1q_u8(p.add(32), r2);
        vst1q_u8(p.add(48), r3);
    }
}

/// Dispatch helper: picks the widest SIMD kernel this target has, otherwise scalar.
#[inline]
fn shift_reduce_inner_ab(
    a_packed: &[u8; MEDIUM_BYTES],
    b_packed: &[u8; MEDIUM_BYTES],
    inv_table: &InvNttTableByteSingleGf8,
    out: &mut [u8; 64],
) {
    #[cfg(target_arch = "aarch64")]
    {
        shift_reduce_inner_ab_fused_neon(a_packed, b_packed, inv_table, out);
    }
    #[cfg(all(target_arch = "x86_64", target_feature = "gfni", target_feature = "avx512bw"))]
    {
        // SAFETY: gfni and avx512bw are statically enabled at compile time.
        unsafe { shift_reduce_inner_ab_gfni_512(a_packed, b_packed, inv_table, out) };
    }
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx2",
        not(all(target_feature = "gfni", target_feature = "avx512bw"))
    ))]
    {
        // SAFETY: avx2, and gfni where the kernel uses it, are statically enabled at compile time.
        unsafe { shift_reduce_inner_ab_avx2(a_packed, b_packed, inv_table, out) };
    }
    #[cfg(not(any(target_arch = "aarch64", all(target_arch = "x86_64", target_feature = "avx2"))))]
    {
        shift_reduce_inner_ab_scalar(a_packed, b_packed, inv_table, out);
    }
}

/// The GFNI kernel one register wide: `ELL` is 64, so the whole column is one
/// ZMM and the combine issues a quarter of the instructions the 128-bit arm
/// does. Byte unpacking and `packus` both work within 128-bit lanes and are
/// exact inverses there, so the widened accumulators may sit in a different
/// order than the narrow arm's and still narrow back to the same bytes.
///
/// # Safety
/// Requires the `gfni` and `avx512bw` target features.
#[cfg(all(target_arch = "x86_64", target_feature = "gfni", target_feature = "avx512bw"))]
#[target_feature(enable = "gfni", enable = "avx512f", enable = "avx512bw")]
unsafe fn shift_reduce_inner_ab_gfni_512(
    a_packed: &[u8; MEDIUM_BYTES],
    b_packed: &[u8; MEDIUM_BYTES],
    inv_table: &InvNttTableByteSingleGf8,
    out: &mut [u8; 64],
) {
    let byte_base_b = 0;
    let chunk = |k: usize| byte_base_b + k * N_CHUNKS..byte_base_b + (k + 1) * N_CHUNKS;

    // SAFETY: the target features are carried by the function; the store covers exactly `out`.
    unsafe {
        let (mut acc_lo, mut acc_hi) = (_mm512_setzero_si512(), _mm512_setzero_si512());
        let zero = _mm512_setzero_si512();

        for k in 0..8 {
            let y = _mm512_gf2p8mul_epi8(
                inv_table.apply_zmm(a_packed[chunk(k)].try_into().expect("one chunk")),
                inv_table.apply_zmm(b_packed[chunk(k)].try_into().expect("one chunk")),
            );
            let shift = _mm_cvtsi32_si128(k as i32);
            acc_lo = _mm512_xor_si512(acc_lo, _mm512_sll_epi16(_mm512_unpacklo_epi8(y, zero), shift));
            acc_hi = _mm512_xor_si512(acc_hi, _mm512_sll_epi16(_mm512_unpackhi_epi8(y, zero), shift));
        }

        // Vectorized gf8_reduce over u16 lanes: two-step fold of the high byte
        // h with h ^ (h<<1) ^ (h<<3) ^ (h<<4)  (x^8 = x^4+x^3+x+1).
        let mask_ff = _mm512_set1_epi16(0xff);
        let fold = |p: __m512i| -> __m512i {
            let h = _mm512_srli_epi16::<8>(p);
            _mm512_xor_si512(
                _mm512_and_si512(p, mask_ff),
                _mm512_xor_si512(
                    _mm512_xor_si512(h, _mm512_slli_epi16::<1>(h)),
                    _mm512_xor_si512(_mm512_slli_epi16::<3>(h), _mm512_slli_epi16::<4>(h)),
                ),
            )
        };
        // Two folds bring 15-bit accumulators down to 8 bits; the second fold's
        // high byte is at most 0x0f, so lanes stay below 256 for `packus`.
        let reduce = |p: __m512i| _mm512_and_si512(fold(fold(p)), mask_ff);
        _mm512_storeu_si512(
            out.as_mut_ptr().cast(),
            _mm512_packus_epi16(reduce(acc_lo), reduce(acc_hi)),
        );
    }
}

/// The 512-bit kernel two registers wide. With GFNI the products are
/// `gf2p8mulb`; without it, the shift-and-add of `gf2_8::avx2::gf8_mul_vec32`.
///
/// # Safety
/// Requires the `avx2` target feature, and `gfni` where the target has it.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[cfg_attr(all(target_feature = "gfni", target_feature = "avx512bw"), allow(dead_code))]
#[target_feature(enable = "avx2")]
unsafe fn shift_reduce_inner_ab_avx2(
    a_packed: &[u8; MEDIUM_BYTES],
    b_packed: &[u8; MEDIUM_BYTES],
    inv_table: &InvNttTableByteSingleGf8,
    out: &mut [u8; 64],
) {
    let byte_base_b = 0;
    // `inv_table.apply` overwrites every lane, so these need no re-zeroing per K.
    let mut a_col = [F8::ZERO; ELL];
    let mut b_col = [F8::ZERO; ELL];

    // SAFETY: the target features are carried by the function or enabled at
    // compile time; the loads and stores stay within a_col/b_col/out, each
    // exactly `ELL` bytes.
    unsafe {
        let mut acc = [[_mm256_setzero_si256(); 2]; 2];
        let zero = _mm256_setzero_si256();

        for k in 0..8 {
            let chunk_off = byte_base_b + k * N_CHUNKS;
            inv_table.apply(&a_packed[chunk_off..chunk_off + N_CHUNKS], &mut a_col);
            inv_table.apply(&b_packed[chunk_off..chunk_off + N_CHUNKS], &mut b_col);
            let shift = _mm_cvtsi32_si128(k as i32);
            for (h, [lo, hi]) in acc.iter_mut().enumerate() {
                let a = _mm256_loadu_si256(a_col.as_ptr().add(32 * h).cast());
                let b = _mm256_loadu_si256(b_col.as_ptr().add(32 * h).cast());
                #[cfg(target_feature = "gfni")]
                let y = _mm256_gf2p8mul_epi8(a, b);
                #[cfg(not(target_feature = "gfni"))]
                let y = gf8_mul_vec32(a, b);
                *lo = _mm256_xor_si256(*lo, _mm256_sll_epi16(_mm256_unpacklo_epi8(y, zero), shift));
                *hi = _mm256_xor_si256(*hi, _mm256_sll_epi16(_mm256_unpackhi_epi8(y, zero), shift));
            }
        }

        // Vectorized gf8_reduce over u16 lanes: two-step fold of the high byte
        // h with h ^ (h<<1) ^ (h<<3) ^ (h<<4)  (x^8 = x^4+x^3+x+1).
        let mask_ff = _mm256_set1_epi16(0xff);
        let fold = |p: __m256i| -> __m256i {
            let h = _mm256_srli_epi16::<8>(p);
            _mm256_xor_si256(
                _mm256_and_si256(p, mask_ff),
                _mm256_xor_si256(
                    _mm256_xor_si256(h, _mm256_slli_epi16::<1>(h)),
                    _mm256_xor_si256(_mm256_slli_epi16::<3>(h), _mm256_slli_epi16::<4>(h)),
                ),
            )
        };
        // Two folds bring 15-bit accumulators down to 8 bits; the second fold's
        // high byte is at most 0x0f, so lanes stay below 256 for `packus`.
        let reduce = |p: __m256i| _mm256_and_si256(fold(fold(p)), mask_ff);
        for (h, [lo, hi]) in acc.into_iter().enumerate() {
            _mm256_storeu_si256(
                out.as_mut_ptr().add(32 * h).cast(),
                _mm256_packus_epi16(reduce(lo), reduce(hi)),
            );
        }
    }
}

/// The scalar route: the fallback without NEON or AVX2, and every kernel's reference.
#[cfg_attr(
    any(target_arch = "aarch64", all(target_arch = "x86_64", target_feature = "avx2")),
    allow(dead_code)
)]
fn shift_reduce_inner_ab_scalar(
    a_packed: &[u8; MEDIUM_BYTES],
    b_packed: &[u8; MEDIUM_BYTES],
    inv_table: &InvNttTableByteSingleGf8,
    out: &mut [u8; 64],
) {
    // `inv_table.apply` overwrites every lane, so these need no re-zeroing per K.
    let mut a_col = [F8::ZERO; ELL];
    let mut b_col = [F8::ZERO; ELL];
    let mut acc: [u16; 64] = [0u16; 64];
    let byte_base_b = 0;
    for k in 0..8 {
        let chunk_off = byte_base_b + k * N_CHUNKS;
        inv_table.apply(&a_packed[chunk_off..chunk_off + N_CHUNKS], &mut a_col);
        inv_table.apply(&b_packed[chunk_off..chunk_off + N_CHUNKS], &mut b_col);
        for lane in 0..ELL {
            let y = (a_col[lane] * b_col[lane]).0 as u16;
            acc[lane] ^= y << k;
        }
    }
    for lane in 0..ELL {
        out[lane] = gf8_reduce(acc[lane]);
    }
}

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
))]
use gfni::Convert;

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx2",
    not(all(target_feature = "gfni", target_feature = "avx512bw", target_feature = "avx512vbmi"))
))]
use avx2::Convert;

#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
use table::Convert;

/// 256-entry tables, one per medium position.
#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
mod table {
    use std::sync::OnceLock;

    use primitives::field::{F192, PHI_8_TABLE_192};

    use super::{ELL, N_MEDIUM_VALUES, gamma_powers};

    /// `gamma^b * phi_8(v)` for every medium position `b` and byte `v`.
    ///
    /// Its shape, not a flat run, lets a byte index a row with no bounds check.
    /// The row stride then folds into the address.
    type Table = [[F192; 256]; N_MEDIUM_VALUES];

    /// The table, built once.
    fn table() -> &'static Table {
        static TABLE: OnceLock<Box<Table>> = OnceLock::new();
        TABLE.get_or_init(|| {
            // Row `b` is `phi_8` of every byte, scaled by `gamma^b`.
            let mut table: Box<Table> = Box::new([[F192::ZERO; 256]; N_MEDIUM_VALUES]);
            for (row, &g_b) in table.iter_mut().zip(gamma_powers()) {
                for (entry, &phi) in row.iter_mut().zip(PHI_8_TABLE_192.iter()) {
                    *entry = g_b * phi;
                }
            }
            table
        })
    }

    /// One worker's per-lane sums for `A B` and for `C`.
    pub(super) struct Convert {
        ab: [F192; ELL],
        c: [F192; ELL],
    }

    impl Convert {
        pub(super) const fn new() -> Self {
            Self {
                ab: [F192::ZERO; ELL],
                c: [F192::ZERO; ELL],
            }
        }

        /// Add one window's medium bytes, a 64-lane row per medium position, at weight `eq_lo`.
        #[inline(always)]
        pub(super) fn accumulate(&mut self, ab: &[[u8; 64]], c: &[[u8; 64]], eq_lo: F192) {
            let table = table();
            #[cfg(target_arch = "aarch64")]
            {
                // A bounded group of four medium positions at a time keeps their table rows hot.
                let mut converted_ab = [F192::ZERO; ELL];
                let mut converted_c = [F192::ZERO; ELL];
                for ((rows, ab), c) in table.chunks(4).zip(ab.chunks(4)).zip(c.chunks(4)) {
                    for lane in 0..ELL {
                        let mut cf_ab = F192::ZERO;
                        let mut cf_c = F192::ZERO;
                        for ((row, ab), c) in rows.iter().zip(ab).zip(c) {
                            cf_ab += row[usize::from(ab[lane])];
                            cf_c += row[usize::from(c[lane])];
                        }
                        converted_ab[lane] += cf_ab;
                        converted_c[lane] += cf_c;
                    }
                }
                // The eq weight, once per lane after the whole window.
                for lane in 0..ELL {
                    self.ab[lane] += converted_ab[lane] * eq_lo;
                    self.c[lane] += converted_c[lane] * eq_lo;
                }
            }
            #[cfg(not(target_arch = "aarch64"))]
            for lane in 0..ELL {
                let mut cf_ab = F192::ZERO;
                let mut cf_c = F192::ZERO;
                for ((row, ab), c) in table.iter().zip(ab).zip(c) {
                    cf_ab += row[usize::from(ab[lane])];
                    cf_c += row[usize::from(c[lane])];
                }
                self.ab[lane] += cf_ab * eq_lo;
                self.c[lane] += cf_c * eq_lo;
            }
        }

        /// The `A B` and `C` sums.
        pub(super) const fn values(&self) -> ([F192; ELL], [F192; ELL]) {
            (self.ab, self.c)
        }
    }
}

/// AVX2: byte-sliced against fixed maps, 32 lanes a register, then one product per lane by the eq weight.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[cfg_attr(
    all(target_feature = "gfni", target_feature = "avx512bw", target_feature = "avx512vbmi"),
    allow(dead_code)
)]
mod avx2 {
    use core::arch::x86_64::*;
    use std::sync::LazyLock;

    use primitives::bit_fold::avx2::{self, Best, HALF, OUT_BYTES, Product};
    use primitives::field::{F192, PHI_8_TABLE_192, mul4};

    use super::{ELL, N_MEDIUM_VALUES, gamma_powers};

    /// The maps of each medium position `b`: the weights `gamma^b * phi_8(2^s)`.
    pub(super) type Maps<P> = [[<P as Product>::Map; OUT_BYTES]; N_MEDIUM_VALUES];

    /// The maps of the product `P`.
    pub(super) fn maps<P: Product>() -> Maps<P> {
        let units: [F192; 8] = std::array::from_fn(|s| PHI_8_TABLE_192[1 << s]);
        gamma_powers().map(|g| P::maps(&units.map(|u| g * u)))
    }

    /// `sum_b gamma^b * phi_8(rows[b][lane])` for every lane, byte-sliced.
    #[target_feature(enable = "avx2")]
    pub(super) fn convert<P: Product>(rows: &[[u8; 64]], maps: &Maps<P>) -> [F192; ELL] {
        let mut out = [F192::ZERO; ELL];
        for (h, out) in out.as_chunks_mut::<HALF>().0.iter_mut().enumerate() {
            let mut acc = [_mm256_setzero_si256(); OUT_BYTES];
            // Eight output bytes at a time keep their accumulators in registers.
            for (o, acc) in acc.as_chunks_mut::<8>().0.iter_mut().enumerate() {
                for (row, m) in rows.iter().zip(maps) {
                    // SAFETY: each half-row is 32 bytes.
                    let x = unsafe { _mm256_loadu_si256(row[HALF * h..].as_ptr().cast()) };
                    avx2::accumulate8::<P>(acc, P::input(x), &m[8 * o..]);
                }
            }
            avx2::store_f192(&acc, out);
        }
        out
    }

    /// One worker's per-lane sums for `A B` and for `C`.
    pub(super) struct Convert {
        ab: [F192; ELL],
        c: [F192; ELL],
    }

    impl Convert {
        pub(super) const fn new() -> Self {
            Self {
                ab: [F192::ZERO; ELL],
                c: [F192::ZERO; ELL],
            }
        }

        /// Add one window's medium bytes, a 64-lane row per medium position, at weight `eq_lo`.
        #[inline(always)]
        pub(super) fn accumulate(&mut self, ab: &[[u8; 64]], c: &[[u8; 64]], eq_lo: F192) {
            static MAPS: LazyLock<Maps<Best>> = LazyLock::new(maps::<Best>);
            for (acc, rows) in [(&mut self.ab, ab), (&mut self.c, c)] {
                // SAFETY: the module is compiled only with AVX2 enabled.
                let cf = unsafe { convert::<Best>(rows, &MAPS) };
                for (acc, cf) in acc.as_chunks_mut::<4>().0.iter_mut().zip(cf.as_chunks::<4>().0) {
                    for (acc, p) in acc.iter_mut().zip(mul4(*cf, [eq_lo; 4])) {
                        *acc += p;
                    }
                }
            }
        }

        /// The `A B` and `C` sums.
        pub(super) const fn values(&self) -> ([F192; ELL], [F192; ELL]) {
            (self.ab, self.c)
        }
    }
}

/// AVX-512 with GFNI: byte-sliced sums, register `o` holding byte `o` of every lane's sum.
///
/// The weight `eq_lo` rides the GFNI matrices, rebuilt for each window:
///
/// ```text
///     w[b][s] = (gamma^b * eq_lo) * phi_8(2^s)        phi_8(2^s) lies in the GF(2^64) base field
/// ```
///
/// So a window costs 16 products and 16 mixed products, not a product per lane.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
))]
mod gfni {
    use core::arch::x86_64::*;
    use std::sync::OnceLock;

    use primitives::bit_fold::gfni::{OUT_BYTES, store_f192, weight_matrices};
    use primitives::field::{F64, F192, PHI_8_TABLE_192, mul_base8, mul4};

    use super::{ELL, N_MEDIUM_VALUES, gamma_powers};

    /// One worker's byte-sliced sums for `A B` and for `C`.
    pub(super) struct Convert {
        ab: [__m512i; OUT_BYTES],
        c: [__m512i; OUT_BYTES],
    }

    impl Convert {
        pub(super) const fn new() -> Self {
            // SAFETY: an all-zero bit pattern is a valid register value.
            unsafe { core::mem::zeroed() }
        }

        /// Add one window's medium bytes, a 64-lane row per medium position, at weight `eq_lo`.
        #[inline(always)]
        pub(super) fn accumulate(&mut self, ab: &[[u8; 64]], c: &[[u8; 64]], eq_lo: F192) {
            // SAFETY: the module is compiled only with these target features enabled.
            unsafe { self.accumulate_gfni(ab, c, eq_lo) }
        }

        #[target_feature(enable = "avx512f", enable = "avx512bw", enable = "avx512vbmi", enable = "gfni")]
        fn accumulate_gfni(&mut self, ab: &[[u8; 64]], c: &[[u8; 64]], eq_lo: F192) {
            // phi_8 of the unit bytes, as base-field scalars.
            static UNITS: OnceLock<[F64; 8]> = OnceLock::new();
            let units = UNITS.get_or_init(|| {
                std::array::from_fn(|s| {
                    let phi = PHI_8_TABLE_192[1 << s];
                    assert!(phi.c1 == 0 && phi.c2 == 0, "phi_8 lands in the base field");
                    F64(phi.c0)
                })
            });

            // Medium position b's matrices: the weights (gamma^b eq_lo) phi_8(2^s).
            let mut matrices = [[0u64; OUT_BYTES]; N_MEDIUM_VALUES];
            for (quad, m) in gamma_powers()
                .as_chunks::<4>()
                .0
                .iter()
                .zip(matrices.as_chunks_mut::<4>().0)
            {
                for (t, m) in mul4(*quad, [eq_lo; 4]).iter().zip(m) {
                    *m = weight_matrices(&mul_base8(*t, *units));
                }
            }

            // Eight output bytes at a time keep sixteen accumulators in registers.
            for g in 0..3 {
                let mut acc_ab: [__m512i; 8] = std::array::from_fn(|l| self.ab[8 * g + l]);
                let mut acc_c: [__m512i; 8] = std::array::from_fn(|l| self.c[8 * g + l]);
                for ((ab, c), m) in ab.iter().zip(c).zip(&matrices) {
                    // SAFETY: each row is 64 bytes.
                    let (xa, xc) = unsafe {
                        (
                            _mm512_loadu_si512(ab.as_ptr().cast()),
                            _mm512_loadu_si512(c.as_ptr().cast()),
                        )
                    };
                    for l in 0..8 {
                        let a = _mm512_set1_epi64(m[8 * g + l] as i64);
                        acc_ab[l] = _mm512_xor_si512(acc_ab[l], _mm512_gf2p8affine_epi64_epi8::<0>(xa, a));
                        acc_c[l] = _mm512_xor_si512(acc_c[l], _mm512_gf2p8affine_epi64_epi8::<0>(xc, a));
                    }
                }
                self.ab[8 * g..8 * g + 8].copy_from_slice(&acc_ab);
                self.c[8 * g..8 * g + 8].copy_from_slice(&acc_c);
            }
        }

        /// The `A B` and `C` sums.
        pub(super) fn values(&self) -> ([F192; ELL], [F192; ELL]) {
            let (mut ab, mut c) = ([F192::ZERO; ELL], [F192::ZERO; ELL]);
            // SAFETY: the module is compiled only with these target features enabled.
            unsafe {
                store_f192(&self.ab, &mut ab);
                store_f192(&self.c, &mut c);
            }
            (ab, c)
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "gfni"))]
    use primitives::bit_fold::avx2::Gfni;
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    use primitives::bit_fold::avx2::{Product, Shuffle};
    use primitives::multilinear::eq_table;
    use primitives::test_util::Rng;

    use super::*;
    use crate::zerocheck::ntt::AdditiveNttGf8;

    /// Pack bits low bit first into bytes.
    pub(crate) fn pack_bits(bits: &[bool]) -> Vec<u8> {
        bits.chunks(8)
            .map(|byte| byte.iter().rev().fold(0u8, |acc, &bit| acc << 1 | u8::from(bit)))
            .collect()
    }

    /// The byte extension from `S` to `Lambda` at the protocol's skip.
    fn lde() -> InvNttTableByteSingleGf8 {
        table(K_SKIP, F8::ZERO, F8(1 << K_SKIP))
    }

    /// The byte extension from `beta_s + S` to `beta_l + S`, `S` of size `2^k`.
    fn table(k: usize, beta_s: F8, beta_l: F8) -> InvNttTableByteSingleGf8 {
        InvNttTableByteSingleGf8::new(&AdditiveNttGf8::new(k, beta_s), &AdditiveNttGf8::new(k, beta_l))
    }

    /// The eq coordinates: the seven fixed ones, then random outer ones.
    fn protocol_r(rng: &mut Rng, m: usize) -> Vec<F192> {
        (small_challenges().into_iter().chain(medium_challenges()))
            .chain(rng.ext_vec(m - WINDOW_LOG))
            .collect()
    }

    /// The extension matrix from `S` to `Lambda` by direct Lagrange interpolation, independent of any transform.
    fn lagrange_extension_matrix(k: usize, beta_s: F8, beta_l: F8) -> Vec<Vec<F192>> {
        let ell = 1usize << k;
        let s: Vec<F8> = (0..ell).map(|j| beta_s + F8(j as u8)).collect();
        // The Lagrange denominators `prod_{h != j} (s_j + s_h)`, inverted.
        let denominators: Vec<F8> = (s.iter().enumerate())
            .map(|(j, &s_j)| {
                let others = s.iter().enumerate().filter(|&(h, _)| h != j);
                others.fold(F8::ONE, |acc, (_, &s_h)| acc * (s_j + s_h)).inv()
            })
            .collect();
        (0..ell)
            .map(|i| {
                let x = beta_l + F8(i as u8);
                let numerator = s.iter().fold(F8::ONE, |acc, &s_h| acc * (x + s_h));
                (s.iter().zip(&denominators))
                    .map(|(&s_j, &d)| phi8_192(numerator * (x + s_j).inv() * d))
                    .collect()
            })
            .collect()
    }

    /// The message by the protocol's formula: every row extended on its own, nothing factored.
    fn naive(bits: [&[bool]; 3], m: usize, r: &[F192]) -> (Vec<F192>, Vec<F192>) {
        let ntt_s = AdditiveNttGf8::new(K_SKIP, F8::ZERO);
        let ntt_l = AdditiveNttGf8::new(K_SKIP, F8(ELL as u8));
        let mut p = [vec![F192::ZERO; ELL], vec![F192::ZERO; ELL]];
        for (x, &weight) in eq_table(r).iter().enumerate().take(1 << (m - K_SKIP)) {
            // Row `x` of each vector, extended from `S` to `Lambda`.
            let [a, b, c] = bits.map(|v| {
                let mut col: Vec<F8> = v[x * ELL..(x + 1) * ELL].iter().map(|&bit| F8(bit.into())).collect();
                ntt_s.inverse(&mut col);
                ntt_l.forward(&mut col);
                col
            });
            for l in 0..ELL {
                p[0][l] += weight * phi8_192(a[l] * b[l]);
                p[1][l] += weight * phi8_192(c[l]);
            }
        }
        let [ab, c] = p;
        (ab, c)
    }

    #[test]
    fn the_extension_is_lagrange_interpolation() {
        // Invariant: the lifted transform is the Lagrange extension from S to Lambda, on any F192 input.
        //
        // Fixture state: every supported size, both halves of the byte field, random and basis inputs.
        let mut rng = Rng::new(0x0011_f7ed);
        for k in 3..=7 {
            for beta_s in [F8::ZERO, F8(0xff)] {
                let beta_l = beta_s + F8(1 << k);
                let lde = table(k, beta_s, beta_l);
                let matrix = lagrange_extension_matrix(k, beta_s, beta_l);
                let apply = |input: &[F192]| -> Vec<F192> {
                    (matrix.iter())
                        .map(|row| (row.iter().zip(input)).fold(F192::ZERO, |acc, (&w, &v)| acc + w * v))
                        .collect()
                };
                // Random inputs.
                for _ in 0..4 {
                    let input = rng.ext_vec(1 << k);
                    assert_eq!(extend(&input, &lde), apply(&input), "k={k}, beta_s={beta_s:?}");
                }
                // Each of the 192 coordinate bits, so every limb boundary of the tower basis.
                for bit in 0..192 {
                    let mut limbs = [0u64; 3];
                    limbs[bit / 64] = 1 << (bit % 64);
                    let mut input = vec![F192::ZERO; 1 << k];
                    input[bit % (1 << k)] = F192::new(limbs[0], limbs[1], limbs[2]);
                    assert_eq!(extend(&input, &lde), apply(&input), "k={k}, bit={bit}");
                }
            }
        }
    }

    #[test]
    fn the_product_bytes_are_the_scalar_route() {
        // Invariant: the packed weighted product sum is each K-row extended, multiplied and weighted by x^K.
        let lde = lde();
        let mut rng = Rng::new(0xDEAD_BEEF);
        for _ in 0..16 {
            let a: [u8; MEDIUM_BYTES] = std::array::from_fn(|_| rng.next_u8());
            let b: [u8; MEDIUM_BYTES] = std::array::from_fn(|_| rng.next_u8());
            let mut want = [F8::ZERO; ELL];
            let (mut a_col, mut b_col) = ([F8::ZERO; ELL], [F8::ZERO; ELL]);
            for k in 0..8 {
                lde.apply(&a[k * N_CHUNKS..(k + 1) * N_CHUNKS], &mut a_col);
                lde.apply(&b[k * N_CHUNKS..(k + 1) * N_CHUNKS], &mut b_col);
                for (w, (&x, &y)) in want.iter_mut().zip(a_col.iter().zip(&b_col)) {
                    *w += x * y * F8(1 << k);
                }
            }
            let mut scalar = [0; ELL];
            shift_reduce_inner_ab_scalar(&a, &b, &lde, &mut scalar);
            assert_eq!(scalar, want.map(|w| w.0), "the scalar route");
            assert_eq!(product_bytes(&a, &b, &lde), scalar, "the dispatched kernel");
        }
    }

    #[test]
    fn the_fixed_eq_weights_are_independent() {
        // Invariant: the 2^7 eq weights of the seven fixed coordinates have rank 128 over GF(2) (lem:fixed-zerocheck).
        //
        // Rank 7 of the coordinates alone would pass while a relation among their products broke the lemma.
        let a: Vec<F192> = small_challenges().into_iter().chain(medium_challenges()).collect();
        assert_eq!(a.len(), N_INNER);

        // One row per corner `b`: `eq(a, b) = prod_i (b_i ? a_i : 1 + a_i)`.
        let mut rows: Vec<[u64; 3]> = (0..1usize << N_INNER)
            .map(|b| {
                let w = (a.iter().enumerate()).fold(F192::ONE, |acc, (i, &ai)| {
                    acc * if b >> i & 1 == 1 { ai } else { F192::ONE + ai }
                });
                [w.c0, w.c1, w.c2]
            })
            .collect();

        // Row-reduce over GF(2), one pivot per column from the top bit down.
        let mut rank = 0;
        for col in (0..192).rev() {
            let (limb, mask) = (col / 64, 1u64 << (col % 64));
            let Some(p) = (rank..rows.len()).find(|&i| rows[i][limb] & mask != 0) else {
                continue;
            };
            rows.swap(rank, p);
            let pivot = rows[rank];
            for (i, row) in rows.iter_mut().enumerate() {
                if i != rank && row[limb] & mask != 0 {
                    for (x, y) in row.iter_mut().zip(pivot) {
                        *x ^= y;
                    }
                }
            }
            rank += 1;
        }
        assert_eq!(
            rank,
            1 << N_INNER,
            "the fixed eq weights must be independent over GF(2)"
        );
    }

    #[test]
    fn the_sweep_is_the_naive_message_over_c_s() {
        // Invariant: `C_s * sweep = naive`, for the `A B` and the `C` halves each.
        let c_s = c_s();
        for m in [13, 14, 15] {
            let mut rng = Rng::new(100 + m as u64);
            let (a, b) = (rng.bits(1 << m), rng.bits(1 << m));
            let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| x & y).collect();
            let r = protocol_r(&mut rng, m);
            let lde = lde();
            let (packed_a, packed_b) = (pack_bits(&a), pack_bits(&b));
            let bits = PackedWitness {
                a: &packed_a,
                b: &packed_b,
            };

            let (naive_ab, naive_c) = naive([&a, &b, &c], m, &r);
            let (ab, c) = Round1::new(bits, m, &r, &lde, &Padding::dense(m)).message();
            assert_eq!(ab.iter().map(|&x| c_s * x).collect::<Vec<_>>(), naive_ab, "A B, m={m}");
            assert_eq!(c.iter().map(|&x| c_s * x).collect::<Vec<_>>(), naive_c, "C, m={m}");
        }
    }

    #[test]
    fn skipping_padding_changes_nothing() {
        // Invariant: on blocks whose bits past the useful ones are zero, skipping them is the dense message.
        //
        // Fixture state, (k_log, useful, blocks):
        //
        //     (14, 16000, 1)   BLAKE2s
        //     (15, 31401, 1)   a boundary inside a medium position
        //     (16, 42560, 1)   a whole medium position skipped
        //     (16, 42560, 8)   several blocks
        for (k_log, useful, n_log) in [
            (14usize, 16_000usize, 0usize),
            (15, 31_401, 0),
            (16, 42_560, 0),
            (16, 42_560, 3),
        ] {
            let m = k_log + n_log;
            let mut rng = Rng::new(0xBEEF_DEAD + (k_log * 31 + m) as u64);
            let mut bit = |i: usize| i % (1 << k_log) < useful && rng.bit();
            let a: Vec<bool> = (0..1 << m).map(&mut bit).collect();
            let b: Vec<bool> = (0..1 << m).map(&mut bit).collect();
            let r = protocol_r(&mut rng, m);
            let lde = lde();
            let (packed_a, packed_b) = (pack_bits(&a), pack_bits(&b));
            let bits = PackedWitness {
                a: &packed_a,
                b: &packed_b,
            };
            let padding = Padding {
                k_log,
                useful_bits: useful,
                live_blocks: usize::MAX,
            };
            let dense = Round1::new(bits, m, &r, &lde, &Padding::dense(m)).message();
            let padded = Round1::new(bits, m, &r, &lde, &padding).message();
            assert_eq!(dense, padded, "k_log={k_log}, useful={useful}, m={m}");
        }
    }

    /// The convert's definition, lane by lane: `sum_b gamma^b * phi_8(rows[b][lane])`.
    fn reference(rows: &[[u8; 64]]) -> [F192; ELL] {
        std::array::from_fn(|lane| {
            (rows.iter().zip(gamma_powers()))
                .fold(F192::ZERO, |acc, (row, &gamma)| acc + gamma * phi8_192(F8(row[lane])))
        })
    }

    /// `n` random rows of 64 bytes.
    fn rows(rng: &mut Rng, n: usize) -> Vec<[u8; 64]> {
        (0..n).map(|_| std::array::from_fn(|_| rng.next_u8())).collect()
    }

    #[test]
    fn the_dispatched_convert_is_the_definition() {
        // Invariant: the target's convert accumulates eq_lo times the definition, per lane.
        //
        // Fixture state: two full windows of 16 medium positions, then every boundary length.
        let mut rng = Rng::new(0xC0_4E27);
        let mut convert = Convert::new();
        let (mut want_ab, mut want_c) = ([F192::ZERO; ELL], [F192::ZERO; ELL]);
        for n in [16, 16].into_iter().chain(0..16) {
            let (ab, c) = (rows(&mut rng, n), rows(&mut rng, n));
            let eq = rng.ext();
            convert.accumulate(&ab, &c, eq);
            for (lane, (w_ab, w_c)) in want_ab.iter_mut().zip(&mut want_c).enumerate() {
                *w_ab += reference(&ab)[lane] * eq;
                *w_c += reference(&c)[lane] * eq;
            }
        }
        assert_eq!(convert.values(), (want_ab, want_c));
    }

    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    #[test]
    fn every_avx2_product_converts_as_the_definition() {
        // Invariant: each AVX2 product this target compiles, not only the dispatched one, is the definition.
        fn check<P: Product>(rng: &mut Rng) {
            let maps = avx2::maps::<P>();
            for n in [16, 7] {
                let rows = rows(rng, n);
                // SAFETY: the crate is built with AVX2.
                assert_eq!(unsafe { avx2::convert::<P>(&rows, &maps) }, reference(&rows), "n={n}");
            }
        }
        let mut rng = Rng::new(0xA7_C04E);
        check::<Shuffle>(&mut rng);
        #[cfg(target_feature = "gfni")]
        check::<Gfni>(&mut rng);
    }
}
