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

use std::sync::OnceLock;

use primitives::bits::bit_transpose_64bytes;
use primitives::field::{F8, F192, phi8_192};
use primitives::multilinear::SplitEq;

use super::multilinear::PackedWitness;
use super::ntt::InvNttTableByteSingleGf8;
use super::{K_SKIP, N_INNER, Padding};
use convert::Convert;
use product::product_bytes;

mod convert;
mod product;

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

#[cfg(test)]
pub(crate) mod tests {
    use primitives::multilinear::eq_table;
    use primitives::test_util::Rng;

    use super::product::shift_reduce_inner_ab_scalar;
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
}
