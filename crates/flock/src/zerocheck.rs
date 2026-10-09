// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! The zerocheck: `a(y) b(y) + c(y) = 0` for every `y` in `{0,1}^m`, for a batch of circuits at once.
//!
//! Each circuit gives three bit vectors of length `2^m`.
//! The zerocheck leaves, per circuit, claims on the extensions of `a`, `b` and `c` at one point.
//!
//! ```text
//!     1. verifier   the eq point r: seven fixed inner coordinates, then sampled outer ones; the batching lambda
//!     2. prover     sum_f lambda^f P_f on the coset Lambda, 2^k_skip values      (the univariate skip, round 1)
//!     3. verifier   the skip challenge z
//!     4. both       one multilinear round per variable past the skip: G(1), G(inf), then its challenge
//!     5. prover     every circuit's (a, b, c) at the point, checked against the final claim
//! ```
//!
//! `c` rides the sumcheck rather than being split off at round 1.
//! That puts all three claims at one point, and leaves the lincheck one family of bit slices per circuit.
//!
//! The prover never reads `c`: an honest witness has `c = a AND b`, which it derives from the bits it reads.
//! A dishonest `c` changes nothing it sends, and the lincheck catches the claims (doc/leanvm Annex C).
//!
//! ## The skip domain
//!
//! The univariate skip's domain, and the interpolations at the skip challenge its verifiers and its prover share.
//!
//! ## The additive NTT
//!
//! The additive NTT over GF(2^8), and the table that collapses the round-1 extension through it.
//!
//! ## Round 1
//!
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
//! ### The product
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
//! ### The convert
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
//!
//! ## The multilinear rounds
//!
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
//!
//! ## Padding
//!
//! Where a batched witness is zero or repeats itself, so the zerocheck's kernels can skip it.

use std::mem::MaybeUninit;
use std::sync::OnceLock;

#[cfg(target_arch = "aarch64")]
use core::arch::aarch64::*;
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
use core::arch::x86_64::*;
use fiat_shamir::arith::{Arith, Native, Verifier};
use fiat_shamir::transcript::{Challenger, ProverState, TranscriptError, Transmitter};
use parallel::Chunks;
use primitives::bit_fold::{BLOCK, BitFold};
use primitives::bits::bit_transpose_64bytes;
#[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "gfni")))]
use primitives::field::gf2_8::avx2::gf8_mul_vec32;
use primitives::field::gf2_8::gf8_reduce;
#[cfg(target_arch = "aarch64")]
use primitives::field::gf2_8::neon::{gf8_mul_vec16, gf8_reduce_vec16};
use primitives::field::{F8, F64, F192, F192Unreduced, PHI_8_TABLE_192, phi8_192, powers};
use primitives::multilinear::{SplitEq, eq_table, skip_lagrange_weights, window_denominator};
use primitives::stream::Stream;
use thiserror::Error;

use crate::lincheck::QuirkyPoint;

/// The variables round 1 folds at once by the univariate skip.
///
/// The round-1 message is `2^K_SKIP = 64` values, one per point of the coset it is sent on.
pub const K_SKIP: usize = 6;

/// The eq coordinates the protocol fixes past the skip: three small ones, then four medium ones.
const N_INNER: usize = 7;

/// The fewest variables a zerocheck's cube can have: the skip, then the fixed coordinates.
pub const MIN_LOG_N: usize = K_SKIP + N_INNER;

/// Bit passes, two rounds each, before the folded tables are stored.
///
/// - A pass re-reads the `a` and `b` bit tables, `2 * 2^m` bits.
/// - Storing at level `t` writes three F192 tables, `3 * 192 * 2^(m - 6 - t)` bits, then reads them back.
/// - On x86 a bit pass is bandwidth-bound, so storing pays once the tables are well below the bits: level 4.
/// - On aarch64 the byte-table fold is compute-bound, its tables growing with the level: store at once.
const PAIR_PASSES: usize = if cfg!(target_arch = "aarch64") { 0 } else { 2 };

// The storing pass sends two rounds too, so the bit passes fit even the smallest cube.
const _: () = assert!(2 * PAIR_PASSES + 2 <= MIN_LOG_N - K_SKIP);

/// Smallest folded table a paired table pass takes.
///
/// Below it the tables fit L1, and one round at a time on this thread beats a parallel dispatch.
const PAIRED_MIN: usize = 1 << 10;

/// The eq coordinates past the skip: the fixed inner ones, then `m - MIN_LOG_N` drawn by `sample`.
fn equality_tail(m: usize, sample: impl FnOnce(usize) -> Vec<F192>) -> Vec<F192> {
    let outer = sample(m - MIN_LOG_N);
    small_challenges()
        .into_iter()
        .chain(medium_challenges())
        .chain(outer)
        .collect()
}

/// Claims on the extensions of `a`, `b` and `c`, all three at the point `(z, mlv_challenges)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ZerocheckClaim {
    /// The univariate-skip challenge, which binds the first `K_SKIP` variables.
    pub z: F192,

    /// The multilinear rounds' challenges, low variable first.
    pub mlv_challenges: Vec<F192>,

    /// `a` at the point.
    pub a_eval: F192,

    /// `b` at the point.
    pub b_eval: F192,

    /// `c` at the point.
    ///
    /// The batch's terminal identity ties it to the other two, and the lincheck pins all three.
    pub c_eval: F192,
}

impl ZerocheckClaim {
    /// The point split as the lincheck reads it: the skip, `inner_rest_len` inner coordinates, then the outer ones.
    pub(crate) fn point(&self, inner_rest_len: usize) -> QuirkyPoint {
        let (inner, outer) = self.mlv_challenges.split_at(inner_rest_len);
        QuirkyPoint {
            z_skip: self.z,
            x_inner_rest: inner.to_vec(),
            x_outer: outer.to_vec(),
        }
    }
}

/// Why the zerocheck verifier refuses.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum ZerocheckError {
    /// Fewer variables than the skip and the fixed coordinates take.
    #[error("log_n {log_n} is below k_skip {k_skip} plus the fixed coordinates")]
    LogNTooSmall { log_n: usize, k_skip: usize },

    /// The circuits' claims do not reproduce the sumcheck's final claim.
    #[error("the circuits' claims do not reproduce the zerocheck's final claim")]
    TerminalMismatch,

    /// The proof stream is malformed.
    #[error(transparent)]
    Transcript(#[from] TranscriptError),
}

/// One circuit's witness in a batched zerocheck: its packed `a` and `b` over a cube of `2^m` bits.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ZerocheckInput<'a> {
    /// The `a` and `b` bits.
    pub bits: PackedWitness<'a>,

    /// The base-two logarithm of the cube's bits.
    pub m: usize,

    /// Where the witness is zero or repeats itself.
    pub padding: Padding,
}

/// The folded tables of one circuit, from the pass that stores them on.
///
/// The tables lag the rounds: `pending` holds the challenges sent but not yet folded in, lowest first.
///
/// ```text
///     paired pass:   fold the pending challenges, then send two rounds from each quad of folded values
///     single round:  fold the pending challenges one at a time, then send one round
/// ```
///
/// A paired pass reads the tables once and writes a quarter of them for two rounds.
/// A single round covers the last round, and a round whose eq challenge is one, which leaves `G(0)` to send.
struct Folded {
    /// The `a`, `b` and `c` tables.
    t: [Vec<F192>; 3],
    /// Ping-pong scratch: a pass writes its folded tables into the spare capacity here, then the two swap.
    nxt: [Vec<F192>; 3],
    /// The challenges not yet folded in.
    pending: Vec<F192>,
}

impl Folded {
    /// Take the folded tables a pass wrote into the scratch, `n_out` values each.
    ///
    /// # Safety
    ///
    /// The pass wrote the first `n_out` slots of every scratch table.
    unsafe fn swap_in(&mut self, n_out: usize) {
        for (t, nxt) in self.t.iter_mut().zip(&mut self.nxt) {
            // SAFETY: the caller's pass wrote these slots, within the capacity it was handed.
            unsafe { nxt.set_len(n_out) };
            std::mem::swap(t, nxt);
        }
    }
}

/// One circuit's prover in a batched zerocheck, stepped one round at a time.
///
/// Level `t` is the round with `rho_1..rho_t` already bound.
///
/// ```text
///     bits of a, b       one bit per slot, 2 * 2^m bits; c = a AND b is derived, never read
///     one F192 table     192 bits per slot, 2^(m - 6 - t) slots
/// ```
///
/// While the tables would outweigh the bits, each pass re-reads the bits.
/// Every pass sends two rounds; the second waits on the first's challenge.
/// The last bit pass stores the three folded tables for the passes after it.
struct CircuitProver<'a> {
    /// The circuit's packed bits.
    bits: PackedWitness<'a>,
    /// Where its witness is zero or repeats itself.
    padding: Padding,
    /// The eq challenges of its variables past the skip.
    r: &'a [F192],
    /// The skip's Lagrange weights at `z`.
    lagrange: Vec<F192>,
    /// The challenges bound so far.
    chis: Vec<F192>,
    /// The running claim: `G` of the last round at its challenge.
    claim: F192,
    /// The round message just sent, as coefficients.
    message: [F192; 3],
    /// The rounds sent from the bits before the storing pass, in pairs.
    paired_bit_rounds: usize,
    /// The second round of a pass, waiting on the first's challenge.
    pair: Option<RoundPair>,
    /// The folded tables, once stored.
    folded: Option<Folded>,
}

impl<'a> CircuitProver<'a> {
    /// The prover and its round-1 message: `P` on the coset, its `a b` and `c` halves summed.
    fn new(input: &ZerocheckInput<'a>, r: &'a [F192], lde: &InvNttTableByteSingleGf8) -> (Self, Vec<F192>) {
        let ZerocheckInput { bits, m, padding } = *input;
        assert!(m >= MIN_LOG_N, "a zerocheck needs at least {MIN_LOG_N} variables");
        let cube_bytes = (1usize << m) / 8;
        assert_eq!(bits.a.len(), cube_bytes);
        assert_eq!(bits.b.len(), cube_bytes);
        let n_mlv = m - K_SKIP;
        assert_eq!(r.len(), n_mlv);

        // The fast message drops the constant `C_s` its fixed eq coordinates factor out.
        // The wire carries the plain message, so the verifier knows nothing of the trick: restore it.
        let (ab, c) = Round1::new(bits, m, r, lde, &padding).message();
        let c_s = c_s();
        let round1 = ab.iter().zip(&c).map(|(&x, &y)| c_s * (x + y)).collect();

        let prover = Self {
            bits,
            padding,
            r,
            lagrange: Vec::new(),
            chis: Vec::with_capacity(n_mlv),
            claim: F192::ZERO,
            message: [F192::ZERO; 3],
            paired_bit_rounds: 2 * PAIR_PASSES,
            pair: None,
            folded: None,
        };
        (prover, round1)
    }

    /// The variables past the skip.
    const fn n_mlv(&self) -> usize {
        self.r.len()
    }

    /// Take the skip challenge: the running claim becomes this circuit's `P(z)`.
    fn start(&mut self, z: F192, round1: &[F192]) {
        self.lagrange = skip_lagrange_weights(K_SKIP, z);
        let vanishing = SkipDomain::FLOCK.vanishing(&mut Native, z);
        self.claim = SkipDomain::FLOCK.first_round_at(&mut Native, z, vanishing, round1);
    }

    /// The next round's coefficients.
    ///
    /// `G(0)` comes from the eq split `(1 + r_eq) G(0) + r_eq G(1) = claim`.
    /// At `r_eq = 1` that leaves it free, so the round computes it.
    /// Only a table round can meet that: the bit rounds run on fixed challenges.
    fn round(&mut self) -> [F192; 3] {
        let j = self.chis.len();
        let r_eq = self.r[j];
        let (g0, g1, g_inf) = if let Some(pair) = self.pair.take() {
            let (g1, g_inf) = pair.second(self.chis[j - 1]);
            (None, g1, g_inf)
        } else if self.folded.is_none() {
            self.bit_round(j)
        } else {
            self.table_round(j)
        };
        let g0 = g0.unwrap_or_else(|| (self.claim + r_eq * g1) * (F192::ONE + r_eq).inv());
        // G(X) = G(0) (1 + X) + G(1) X + G(inf) X (1 + X).
        self.message = [g0, g0 + g1 + g_inf, g_inf];
        self.message
    }

    /// Bind the round just sent at `chi`.
    fn bind(&mut self, chi: F192) {
        self.claim = primitives::multilinear::poly_eval(&self.message, chi);
        self.chis.push(chi);
        if let Some(folded) = &mut self.folded {
            folded.pending.push(chi);
        }
    }

    /// The first round of a bit pass; the last bit pass also stores the folded tables.
    fn bit_round(&mut self, j: usize) -> (Option<F192>, F192, F192) {
        let (bits, padding, r) = (self.bits, self.padding, self.r);
        let fold = BitFold::at_level(&self.lagrange, &self.chis);
        let pair = if j < self.paired_bit_rounds {
            bit_pass(bits, &fold, &r[j + 1..], &padding)
        } else {
            let (pair, t) = bit_pass_storing(bits, &fold, &r[j + 1..], &padding);
            // The first table pass folds this pass's two challenges, a quarter of the tables out.
            let room = t[0].len() / 4;
            self.folded = Some(Folded {
                t,
                nxt: std::array::from_fn(|_| Vec::with_capacity(room)),
                pending: Vec::with_capacity(2),
            });
            pair
        };
        self.pair = Some(pair);
        (None, pair.first.0, pair.first.1)
    }

    /// A round on the folded tables: the first of a paired pass, or a single round.
    fn table_round(&mut self, j: usize) -> (Option<F192>, F192, F192) {
        let (r, padding) = (self.r, self.padding);
        let n_mlv = r.len();
        let folded = self.folded.as_mut().expect("the tables are stored");

        // The tables' length once the pending challenges are folded in.
        let n_out = folded.t[0].len() >> folded.pending.len();
        let paired = j + 1 < n_mlv && n_out >= PAIRED_MIN && r[j] != F192::ONE && r[j + 1] != F192::ONE;
        if paired {
            let [a, b, c] = &folded.t;
            let outs = folded.nxt.each_mut().map(|t| {
                t.clear();
                &mut t.spare_capacity_mut()[..n_out]
            });
            // A level-`j` value covers `2^(K_SKIP + j)` bits of the witness.
            let pair = table_pass([a, b, c], outs, &folded.pending, &r[j + 1..], &padding, K_SKIP + j);
            // SAFETY: the pass wrote the first `n_out` slots of each table.
            unsafe { folded.swap_in(n_out) };
            folded.pending.clear();
            self.pair = Some(pair);
            return (None, pair.first.0, pair.first.1);
        }

        // One round at a time: fold each pending challenge, then sum the round.
        for &rho in &folded.pending {
            for t in &mut folded.t {
                bind_low(t, rho);
            }
        }
        folded.pending.clear();
        let [a, b, c] = &folded.t;
        // The eq weights of the variables this round does not bind.
        let r_eq = &r[j + 1..];
        let (g1, g_inf) = single_round([a, b, c], r_eq);
        // An eq challenge of one leaves `G(0)` out of the claim's split: sum it directly.
        let g0 = (r[j] == F192::ONE).then(|| {
            let eq = primitives::multilinear::eq_table(r_eq);
            (eq.iter().enumerate()).fold(F192::ZERO, |acc, (x, &e)| acc + e * (a[2 * x] * b[2 * x] + c[2 * x]))
        });
        (g0, g1, g_inf)
    }

    /// The three claims, once every round is bound.
    ///
    /// Only `a` and `b` are folded to the end: `c`'s claim comes from the terminal identity.
    /// That keeps the claims the ones the transcript implies on a dishonest witness too.
    /// The running claim descends from the round-1 message, whose reconstruction assumes the zeros on the skip domain.
    fn finish(self) -> (F192, F192, F192) {
        let claim = self.claim;
        let mut folded = self.folded.expect("every circuit stores its tables");
        // Fold the last pending challenges into `a` and `b`, down to one value each.
        let [a, b, _] = &mut folded.t;
        for &rho in &folded.pending {
            bind_low(a, rho);
            bind_low(b, rho);
        }
        debug_assert_eq!(a.len(), 1);
        debug_assert_eq!(b.len(), 1);
        // The final claim is `a b + c`, which fixes `c`.
        (a[0], b[0], claim + a[0] * b[0])
    }
}

/// The zerocheck prover: `a b + c = 0` for every circuit of a batch, each circuit's `(a, b, c)` claimed at one point.
///
/// The circuits share every challenge (doc/leanvm Annex C, "Batching the circuits"):
///
/// - The eq point is one vector `r`, circuit `f` of `n_f` variables past the skip taking its first `n_f` coordinates.
/// - The batch is the circuits' polynomials times the powers of one challenge `lambda`.
/// - Each is lifted onto the batch's variables by summing over those it lacks, where its eq factor sums to one.
///
/// So round 1 sends the `lambda`-combination of the circuits' messages.
/// The rounds bind the lowest variable first, every circuit from the first round.
/// Circuit `f` is done after its `n_f` rounds, and then adds the constant `G` it ended on.
/// That constant reaches only the coefficient the claim fixes.
pub(crate) fn prove(inputs: &[ZerocheckInput<'_>], ps: &mut ProverState) -> Vec<ZerocheckClaim> {
    let n_mlv = inputs.iter().map(|i| i.m).max().expect("a batch has a circuit") - K_SKIP;

    // Phase 1: the eq point, fixed inner coordinates then sampled outer ones, and the batching challenge.
    let r = equality_tail(n_mlv + K_SKIP, |n| ps.sample_vec(n));
    let lambdas = powers(ps.sample(), inputs.len());

    // Phase 2: round 1, each circuit's message on the coset Lambda, combined by the batching powers.
    let span = tracing::info_span!("Round 1").entered();
    // The extension of a 64-bit row from the skip domain to its coset, as one byte table.
    let lde = InvNttTableByteSingleGf8::new(
        &AdditiveNttGf8::new(K_SKIP, F8::ZERO),
        &AdditiveNttGf8::new(K_SKIP, F8(1 << K_SKIP)),
    );
    let mut round1 = vec![F192::ZERO; 1 << K_SKIP];
    let provers: Vec<_> = (inputs.iter().zip(&lambdas))
        .map(|(input, &lambda)| {
            let (prover, own) = CircuitProver::new(input, &r[..input.m - K_SKIP], &lde);
            for (x, &y) in round1.iter_mut().zip(&own) {
                *x += lambda * y;
            }
            (prover, own)
        })
        .collect();
    drop(span);
    ps.add_scalars(&round1);

    // Phase 3: the skip challenge sets each circuit's running claim.
    let z = ps.sample();
    let mut provers: Vec<CircuitProver<'_>> = (provers.into_iter())
        .map(|(mut prover, own)| {
            prover.start(z, &own);
            prover
        })
        .collect();

    // Phase 4: the multilinear rounds, a circuit done early adding its constant.
    let span = tracing::info_span!("Rounds").entered();
    for j in 0..n_mlv {
        let mut message = [F192::ZERO; 3];
        for (prover, &lambda) in provers.iter_mut().zip(&lambdas) {
            let own = if j < prover.n_mlv() {
                prover.round()
            } else {
                [prover.claim, F192::ZERO, F192::ZERO]
            };
            for (m, c) in message.iter_mut().zip(own) {
                *m += lambda * c;
            }
        }
        ps.add_round_poly(&message, true);
        let chi = ps.sample();
        for prover in provers.iter_mut().filter(|p| j < p.n_mlv()) {
            prover.bind(chi);
        }
    }
    drop(span);

    // Phase 5: the claims ride the stream before the lincheck's challenge, which batches them.
    // Drawn after them, it cannot be steered by them.
    provers
        .into_iter()
        .map(|prover| {
            let mlv_challenges = prover.chis.clone();
            let (a_eval, b_eval, c_eval) = prover.finish();
            ps.add_scalars(&[a_eval, b_eval, c_eval]);
            ZerocheckClaim {
                z,
                mlv_challenges,
                a_eval,
                b_eval,
                c_eval,
            }
        })
        .collect()
}

/// What the batched zerocheck's replay leaves: its point, and each circuit's three evaluations.
///
/// Its elements are values, or whatever a verifier holds them as.
pub(crate) struct ZerocheckReplay<E> {
    /// The univariate-skip challenge.
    pub(crate) z: E,

    /// `V_S(z)`, which the lincheck's `C` terms reuse.
    pub(crate) vanishing: E,

    /// The batch's challenges, circuit `f` taking its first `m_f - K_SKIP`.
    pub(crate) mlv_challenges: Vec<E>,

    /// Each circuit's `a`, `b` and `c` at its share of the point.
    pub(crate) evals: Vec<[E; 3]>,
}

/// Replay a batched zerocheck over circuits of `2^m` bits each, `log_ns[f] = m`.
///
/// The replay walks the transcript in lockstep with the prover and carries the running claim through the rounds.
/// It then checks the terminal identity `claim = sum_f lambda^f (a_f b_f + c_f)` on the claims read.
///
/// Nothing else is checked here: the lincheck, which pins every circuit's claims to its witness, gives them meaning.
/// Never treat its success alone as acceptance.
///
/// The round-1 message is known on `Lambda` and, by the zerocheck identity, zero on `S`.
/// Those `2 * 2^k_skip` values fix a polynomial of lower degree, which the running claim interpolates at `z`.
/// A dishonest witness breaks the zeros on `S`, and the chain ends at claims the lincheck refuses.
///
/// # Errors
///
/// A circuit with too few variables, a malformed stream, or claims that miss the final claim.
pub(crate) fn verify<V: Verifier>(log_ns: &[usize], v: &mut V) -> Result<ZerocheckReplay<V::E>, ZerocheckError> {
    if let Some(&log_n) = log_ns.iter().find(|&&m| m < MIN_LOG_N) {
        return Err(ZerocheckError::LogNTooSmall { log_n, k_skip: K_SKIP });
    }
    let m = log_ns.iter().copied().max().expect("a batch has a circuit");

    // Phase 1: the eq point, the batching challenge, then the fixed coordinates as the verifier holds them.
    let outer = v.sample_vec(m - MIN_LOG_N);
    let lambda = v.sample();
    let lambdas = v.powers(lambda, log_ns.len());
    let fixed: Vec<V::E> = (small_challenges().into_iter().chain(medium_challenges()))
        .map(|c| v.constant(c))
        .collect();

    // Phase 2: round 1, interpolated at the skip challenge.
    let domain = SkipDomain::FLOCK;
    let round1 = v.next_scalars(domain.size())?;
    let z = v.sample();
    let vanishing = domain.vanishing(v, z);
    let mut claim = domain.first_round_at(v, z, vanishing, &round1);

    // Phase 3: the multilinear rounds.
    // The split `G_{j-1}(chi) = (1 + r_eq) G_j(0) + r_eq G_j(1)` absorbs the eq factor of each bound variable.
    let mut mlv_challenges = Vec::with_capacity(m - K_SKIP);
    for &r_eq in fixed.iter().chain(&outer) {
        let g = v.next_round_poly(3, claim, Some(r_eq))?;
        let chi = v.sample();
        mlv_challenges.push(chi);
        claim = v.poly_eval(&g, chi);
    }

    // Phase 4: the terminal identity, a circuit done early having carried its value unchanged since.
    let mut terminal = v.zero();
    let mut evals = Vec::with_capacity(log_ns.len());
    for &weight in &lambdas {
        let [a, b, c] = [v.next_scalar()?, v.next_scalar()?, v.next_scalar()?];
        let value = v.mul_add(a, b, c);
        terminal = v.mul_add(weight, value, terminal);
        evals.push([a, b, c]);
    }
    v.ensure_eq(terminal, claim, || ZerocheckError::TerminalMismatch)?;
    Ok(ZerocheckReplay {
        z,
        vanishing,
        mlv_challenges,
        evals,
    })
}

/// The skip domain `S`: the first `2^k_skip` nodes of the phi_8 table.
///
/// It is a subspace over GF(2), since phi_8 is linear on its index.
/// Its coset `Lambda = S + phi_8(2^k_skip)` holds the zerocheck's first message.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SkipDomain {
    k_skip: usize,
}

impl SkipDomain {
    /// The domain the zerocheck skips and the lincheck interpolates over.
    pub const FLOCK: Self = Self { k_skip: K_SKIP };

    /// The domain of `2^k_skip` nodes.
    ///
    /// # Panics
    ///
    /// If `S` and `Lambda` do not fit the phi_8 table.
    pub(crate) const fn new(k_skip: usize) -> Self {
        assert!(k_skip < 8, "the window fits the phi_8 table");
        Self { k_skip }
    }

    /// The base-two logarithm of its size.
    pub(crate) const fn k_skip(self) -> usize {
        self.k_skip
    }

    /// Its size, and the zerocheck's first message's.
    pub(crate) const fn size(self) -> usize {
        1 << self.k_skip
    }

    /// The coefficients `c_j` of `V_S(X) = prod_{s in S} (X + s) = sum_j c_j X^(2^j)`, lowest first.
    ///
    /// Adding a basis element `a` to a subspace takes `V` to `V(X)^2 + V(a) V(X)`, since `V(X + a) = V(X) + V(a)`.
    fn vanishing_coefficients(self) -> Vec<F192> {
        // The zero subspace's polynomial is `X`.
        let mut c = vec![F192::ZERO; self.k_skip + 1];
        c[0] = F192::ONE;
        // Add the basis elements `phi_8(2^j)` one at a time.
        for j in 0..self.k_skip {
            let a = PHI_8_TABLE_192[1 << j];
            let at_a = Self::linearized(&c, a);
            // `V(X)^2` shifts every coefficient up a power; `V(a) V(X)` scales them in place.
            for k in (0..=j + 1).rev() {
                let squared = if k == 0 { F192::ZERO } else { c[k - 1].square() };
                c[k] = squared + at_a * c[k];
            }
        }
        c
    }

    /// A linearized polynomial `sum_j c_j x^(2^j)` at `x`.
    fn linearized(c: &[F192], x: F192) -> F192 {
        let (mut power, mut acc) = (x, F192::ZERO);
        for &cj in c {
            acc += cj * power;
            power = power.square();
        }
        acc
    }

    /// `V_S(z)`: `k_skip` squarings and as many products by constants of `K`.
    pub fn vanishing<A: Arith>(self, a: &mut A, z: A::E) -> A::E {
        let c = self.vanishing_coefficients();
        // `z^(2^j)` for every `j`, by squaring.
        let mut powers = vec![z];
        for j in 0..self.k_skip {
            powers.push(a.square(powers[j]));
        }
        debug_assert_eq!(c[self.k_skip], F192::ONE, "the vanishing polynomial is monic");
        (c[..self.k_skip].iter().zip(&powers)).fold(powers[self.k_skip], |acc, (&cj, &p)| a.mul_const_add(p, cj, acc))
    }

    /// `1 / (z + node)` for each node.
    fn inverses_at<A: Arith>(a: &mut A, z: A::E, nodes: &[F192]) -> Vec<A::E> {
        (nodes.iter())
            .map(|&node| {
                let difference = a.add_const(z, node);
                a.inv(difference)
            })
            .collect()
    }

    /// `1 / (z + s_i)` over `S`, which the Lagrange sum over `S` takes.
    pub(crate) fn inverses<A: Arith>(self, a: &mut A, z: A::E) -> Vec<A::E> {
        Self::inverses_at(a, z, &PHI_8_TABLE_192[..self.size()])
    }

    /// `scale * sum_i values_i * inverses_i`.
    pub(crate) fn lagrange_with<A: Arith>(a: &mut A, scale: A::E, inverses: &[A::E], values: &[A::E]) -> A::E {
        assert_eq!(inverses.len(), values.len(), "a value per node");
        let zero = a.zero();
        let sum = (inverses.iter().zip(values)).fold(zero, |acc, (&h, &value)| a.mul_add(value, h, acc));
        a.mul(scale, sum)
    }

    /// The first round's message, known on `Lambda` and zero on `S`, interpolated at `z` over the window `S + Lambda`.
    ///
    /// Its value, `l` the domain's size:
    ///
    /// ```text
    ///     D_2l * V_S(z) * V_Lambda(z) * sum_i values_i / (z + lambda_i)        V_Lambda(z) = V_S(z) + V_S(phi_8(l))
    /// ```
    pub(crate) fn first_round_at<A: Arith>(self, a: &mut A, z: A::E, vanishing: A::E, values: &[A::E]) -> A::E {
        let size = self.size();
        // The coset's vanishing polynomial is the domain's shifted by a constant, `V_S` being linear.
        let lambda = &PHI_8_TABLE_192[size..2 * size];
        let offset = Self::linearized(&self.vanishing_coefficients(), lambda[0]);
        let on_lambda = a.add_const(vanishing, offset);
        let both = a.mul(vanishing, on_lambda);
        let scaled = a.mul_const(both, window_denominator(2 * size));
        let inverses = Self::inverses_at(a, z, lambda);
        Self::lagrange_with(a, scaled, &inverses, values)
    }

    /// `D_l * V_S(z)`, `l` the domain's size: the scale of the Lagrange sum over `S`.
    pub(crate) fn lagrange_scale<A: Arith>(self, a: &mut A, vanishing: A::E) -> A::E {
        a.mul_const(vanishing, window_denominator(self.size()))
    }

    /// `sum_i L_i(z) values_i` over `S`, `L_i` its Lagrange basis: `D_l * V_S(z) * sum_i values_i / (z + s_i)`.
    pub fn lagrange_at<A: Arith>(self, a: &mut A, z: A::E, vanishing: A::E, values: &[A::E]) -> A::E {
        let scaled = self.lagrange_scale(a, vanishing);
        let inverses = self.inverses(a, z);
        Self::lagrange_with(a, scaled, &inverses, values)
    }
}

/// Twiddle recurrence used to build the next subspace layer's evaluation points:
/// `next_s(s, root) = s² + root · s = s · (s + root)`.
#[inline]
fn next_s(s: F8, s_at_root: F8) -> F8 {
    s * (s + s_at_root)
}

/// Build the size-(2^k − 1) twiddle table for the additive NTT.
///
/// Layout: level-L twiddles live at offset (2^L − 1).
/// Level 0 has 2^{k-1} twiddles, level 1 has 2^{k-2}, …, level k−1 has 1.
fn compute_twiddles(k: usize, beta: F8) -> Vec<F8> {
    if k == 0 {
        return Vec::new();
    }
    let n = 1usize << k;
    let mut twiddles = vec![F8::ZERO; n - 1];

    // Layer 0: 2^{k-1} points beta + {0, 2, 4, ..., 2(write_at-1)}.
    let mut write_at = 1usize << (k - 1);
    let mut layer: Vec<F8> = (0..write_at).map(|i| beta + F8((2 * i) as u8)).collect();
    let mut s_at_root = F8::ONE;

    // Write layer 0 directly (s_at_root = 1 ⇒ no scaling needed).
    twiddles[write_at - 1..2 * write_at - 1].copy_from_slice(&layer[..write_at]);

    // Subsequent layers: halve the size, advance the recurrence, scale by s⁻¹.
    for _ in 1..k {
        write_at >>= 1;
        let next_s_root = next_s(layer[1] + layer[0], s_at_root);
        for i in 0..write_at {
            layer[i] = next_s(layer[2 * i], s_at_root);
        }
        s_at_root = next_s_root;

        let s_inv = s_at_root.inv();
        for j in 0..write_at {
            twiddles[write_at - 1 + j] = s_inv * layer[j];
        }
    }

    twiddles
}

#[inline]
fn fft_butterfly(v: &mut [F8], lambda: F8) {
    let n = v.len();
    let half = n >> 1;
    for i in 0..half {
        let w = v[half + i];
        v[i] += lambda * w;
        v[half + i] = w + v[i];
    }
}

fn fft_rec(v: &mut [F8], tw: &[F8], idx: usize) {
    let n = v.len();
    if n == 1 {
        return;
    }
    fft_butterfly(v, tw[idx - 1]);
    let half = n >> 1;
    let (lo, hi) = v.split_at_mut(half);
    fft_rec(lo, tw, 2 * idx);
    fft_rec(hi, tw, 2 * idx + 1);
}

#[inline]
fn ifft_butterfly(v: &mut [F8], lambda: F8) {
    let n = v.len();
    let half = n >> 1;
    for i in 0..half {
        v[half + i] += v[i];
        v[i] += lambda * v[half + i];
    }
}

fn ifft_rec(v: &mut [F8], tw: &[F8], idx: usize) {
    let n = v.len();
    if n == 1 {
        return;
    }
    let half = n >> 1;
    let (lo, hi) = v.split_at_mut(half);
    ifft_rec(lo, tw, 2 * idx);
    ifft_rec(hi, tw, 2 * idx + 1);
    ifft_butterfly(v, tw[idx - 1]);
}

/// Additive NTT over GF(2^8) with domain of size 2^k.
///
/// Evaluation domain `W = β + span{1, 2, …, 2^{k-1}}` (additive coset of an
/// F_2 subspace of F_{2^8}). Maximum useful `k` is 7 (|W| = 128); k = 8 would
/// exhaust all 256 elements of F_{2^8}.
///
/// Internal LCH basis: the forward transform maps coefficients in the
/// Lin-Chung-Han basis to evaluations at the 2^k points of the domain.
/// `inverse` is the exact reverse.
#[derive(Clone, Debug)]
pub(crate) struct AdditiveNttGf8 {
    k: usize,
    twiddles: Vec<F8>,
}

impl AdditiveNttGf8 {
    /// Build an NTT for a 2^k-point domain with offset β.
    pub(crate) fn new(k: usize, beta: F8) -> Self {
        Self {
            k,
            twiddles: compute_twiddles(k, beta),
        }
    }

    pub(crate) const fn k(&self) -> usize {
        self.k
    }
    const fn domain_size(&self) -> usize {
        1usize << self.k
    }

    pub(crate) fn forward(&self, v: &mut [F8]) {
        assert_eq!(v.len(), self.domain_size(), "forward: input length must be 2^k");
        if v.len() <= 1 {
            return;
        }
        fft_rec(v, &self.twiddles, 1);
    }

    pub(crate) fn inverse(&self, v: &mut [F8]) {
        assert_eq!(v.len(), self.domain_size(), "inverse: input length must be 2^k");
        if v.len() <= 1 {
            return;
        }
        ifft_rec(v, &self.twiddles, 1);
    }
}

/// §2.1 single-table collapse of the LDE matrix `M = fwd_NTT_Λ ∘ inv_NTT_S`.
///
/// Background: the URM round-1 needs to map each `ell`-bit row of the boolean
/// witness (packed as `n_chunks = ell/8` bytes) to `ell` evaluations on the
/// NTT domain `Λ`. The naive way computes inv_NTT on S then fwd_NTT on Λ for
/// every row, which is too slow.
///
/// The optimization (§2.1 of the paper): `M = α · M̃` with `M̃` Cauchy and `α`
/// a scalar. The columns of `M` satisfy a XOR-shift relation, so the `n_chunks`
/// per-byte sub-tables collapse to a single 256-row base table `T_0`:
///
///   M[i', 8b + t]  =  T_0[bit-t-mask(8b+t)][i' ⊕ 8b]
///
/// Per-byte-chunk b contributes `π_b(T_0[byte_b])` to the output, where
/// `π_b(i') = i' ⊕ 8b`.
///
/// Storage: 256 × ell bytes (16 KB at k=6, 32 KB at k=7), which fits in L1.
/// Lookups per row: n_chunks (= ell/8), each load is `ell` contiguous bytes.
#[derive(Clone, Debug)]
pub(crate) struct InvNttTableByteSingleGf8 {
    pub(crate) k: usize,
    pub(crate) ell: usize,
    pub(crate) n_chunks: usize,
    /// `data[w * ell .. (w+1) * ell]` = T_0[w], the XOR-sum of columns of `M`
    /// indexed by the set bits of `w`.
    data: Vec<F8>,
    /// The same S/Λ butterflies, lifted through φ₈ into the base field, for
    /// extending the reduced E-valued C vector without Boolean bit planes.
    twiddles: Vec<F64>,
}

impl InvNttTableByteSingleGf8 {
    /// Build the table given the two NTT instances: `ntt_S` over the input
    /// domain, `ntt_L` over the output (extension) domain. Both must have the
    /// same `k`.
    pub(crate) fn new(ntt_s: &AdditiveNttGf8, ntt_l: &AdditiveNttGf8) -> Self {
        assert_eq!(ntt_s.k(), ntt_l.k(), "ntt_S and ntt_L must share k");
        let k = ntt_s.k();
        let ell = 1usize << k;
        assert!(ell >= 8, "ell must be ≥ 8 so n_chunks ≥ 1");
        let n_chunks = ell / 8;
        assert!(n_chunks <= 16, "n_chunks must fit the i'/chunk XOR encoding");

        let mut data = vec![F8::ZERO; 256 * ell];

        // Compute the 8 unit-column images cols[t] = fwd_NTT_Λ ∘ inv_NTT_S (e_t)
        // for t ∈ 0..8. The remaining columns of M are XOR-shifted versions.
        let mut tmp = vec![F8::ZERO; ell];
        let mut cols: Vec<Vec<F8>> = Vec::with_capacity(8);
        for t in 0..8 {
            tmp.iter_mut().for_each(|x| *x = F8::ZERO);
            tmp[t] = F8::ONE;
            ntt_s.inverse(&mut tmp);
            ntt_l.forward(&mut tmp);
            cols.push(tmp.clone());
        }

        // T_0[0] already zero. T_0[2^t] = cols[t]. Then for non-power-of-two w,
        // T_0[w] = T_0[w ^ lo_bit] ⊕ T_0[lo_bit]; this builds all 256 entries
        // with one XOR per entry.
        for (t, col) in cols.iter().enumerate() {
            let entry_start = (1usize << t) * ell;
            data[entry_start..entry_start + ell].copy_from_slice(col);
        }
        for w in 3usize..256 {
            if (w & (w - 1)) == 0 {
                continue; // skip powers of 2 (already written)
            }
            let lo_bit = 1usize << w.trailing_zeros();
            let parent = w ^ lo_bit;
            // Borrow-checker friendly: read parent + bit_v slices, then write entry.
            let (parent_off, bit_off, entry_off) = (parent * ell, lo_bit * ell, w * ell);
            for i in 0..ell {
                let v = data[parent_off + i] + data[bit_off + i];
                data[entry_off + i] = v;
            }
        }

        Self {
            k,
            ell,
            n_chunks,
            data,
            twiddles: ntt_s
                .twiddles
                .iter()
                .chain(&ntt_l.twiddles)
                .map(|&t| F64(phi8_192(t).c0))
                .collect(),
        }
    }

    /// Extend E-valued evaluations from S to Λ in place. The GF8 embedding
    /// lies in K, so each butterfly multiplies the three E limbs by one K
    /// twiddle. These are the original GF8 domains and LCH basis, not the
    /// polynomial-basis domains of the GF64 NTT.
    pub(crate) fn extend_lifted(&self, v: &mut [F192]) {
        assert_eq!(v.len(), self.ell);
        let (twiddles_s, twiddles_l) = self.twiddles.split_at(self.ell - 1);

        // Inverse on S: children before parents in the twiddle tree.
        for level in (0..self.k).rev() {
            let nodes = 1usize << level;
            let size = self.ell >> level;
            let twiddles = &twiddles_s[nodes - 1..2 * nodes - 1];
            for (block, &lambda) in v.chunks_exact_mut(size).zip(twiddles) {
                let (lo, hi) = block.split_at_mut(size / 2);
                if lambda == F64::ZERO {
                    for (a, b) in lo.iter().zip(hi) {
                        *b += *a;
                    }
                } else {
                    for (a, b) in lo.iter_mut().zip(hi) {
                        *b += *a;
                        *a += b.mul_base(lambda);
                    }
                }
            }
        }

        // Forward on Λ: parents before children, with the same point order.
        for level in 0..self.k {
            let nodes = 1usize << level;
            let size = self.ell >> level;
            let twiddles = &twiddles_l[nodes - 1..2 * nodes - 1];
            for (block, &lambda) in v.chunks_exact_mut(size).zip(twiddles) {
                let (lo, hi) = block.split_at_mut(size / 2);
                if lambda == F64::ZERO {
                    for (a, b) in lo.iter().zip(hi) {
                        *b += *a;
                    }
                } else {
                    for (a, b) in lo.iter_mut().zip(hi) {
                        *a += b.mul_base(lambda);
                        *b += *a;
                    }
                }
            }
        }
    }

    /// Raw pointer to the table data (`256 × ell` bytes, row-major). Used by
    /// the URM fused inner kernel, which can't go through the safe slice API
    /// without losing the register-fused layout.
    #[cfg(target_arch = "aarch64")]
    #[inline]
    pub(crate) const fn data_ptr(&self) -> *const u8 {
        self.data.as_ptr() as *const u8
    }

    /// Apply M to a single byte-packed row, in place.
    /// `bytes` is `n_chunks` bytes (the LCH-coefficient bits of the row);
    /// `out` will be filled with the `ell` evaluations on Λ.
    ///
    /// Dispatches: NEON on aarch64 / SSE2 on x86_64 when `ell ≥ 16`, which
    /// covers every supported arch at the protocol size (k_skip=6 ⇒ ell=64).
    /// The scalar arm is reachable only at `ell < 16`, i.e. k=3, which occurs
    /// only in tests.
    #[inline]
    pub(crate) fn apply(&self, bytes: &[u8], out: &mut [F8]) {
        #[cfg(target_arch = "aarch64")]
        if self.ell >= 16 {
            // SAFETY: aarch64 statically guarantees NEON; ell ≥ 16 ⇒ at least
            // one 128-bit chunk; method validates slice lengths.
            unsafe { self.apply_v128::<Neon>(bytes, out) };
            return;
        }
        #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
        if self.ell == 64 {
            // SAFETY: avx512f is enabled at compile time; the method validates
            // slice lengths and requires exactly this `ell`.
            unsafe { self.apply_avx512(bytes, out) };
            return;
        }
        #[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
        if self.ell == 64 {
            // SAFETY: avx2 is enabled at compile time; the method validates
            // slice lengths and requires exactly this `ell`.
            unsafe { self.apply_avx2(bytes, out) };
            return;
        }
        #[cfg(target_arch = "x86_64")]
        if self.ell >= 16 {
            // SAFETY: x86_64 statically guarantees SSE2; ell ≥ 16 ⇒ at least
            // one 128-bit chunk; method validates slice lengths.
            unsafe { self.apply_v128::<Sse2>(bytes, out) };
            return;
        }
        self.apply_scalar(bytes, out);
    }

    /// [`apply`](Self::apply) at the protocol's `ell = 64`, one register wide.
    ///
    /// # Safety
    /// Requires AVX-512F, and `self.ell` must be 64. The method validates slice
    /// lengths.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
    #[inline]
    #[target_feature(enable = "avx512f")]
    unsafe fn apply_avx512(&self, bytes: &[u8], out: &mut [F8]) {
        assert_eq!(out.len(), self.ell);
        let bytes: &[u8; 8] = bytes.try_into().expect("8 bytes at ell = 64");
        // SAFETY: the single store covers exactly `out`.
        unsafe { _mm512_storeu_si512(out.as_mut_ptr().cast(), self.apply_zmm(bytes)) };
    }

    /// The 64 evaluations of one 8-byte row as one ZMM, at `ell = 64`.
    ///
    /// Byte `b`'s row enters permuted by `i' ⊕ 8b`, an XOR of `b` on the qword index.
    /// The rows are summed as a tree, so each bit of `b` is one fixed shuffle:
    /// bit 0 swaps the qwords of each 128-bit lane, bits 1 and 2 swap lanes, and only those two cross a lane.
    ///
    /// # Panics
    /// Panics unless `self.ell` is 64.
    ///
    /// # Safety
    /// Requires AVX-512F, which the target enables wherever this is compiled.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
    #[inline]
    #[target_feature(enable = "avx512f")]
    pub(crate) fn apply_zmm(&self, bytes: &[u8; 8]) -> __m512i {
        assert_eq!(self.ell, 64);
        let base = self.data.as_ptr().cast::<u8>();
        // SAFETY: every row offset is `byte * 64` into a `256 * 64` table.
        let row = |b: usize| unsafe { _mm512_loadu_si512(base.add(bytes[b] as usize * 64).cast()) };
        let swap_qwords = |v| _mm512_shuffle_epi32::<0x4E>(v);
        let swap_lanes = |v| _mm512_shuffle_i64x2::<0xB1>(v, v);
        let swap_halves = |v| _mm512_shuffle_i64x2::<0x4E>(v, v);
        let pair = |b: usize| _mm512_xor_si512(row(b), swap_qwords(row(b + 1)));
        let lo = _mm512_xor_si512(pair(0), swap_lanes(pair(2)));
        let hi = _mm512_xor_si512(pair(4), swap_lanes(pair(6)));
        _mm512_xor_si512(lo, swap_halves(hi))
    }

    /// [`apply`](Self::apply) at the protocol's `ell = 64`, two registers wide.
    ///
    /// The `i' ⊕ 8b` permutation is a qword-index XOR by `b`: bit 0 swaps the qwords of each lane, bit 1 the lanes, bit 2
    /// the registers.
    ///
    /// # Safety
    /// Requires AVX2, and `self.ell` must be 64. The method validates slice
    /// lengths.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    #[cfg_attr(target_feature = "avx512f", allow(dead_code))]
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn apply_avx2(&self, bytes: &[u8], out: &mut [F8]) {
        assert_eq!(self.ell, 64);
        assert_eq!(bytes.len(), self.n_chunks);
        assert_eq!(out.len(), self.ell);
        // SAFETY: every row offset is `byte * 64` into a `256 * 64` table, and
        // the two stores cover exactly `out`.
        unsafe {
            let base = self.data.as_ptr().cast::<u8>();
            let row = |b: usize| {
                let p = base.add(bytes[b] as usize * 64);
                (_mm256_loadu_si256(p.cast()), _mm256_loadu_si256(p.add(32).cast()))
            };
            let (mut lo, mut hi) = row(0);
            for b in 1..8 {
                let (mut l, mut h) = row(b);
                if b & 1 != 0 {
                    (l, h) = (
                        _mm256_shuffle_epi32::<0b01_00_11_10>(l),
                        _mm256_shuffle_epi32::<0b01_00_11_10>(h),
                    );
                }
                if b & 2 != 0 {
                    (l, h) = (
                        _mm256_permute4x64_epi64::<0b01_00_11_10>(l),
                        _mm256_permute4x64_epi64::<0b01_00_11_10>(h),
                    );
                }
                if b & 4 != 0 {
                    (l, h) = (h, l);
                }
                lo = _mm256_xor_si256(lo, l);
                hi = _mm256_xor_si256(hi, h);
            }
            let dst = out.as_mut_ptr().cast::<u8>();
            _mm256_storeu_si256(dst.cast(), lo);
            _mm256_storeu_si256(dst.add(32).cast(), hi);
        }
    }

    /// Scalar reference. Kept public so tests can use it as the cross-check
    /// oracle for the NEON variant.
    pub(crate) fn apply_scalar(&self, bytes: &[u8], out: &mut [F8]) {
        assert_eq!(bytes.len(), self.n_chunks);
        assert_eq!(out.len(), self.ell);
        out.iter_mut().for_each(|x| *x = F8::ZERO);
        for (b, &byte_b) in bytes.iter().enumerate() {
            let row_off = byte_b as usize * self.ell;
            let row = &self.data[row_off..row_off + self.ell];
            let shift = 8 * b;
            for i in 0..self.ell {
                out[i] += row[i ^ shift];
            }
        }
    }

    /// SIMD variant of `apply`, operating in 16-byte chunks.
    ///
    /// For each output chunk `c ∈ 0..ell/16`:
    ///   * `b = 0`: straight 16-byte copy from `row0[c]`
    ///   * `b ≥ 1`: load `row_b[c ⊕ (b>>1)]`, half-swap if `b` is odd, XOR
    ///
    /// The `b>>1` chunk-XOR and the `8 · b` within-chunk shift together
    /// implement the `π_b(i') = i' ⊕ 8b` permutation that the §2.1 collapse
    /// requires.
    ///
    /// This is the URM round-1 inner loop and it must inline into flock's
    /// `shift_reduce_inner_ab_gfni`, hence `#[inline(always)]` here and on
    /// every [`Vec128`] method.
    ///
    /// # Safety
    /// `V`'s target features must be available (statically true at the
    /// dispatch site for both NEON on aarch64 and SSE2 on x86_64). The method
    /// validates slice lengths.
    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[inline(always)]
    unsafe fn apply_v128<V: Vec128>(&self, bytes: &[u8], out: &mut [F8]) {
        assert_eq!(bytes.len(), self.n_chunks);
        assert_eq!(out.len(), self.ell);
        let n128 = self.ell / 16; // 4 for ell = 64
        let base = self.data.as_ptr() as *const u8;
        let out_ptr = out.as_mut_ptr() as *mut u8;

        // SAFETY: the caller guarantees `V`'s features. `data` is `256 * ell` bytes and each row index is a byte, so
        // row `bytes[b] * ell` has `ell` bytes; `ell` is a power of two, `n128 = ell / 16` and
        // `b >> 1 <= (n_chunks - 1) / 2 < n128`, so every chunk index `c ^ (b >> 1)` stays below `n128`, and each
        // 16-byte access lies inside its row or inside `out`, whose length is asserted to be `ell`.
        unsafe {
            // b = 0: identity permutation, a straight copy from row 0.
            let row0 = base.add(bytes[0] as usize * self.ell);
            for c in 0..n128 {
                V::store(out_ptr.add(c * 16), V::load(row0.add(c * 16)));
            }

            // b ≥ 1: XOR with table row[bytes[b]], permuted.
            for (b, &byte) in bytes.iter().enumerate().take(self.n_chunks).skip(1) {
                let b_high = b >> 1;
                let b_odd = (b & 1) != 0;
                let row_b = base.add(byte as usize * self.ell);
                if b_odd {
                    for c in 0..n128 {
                        let v = V::load(row_b.add((c ^ b_high) * 16)).swap64();
                        let dst = out_ptr.add(c * 16);
                        V::store(dst, V::load(dst).xor(v));
                    }
                } else {
                    for c in 0..n128 {
                        let v = V::load(row_b.add((c ^ b_high) * 16));
                        let dst = out_ptr.add(c * 16);
                        V::store(dst, V::load(dst).xor(v));
                    }
                }
            }
        }
    }
}

/// The four inlined 128-bit primitives used by `apply_v128`'s inner loop.
#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
trait Vec128: Copy {
    /// # Safety
    /// `p` must be readable for 16 bytes (alignment not required).
    unsafe fn load(p: *const u8) -> Self;
    /// # Safety
    /// `p` must be writable for 16 bytes (alignment not required).
    unsafe fn store(p: *mut u8, v: Self);
    fn xor(self, other: Self) -> Self;
    /// Swap the two 64-bit halves.
    fn swap64(self) -> Self;
}

#[cfg(target_arch = "aarch64")]
#[derive(Clone, Copy)]
struct Neon(core::arch::aarch64::uint8x16_t);

#[cfg(target_arch = "aarch64")]
impl Vec128 for Neon {
    #[inline(always)]
    unsafe fn load(p: *const u8) -> Self {
        // SAFETY: NEON is part of the aarch64 baseline, and the caller guarantees 16 readable bytes at `p`.
        Self(unsafe { core::arch::aarch64::vld1q_u8(p) })
    }
    #[inline(always)]
    unsafe fn store(p: *mut u8, v: Self) {
        // SAFETY: NEON is part of the aarch64 baseline, and the caller guarantees 16 writable bytes at `p`.
        unsafe { core::arch::aarch64::vst1q_u8(p, v.0) }
    }
    #[inline(always)]
    fn xor(self, other: Self) -> Self {
        // SAFETY: NEON is part of the aarch64 baseline; registers only.
        Self(unsafe { core::arch::aarch64::veorq_u8(self.0, other.0) })
    }
    #[inline(always)]
    fn swap64(self) -> Self {
        // SAFETY: NEON is part of the aarch64 baseline; registers only.
        Self(unsafe { core::arch::aarch64::vextq_u8::<8>(self.0, self.0) })
    }
}

#[cfg(target_arch = "x86_64")]
#[derive(Clone, Copy)]
struct Sse2(core::arch::x86_64::__m128i);

#[cfg(target_arch = "x86_64")]
impl Vec128 for Sse2 {
    #[inline(always)]
    unsafe fn load(p: *const u8) -> Self {
        // SAFETY: SSE2 is part of the x86-64 baseline, and the caller guarantees 16 readable bytes at `p`;
        // the load is unaligned.
        Self(unsafe { core::arch::x86_64::_mm_loadu_si128(p as *const core::arch::x86_64::__m128i) })
    }
    #[inline(always)]
    unsafe fn store(p: *mut u8, v: Self) {
        // SAFETY: SSE2 is part of the x86-64 baseline, and the caller guarantees 16 writable bytes at `p`;
        // the store is unaligned.
        unsafe { core::arch::x86_64::_mm_storeu_si128(p as *mut core::arch::x86_64::__m128i, v.0) }
    }
    #[inline(always)]
    fn xor(self, other: Self) -> Self {
        // SAFETY: SSE2 is part of the x86-64 baseline; registers only.
        unsafe { Self(core::arch::x86_64::_mm_xor_si128(self.0, other.0)) }
    }
    #[inline(always)]
    fn swap64(self) -> Self {
        // SAFETY: SSE2 is part of the x86-64 baseline; registers only.
        unsafe { Self(core::arch::x86_64::_mm_shuffle_epi32::<0b01_00_11_10>(self.0)) }
    }
}

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

/// Where the padding of a batched witness lies.
///
/// The witness is `2^(m - k_log)` blocks of `2^k_log` bits, each its data first and zero padding after.
/// A run of zero bits adds nothing to a round message, so skipping it leaves the message unchanged.
///
/// The blocks from `live_blocks` on are copies of one padding block.
/// While the rounds bind variables inside a block, the kernels sum one copy, weighted by the tail's eq mass.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Padding {
    /// The base-two logarithm of the bits in one block.
    pub k_log: usize,

    /// The bits at the start of each block that carry data; the rest are zero.
    pub useful_bits: usize,

    /// The blocks before the identical tail; at least the block count when there is none.
    pub live_blocks: usize,
}

impl Padding {
    /// Every bit of a cube of `2^m` bits useful, and no tail.
    #[cfg(test)]
    pub(crate) const fn dense(m: usize) -> Self {
        Self {
            k_log: m,
            useful_bits: 1 << m,
            live_blocks: 1,
        }
    }

    /// The same blocks, with no tail known.
    pub(crate) const fn without_tail(self) -> Self {
        Self {
            live_blocks: usize::MAX,
            ..self
        }
    }

    /// Split a kernel's cube of `2^m` bits at the tail, or `None` when that saves nothing.
    ///
    /// - The head is a whole number of groups and of `2^step_log`-bit steps, the kernel's unit of work.
    /// - A group is a block, or enough whole blocks for the kernel's smallest cube, `2^min_group_log` bits.
    /// - `r` are the kernel's eq challenges, the last of which index the groups.
    /// - The cube's last group stands for every group past the head: they are all copies of it.
    pub(crate) fn tail(&self, m: usize, min_group_log: usize, step_log: usize, r: &[F192]) -> Option<Tail> {
        // Groups of at least one block, and at most the cube.
        let group_log = self.k_log.max(min_group_log);
        if group_log >= m {
            return None;
        }
        let n_groups_log = m - group_log;

        // The groups holding a live block, rounded up to whole steps.
        let live_groups = self.live_blocks.div_ceil(1 << (group_log - self.k_log));
        if live_groups >= 1 << n_groups_log {
            return None;
        }
        let first = live_groups.next_multiple_of(1 << step_log.saturating_sub(group_log));
        if first >= 1 << n_groups_log {
            return None;
        }
        Some(Tail {
            head: first << group_log,
            group_log,
            r_inner: r.len() - n_groups_log,
            weight: eq_mass_from(&r[r.len() - n_groups_log..], first),
        })
    }
}

/// A kernel's cube split by its tail: the head it sums as is, then its last group once for the rest.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Tail {
    /// Bits in the head.
    pub head: usize,

    /// The base-two logarithm of the bits in a group.
    pub group_log: usize,

    /// The eq challenges inside a group: the kernel's first `r_inner`.
    pub r_inner: usize,

    /// The eq mass of the groups past the head.
    pub weight: F192,
}

impl Tail {
    /// The last group's bytes of a packed witness.
    pub(crate) fn group<'a>(&self, packed: &'a [u8]) -> &'a [u8] {
        &packed[packed.len() - (1 << self.group_log) / 8..]
    }
}

/// `sum_{x >= from} eq(r, x)`, `x` read low bit first.
///
/// The whole cube's mass is one, so this is one plus the mass below `from`.
fn eq_mass_from(r: &[F192], from: usize) -> F192 {
    let mut below = F192::ZERO;
    // The eq factor of the bits above the current one, set to `from`'s.
    let mut above = F192::ONE;
    for (k, &r_k) in r.iter().enumerate().rev() {
        if from >> k & 1 == 1 {
            // Every `x` agreeing above and with this bit clear lies below `from`.
            below += above * (F192::ONE + r_k);
            above *= r_k;
        } else {
            above *= F192::ONE + r_k;
        }
    }
    F192::ONE + below
}

#[cfg(test)]
mod tests {
    use fiat_shamir::transcript::{ProofTranscript, VerifierState};
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "gfni"))]
    use primitives::bit_fold::avx2::Gfni;
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    use primitives::bit_fold::avx2::{Product, Shuffle};
    use primitives::test_util::Rng;

    use super::*;

    const LABEL: &[u8] = b"flock-test-v0";

    /// An honest witness of `2^m` bits, `c = a AND b`: the bits, then `a` and `b` packed.
    fn honest(rng: &mut Rng, m: usize) -> ([Vec<bool>; 3], [Vec<u8>; 2]) {
        let (a, b) = (rng.bits(1 << m), rng.bits(1 << m));
        let c = a.iter().zip(&b).map(|(x, y)| x & y).collect();
        let packed = [pack_bits(&a), pack_bits(&b)];
        ([a, b, c], packed)
    }

    /// Prove one dense circuit.
    fn prove_one([a, b]: &[Vec<u8>; 2], m: usize) -> (ZerocheckClaim, ProofTranscript) {
        let input = ZerocheckInput {
            bits: PackedWitness { a, b },
            m,
            padding: Padding::dense(m),
        };
        let mut ps = ProverState::from_label(LABEL);
        let claim = prove(&[input], &mut ps).pop().expect("one circuit");
        (claim, ps.into_proof())
    }

    /// Replay one circuit.
    fn verify_one(m: usize, vs: &mut VerifierState<'_>) -> Result<ZerocheckClaim, ZerocheckError> {
        let replay = verify(&[m], vs)?;
        let [[a_eval, b_eval, c_eval]] = replay.evals[..] else {
            unreachable!("one circuit")
        };
        Ok(ZerocheckClaim {
            z: replay.z,
            mlv_challenges: replay.mlv_challenges,
            a_eval,
            b_eval,
            c_eval,
        })
    }

    /// A Boolean witness's extension at `(z, chi)`: the skip's Lagrange combination of its bit slices' extensions.
    fn quirky_eval(bits: &[bool], z: F192, chi: &[F192]) -> F192 {
        let weights = skip_lagrange_weights(K_SKIP, z);
        let eq = primitives::multilinear::eq_table(chi);
        let mut acc = F192::ZERO;
        for (row, &e) in bits.chunks(1 << K_SKIP).zip(&eq) {
            for (&bit, &w) in row.iter().zip(&weights) {
                if bit {
                    acc += e * w;
                }
            }
        }
        acc
    }

    /// Whether a claim holds the true evaluations of all three bit vectors.
    fn all_true(claim: &ZerocheckClaim, [a, b, c]: &[Vec<bool>; 3]) -> bool {
        let chi = &claim.mlv_challenges;
        claim.a_eval == quirky_eval(a, claim.z, chi)
            && claim.b_eval == quirky_eval(b, claim.z, chi)
            && claim.c_eval == quirky_eval(c, claim.z, chi)
    }

    #[test]
    fn an_honest_proof_replays_to_the_true_evaluations() {
        // Invariant: on an honest witness, the replay accepts and its claims are the prover's and the truth.
        //
        // Fixture state: the smallest cube, 13 variables, up to 17, which reaches the table passes.
        for m in 13..=17 {
            let mut rng = Rng::new(2024 + m as u64);
            let (bits, packed) = honest(&mut rng, m);
            let (claim, proof) = prove_one(&packed, m);

            // The stream is round 1, two words per multilinear round, then the three claims.
            assert_eq!(proof.stream.len(), (1 << K_SKIP) + 2 * (m - K_SKIP) + 3, "m={m}");

            let mut vs = VerifierState::from_label(LABEL, &proof);
            let replayed = verify_one(m, &mut vs).unwrap_or_else(|e| panic!("m={m}: {e:?}"));
            assert_eq!(claim, replayed, "m={m}");
            assert!(all_true(&claim, &bits), "m={m}");
        }
    }

    #[test]
    fn a_false_statement_or_a_tampered_word_leaves_a_wrong_claim() {
        // Invariant: no false run leaves all three claims true.
        // The zerocheck alone cannot refuse one; the lincheck, which pins the claims to the witness, then does.
        //
        // Mutation 1: flip one to four bits of `c`, so `a b + c = 0` fails somewhere.
        for m in [13, 14, 15] {
            for seed in 0..20u64 {
                let mut rng = Rng::new(0xBADC0DE ^ seed ^ ((m as u64) << 32));
                let ([a, b, mut c], packed) = honest(&mut rng, m);
                for _ in 0..1 + rng.next_u64() % 4 {
                    let i = rng.next_u64() as usize % c.len();
                    c[i] = !c[i];
                }
                let (_, proof) = prove_one(&packed, m);
                let mut vs = VerifierState::from_label(LABEL, &proof);
                let claim = verify_one(m, &mut vs).expect("the shape is valid");
                assert!(!all_true(&claim, &[a, b, c]), "m={m}, seed={seed}");
            }
        }

        // Mutation 2: one word in every region of an honest proof.
        //
        //     [round 1: 64 words][2 per round, 8 rounds][a, b, c]
        let m = 14;
        let mut rng = Rng::new(5050);
        let (bits, packed) = honest(&mut rng, m);
        let (_, proof) = prove_one(&packed, m);
        let (ell, n_mlv) = (1 << K_SKIP, m - K_SKIP);
        for (label, word) in [
            ("round 1, first", 0),
            ("round 1, sixth", 5),
            ("first round, G(1)", ell),
            ("middle round, G(inf)", ell + 2 * (n_mlv / 2) + 1),
            ("a", ell + 2 * n_mlv),
            ("b", ell + 2 * n_mlv + 1),
            ("c", ell + 2 * n_mlv + 2),
        ] {
            let mut bad = proof.clone();
            bad.stream[word] += F192::ONE;
            let mut vs = VerifierState::from_label(LABEL, &bad);
            match verify_one(m, &mut vs) {
                Err(ZerocheckError::TerminalMismatch) => {}
                Err(e) => panic!("{label}: refused on its shape, {e:?}"),
                Ok(claim) => assert!(!all_true(&claim, &bits), "{label} left every claim true"),
            }
        }
    }

    #[test]
    fn a_malformed_proof_is_refused_on_its_shape() {
        let m = 14;
        let mut rng = Rng::new(606);
        let (_, packed) = honest(&mut rng, m);
        let (_, proof) = prove_one(&packed, m);

        // Mutation: drop the three claims, so the replay runs out of words.
        let mut short = proof.clone();
        short.stream.truncate(short.stream.len() - 3);
        let mut vs = VerifierState::from_label(LABEL, &short);
        assert!(matches!(verify_one(m, &mut vs), Err(ZerocheckError::Transcript(_))));

        // Mutation: claim a cube below the skip and the fixed coordinates.
        let mut vs = VerifierState::from_label(LABEL, &proof);
        assert!(matches!(
            verify_one(MIN_LOG_N - 1, &mut vs),
            Err(ZerocheckError::LogNTooSmall { .. })
        ));
    }

    #[test]
    fn the_claims_are_bound_before_the_next_challenge() {
        // Invariant: the lincheck batches the three claims by one challenge drawn after them.
        // Drawn before, a prover knowing it could pick claims that satisfy the batch but not each tie.
        //
        // Mutation: `(a, b) -> (a t, b / t)` keeps `a b`, so the terminal identity still holds.
        // Only the transcript can tell the two runs apart: the next challenge must move.
        let m = 14;
        let mut rng = Rng::new(0xF1A7_5A11);
        let (_, packed) = honest(&mut rng, m);
        let (claim, proof) = prove_one(&packed, m);

        let mut vs = VerifierState::from_label(LABEL, &proof);
        verify_one(m, &mut vs).expect("honest");
        let alpha = Challenger::sample(&mut vs);

        let t = F192::new(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 0x55aa_aa55_0123_4567);
        let n = proof.stream.len();
        let mut bad = proof.clone();
        bad.stream[n - 3] *= t;
        bad.stream[n - 2] *= t.inv();
        assert_eq!(bad.stream[n - 3] * bad.stream[n - 2], claim.a_eval * claim.b_eval);

        let mut vs = VerifierState::from_label(LABEL, &bad);
        verify_one(m, &mut vs).expect("the terminal identity still holds");
        assert_ne!(Challenger::sample(&mut vs), alpha, "the claims are not bound");
    }

    /// One circuit of a test batch: its cube, its packed `a` and `b`, and its three bit vectors.
    struct TestCircuit {
        m: usize,
        packed: [Vec<u8>; 2],
        dense: [Vec<bool>; 3],
    }

    /// An honest witness of `2^m` bits whose 512-bit blocks are empty from position 400 on.
    fn padded_circuit(rng: &mut Rng, m: usize) -> TestCircuit {
        let mut bit = |i: usize| i % 512 < 400 && rng.bit();
        let a: Vec<bool> = (0..1 << m).map(&mut bit).collect();
        let b: Vec<bool> = (0..1 << m).map(&mut bit).collect();
        let c = a.iter().zip(&b).map(|(x, y)| x & y).collect();
        TestCircuit {
            m,
            packed: [pack_bits(&a), pack_bits(&b)],
            dense: [a, b, c],
        }
    }

    /// The bits of a cube folded at `z` over the skip: one value per position past it.
    fn at_z(bits: &[bool], z: F192) -> Vec<F192> {
        let weights = skip_lagrange_weights(K_SKIP, z);
        (bits.chunks(1 << K_SKIP))
            .map(|row| (row.iter().zip(&weights)).fold(F192::ZERO, |acc, (&bit, &w)| if bit { acc + w } else { acc }))
            .collect()
    }

    #[test]
    fn a_batch_sends_the_sum_of_its_circuits_rounds() {
        // Invariant: every message is the lambda-combination of each circuit's own, on circuits of mixed sizes.
        //
        //     round 1          interpolates to sum_f lambda^f P_f(z)
        //     each round       sum_f lambda^f of the circuit's round, a done circuit adding its constant
        //     the claims       each circuit's true evaluations
        let mut rng = Rng::new(0xBA7C);
        let circuits: Vec<TestCircuit> = [13, 17, 15, 20, 16].map(|m| padded_circuit(&mut rng, m)).into();
        let padding = Padding {
            k_log: 9,
            useful_bits: 400,
            live_blocks: usize::MAX,
        };
        let inputs: Vec<ZerocheckInput<'_>> = (circuits.iter())
            .map(|c| {
                let [a, b] = &c.packed;
                ZerocheckInput {
                    bits: PackedWitness { a, b },
                    m: c.m,
                    padding,
                }
            })
            .collect();
        let mut ps = ProverState::from_label(LABEL);
        let claims = prove(&inputs, &mut ps);
        let proof = ps.into_proof();

        // Replay the challenges by hand, folding each circuit's tables naively alongside.
        let mut vs = VerifierState::from_label(LABEL, &proof);
        let n_mlv = circuits.iter().map(|c| c.m).max().unwrap() - K_SKIP;
        let r = equality_tail(n_mlv + K_SKIP, |n| Challenger::sample_vec(&mut vs, n));
        let lambdas = powers(Challenger::sample(&mut vs), circuits.len());
        let round1 = vs.next_scalars(1 << K_SKIP).unwrap();
        let z = Challenger::sample(&mut vs);
        let mut tables: Vec<[Vec<F192>; 3]> = circuits
            .iter()
            .map(|c| c.dense.clone().map(|bits| at_z(&bits, z)))
            .collect();

        // Round 1: the combination of each circuit's eq-weighted sum.
        let p_at_z = (tables.iter().zip(&lambdas)).fold(F192::ZERO, |acc, ([a, b, c], &lambda)| {
            let eq = primitives::multilinear::eq_table(&r[..a.len().trailing_zeros() as usize]);
            acc + lambda * (0..a.len()).fold(F192::ZERO, |acc, v| acc + eq[v] * (a[v] * b[v] + c[v]))
        });
        let vanishing = SkipDomain::FLOCK.vanishing(&mut Native, z);
        let mut claim = SkipDomain::FLOCK.first_round_at(&mut Native, z, vanishing, &round1);
        assert_eq!(claim, p_at_z, "round 1");

        // Each later round, a done circuit carrying its `G` at its last challenge.
        let mut done = vec![F192::ZERO; circuits.len()];
        for j in 0..n_mlv {
            let mut expected = [F192::ZERO; 3];
            let mut own = Vec::new();
            for (f, [a, b, c]) in tables.iter().enumerate() {
                let coeffs = if a.len() > 1 {
                    let eq = primitives::multilinear::eq_table(&r[j + 1..j + a.len().trailing_zeros() as usize]);
                    let mut g = [F192::ZERO; 3];
                    for (v, &e) in eq.iter().enumerate() {
                        let (lo, hi) = (2 * v, 2 * v + 1);
                        g[0] += e * (a[lo] * b[lo] + c[lo]);
                        g[1] += e * (a[hi] * b[hi] + c[hi]);
                        g[2] += e * (a[lo] + a[hi]) * (b[lo] + b[hi]);
                    }
                    [g[0], g[0] + g[1] + g[2], g[2]]
                } else {
                    [done[f], F192::ZERO, F192::ZERO]
                };
                for (e, x) in expected.iter_mut().zip(coeffs) {
                    *e += lambdas[f] * x;
                }
                own.push(coeffs);
            }
            let message = vs.next_round_poly(3, claim, Some(r[j])).unwrap();
            assert_eq!(message, expected, "round {j}");
            let chi = Challenger::sample(&mut vs);
            claim = primitives::multilinear::poly_eval(&message, chi);
            for (f, t) in tables.iter_mut().enumerate() {
                if t[0].len() > 1 {
                    for v in t.iter_mut() {
                        *v = (0..v.len() / 2)
                            .map(|i| v[2 * i] + chi * (v[2 * i] + v[2 * i + 1]))
                            .collect();
                    }
                    done[f] = primitives::multilinear::poly_eval(&own[f], chi);
                }
            }
        }

        // The claims: each circuit's fully folded tables.
        for (f, ([a, b, c], claim)) in tables.iter().zip(&claims).enumerate() {
            assert_eq!(vs.next_scalars(3).unwrap(), [a[0], b[0], c[0]], "circuit {f}");
            assert_eq!(
                [claim.a_eval, claim.b_eval, claim.c_eval],
                [a[0], b[0], c[0]],
                "circuit {f}"
            );
        }
        vs.finish().unwrap();
    }

    #[test]
    fn an_identical_tail_changes_no_word() {
        // Invariant: telling the prover of an identical tail of blocks changes no word of the proof.
        //
        // Fixture state, (m, k_log, useful bits):
        //
        //     (23, 14, 16000)   BLAKE2s blocks, deep enough for table passes folding one and two challenges
        //     (21, 9, 400)      blocks smaller than a round-1 window
        //     (19, 13, 7000)    blocks the size of a window
        //
        // The tails start at a block, inside a kernel's step or task, past every step, and at block 0.
        let shapes = [(23usize, 14usize, 16_000usize), (21, 9, 400), (19, 13, 7_000)];
        let mut rng = Rng::new(0x7A11_5EED);
        for (trial, frac) in [(0, 0.27), (1, 0.6), (2, 1.0 - 1e-9), (3, 0.0), (4, 0.51)] {
            let lives: Vec<usize> = (shapes.iter())
                .map(|&(m, k_log, _)| ((frac * (1usize << (m - k_log)) as f64) as usize) | usize::from(trial == 4))
                .collect();
            let witnesses: Vec<[Vec<u8>; 2]> = (shapes.iter().zip(&lives))
                .map(|(&(m, k_log, useful), &live)| {
                    // Live blocks are random; every block from `live` on is one padding block.
                    let block = 1usize << k_log;
                    let pad = [rng.bits(block), rng.bits(block)];
                    std::array::from_fn(|w| {
                        let bits: Vec<bool> = (0..1usize << m)
                            .map(|i| {
                                let (blk, off) = (i / block, i % block);
                                let bit = if blk < live { rng.bit() } else { pad[w][off] };
                                off < useful && bit
                            })
                            .collect();
                        pack_bits(&bits)
                    })
                })
                .collect();
            let run = |tail: bool| {
                let inputs: Vec<ZerocheckInput<'_>> = (shapes.iter().zip(&lives).zip(&witnesses))
                    .map(|((&(m, k_log, useful), &live), [a, b])| ZerocheckInput {
                        bits: PackedWitness { a, b },
                        m,
                        padding: Padding {
                            k_log,
                            useful_bits: useful,
                            live_blocks: if tail { live } else { usize::MAX },
                        },
                    })
                    .collect();
                let mut ps = ProverState::from_label(LABEL);
                let claims = prove(&inputs, &mut ps);
                (claims, ps.into_proof().stream)
            };
            assert_eq!(run(true), run(false), "trial {trial}, live {lives:?}");
        }
    }

    #[test]
    fn the_first_round_is_the_whole_windows_interpolant() {
        // Invariant: the first round, known on Lambda and zero on S, is the whole window's interpolant.
        //
        // Fixture state: every domain size, random values on Lambda, four random points each.
        let mut rng = Rng::new(0x0C0B_14ED);
        for k_skip in 0..8 {
            let domain = SkipDomain::new(k_skip);
            let values = rng.ext_vec(domain.size());
            for z in rng.ext_vec(4) {
                // The window's Lagrange weights at `z`, zero on S, so only Lambda's half counts.
                let window = skip_lagrange_weights(k_skip + 1, z)[domain.size()..]
                    .iter()
                    .zip(&values)
                    .fold(F192::ZERO, |acc, (&w, &v)| acc + w * v);
                let vanishing = domain.vanishing(&mut Native, z);
                assert_eq!(
                    domain.first_round_at(&mut Native, z, vanishing, &values),
                    window,
                    "k_skip {k_skip}"
                );
            }
        }
    }

    #[test]
    fn the_lagrange_sum_is_the_skip_domains() {
        // Invariant: the vanishing polynomial and the Lagrange sum over S are the domain's, by their definitions.
        //
        // Fixture state: every domain size, four random points each.
        let mut rng = Rng::new(0x5_1EB);
        for k_skip in 0..8 {
            let domain = SkipDomain::new(k_skip);
            let values = rng.ext_vec(domain.size());
            for z in rng.ext_vec(4) {
                // `V_S(z)` as the product over the nodes.
                let vanishing = (PHI_8_TABLE_192[..domain.size()].iter()).fold(F192::ONE, |acc, &s| acc * (z + s));
                assert_eq!(domain.vanishing(&mut Native, z), vanishing, "k_skip {k_skip}");
                let lagrange = (skip_lagrange_weights(k_skip, z).iter().zip(&values))
                    .fold(F192::ZERO, |acc, (&w, &v)| acc + w * v);
                assert_eq!(
                    domain.lagrange_at(&mut Native, z, vanishing, &values),
                    lagrange,
                    "k_skip {k_skip}"
                );
            }
        }
    }

    fn rand_vec(rng: &mut Rng, n: usize) -> Vec<F8> {
        (0..n).map(|_| F8((rng.next_u64() & 0xff) as u8)).collect()
    }

    #[test]
    fn forward_inverse_roundtrip() {
        let mut rng = Rng::new(42);
        for k in 1..=7 {
            let ntt = AdditiveNttGf8::new(k, F8::ZERO);
            for _ in 0..8 {
                let original = rand_vec(&mut rng, 1 << k);
                let mut v = original.clone();
                ntt.forward(&mut v);
                ntt.inverse(&mut v);
                assert_eq!(v, original, "roundtrip failed at k={k}");
            }
        }
    }

    #[test]
    fn nonzero_beta_roundtrip() {
        let mut rng = Rng::new(45);
        for beta_v in [0x01u8, 0x42, 0xCA, 0xFF] {
            let beta = F8(beta_v);
            for k in 1..=6 {
                let ntt = AdditiveNttGf8::new(k, beta);
                let original = rand_vec(&mut rng, 1 << k);
                let mut v = original.clone();
                ntt.forward(&mut v);
                ntt.inverse(&mut v);
                assert_eq!(v, original, "beta={beta_v:#x}, k={k}");
            }
        }
    }

    /// Naive reference: unpack `bytes` into `ell` GF(2)-valued F8 elements
    /// (one per coefficient bit), apply inv_NTT_S, then fwd_NTT_Λ.
    fn naive_apply(ntt_s: &AdditiveNttGf8, ntt_l: &AdditiveNttGf8, bytes: &[u8]) -> Vec<F8> {
        let ell = 1usize << ntt_s.k();
        assert_eq!(bytes.len(), ell / 8);
        let mut v = vec![F8::ZERO; ell];
        for (b, &byte) in bytes.iter().enumerate() {
            for t in 0..8 {
                if (byte >> t) & 1 != 0 {
                    v[8 * b + t] = F8::ONE;
                }
            }
        }
        ntt_s.inverse(&mut v);
        ntt_l.forward(&mut v);
        v
    }

    #[test]
    fn matches_naive() {
        for k in [3usize, 4, 6] {
            let ntt_s = AdditiveNttGf8::new(k, F8::ZERO);
            let ntt_l = AdditiveNttGf8::new(k, F8(1 << k));
            let table = InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l);
            let mut rng = Rng::new(100 + k as u64);
            let mut out = vec![F8::ZERO; table.ell];
            for _ in 0..32 {
                let bytes: Vec<u8> = (0..table.n_chunks).map(|_| rng.next_u8()).collect();
                table.apply(&bytes, &mut out);
                assert_eq!(out, naive_apply(&ntt_s, &ntt_l, &bytes), "k={k}, bytes={bytes:02x?}");
            }
        }
    }

    /// The dispatched SIMD `apply` must reproduce `apply_scalar`. `ell ≥ 16` at
    /// every k here, so this exercises the vector body: k=4 (n_chunks=2,
    /// n128=1) through k=6 (n_chunks=8, n128=4, the headline protocol size).
    #[test]
    fn apply_simd_matches_apply_scalar() {
        for &k in &[4usize, 5, 6] {
            let ntt_s = AdditiveNttGf8::new(k, F8::ZERO);
            let ntt_l = AdditiveNttGf8::new(k, F8(1u8 << k));
            let table = InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l);

            let mut rng = Rng::new(100 + k as u64);
            for _ in 0..32 {
                let bytes: Vec<u8> = (0..table.n_chunks).map(|_| (rng.next_u64() & 0xff) as u8).collect();
                let mut out_scalar = vec![F8::ZERO; table.ell];
                let mut out_simd = vec![F8::ZERO; table.ell];
                table.apply_scalar(&bytes, &mut out_scalar);
                table.apply(&bytes, &mut out_simd);
                assert_eq!(
                    out_scalar, out_simd,
                    "scalar/simd apply disagree at k={k}, bytes={bytes:02x?}"
                );
                #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
                if table.ell == 64 {
                    // SAFETY: the crate is built with AVX2, and `ell` is 64.
                    unsafe { table.apply_avx2(&bytes, &mut out_simd) };
                    assert_eq!(out_scalar, out_simd, "scalar/avx2 apply disagree, bytes={bytes:02x?}");
                }
            }
        }
    }

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

    #[test]
    fn eq_mass_from_is_the_tables_suffix_sum() {
        // Invariant: the closed form is the eq table summed from `from` on, at every index of a small cube.
        let mut rng = Rng::new(0xE0_3A55);
        for n in 0..6 {
            let r = rng.ext_vec(n);
            let table = eq_table(&r);
            for from in 0..1usize << n {
                let want = table[from..].iter().fold(F192::ZERO, |acc, &e| acc + e);
                assert_eq!(eq_mass_from(&r, from), want, "n={n}, from={from}");
            }
        }
    }
}
