// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Zerocheck PIOP: prove a(y) · b(y) ⊕ c(y) = 0 for all y ∈ {0,1}^m, for a batch
//! of circuits at once.
//!
//! Inputs are three bit vectors of length 2^m per circuit. Output is, per circuit,
//! an evaluation claim on the multilinear extensions â, b̂, ĉ at one point.
//!
//! Protocol shape (k_skip = [`K_SKIP`] = 6, `n` the most variables past the skip):
//!   1. Verifier constructs `r ∈ F_{2^192}^n` from fixed inner coordinates and
//!      sampled outer coordinates, then the batching challenge `λ`.
//!   2. Prover sends `Σ_f λ^f P_f(λ')` for λ' ∈ Λ, |Λ| = 2^k_skip, each
//!      `P_f = P_f^{AB} + P_f^C`.
//!   3. Verifier samples `z ∈ F_{2^192}` (univariate-skip fold point).
//!   4. For each of the `n` multilinear rounds, prover sends the linear and
//!      quadratic coefficients; the verifier derives the constant from the claim
//!      and samples the round challenge.
//!   5. Prover sends every circuit's `(â, b̂, ĉ)`, and the verifier checks they
//!      reproduce the final claim.
//!
//! C rides the sumcheck rather than being split off at round 1, which is what
//! puts all three claims at ONE point and leaves lincheck a single family of
//! bit slices per circuit for ring switching (doc/leanvm Annex C).

use crate::zerocheck::ntt::{AdditiveNttGf8, InvNttTableByteSingleGf8};
use fiat_shamir::arith::{Native, Verifier};
use fiat_shamir::transcript::{Challenger, ProverState, TranscriptError, Transmitter};
use multilinear::{
    PackedWitness, RoundPair, bit_round_materialize, bit_round_pair, fold_and_round_pair_into, fold_in_place_pair,
    fold_in_place_single, round_pair_naive, round_single_naive,
};
use primitives::bit_fold::BitFold;
use primitives::field::{F8, F192, powers};
use primitives::multilinear::skip_lagrange_weights;
use round1::{c_s, medium_challenges, round1_shift_reduce_extract_c_packed_padded, small_challenges};
use thiserror::Error;

pub(crate) mod multilinear;
mod ntt;
pub(crate) mod round1;
mod skip_domain;

pub use skip_domain::SkipDomain;

/// Number of variables folded in round 1 via the additive-NTT univariate skip.
/// |Λ| = 2^K_SKIP = 64 elements, which is the round-1 prover message: one
/// length-64 vector of F192, the AB and C halves already summed.
pub const K_SKIP: usize = 6;
const N_INNER: usize = 7; // 3 small + 4 medium fixed-constant eq dimensions

/// The fewest variables a zerocheck's cube can have: the univariate skip plus the fixed-constant dimensions.
pub const MIN_LOG_N: usize = K_SKIP + N_INNER;

/// Passes over the packed bits, two rounds each, before the folded tables are stored.
///
/// - A pass re-reads the `a` and `b` bit tables, `2 * 2^m` bits; it derives `c = a AND b`.
/// - Storing at level `t` writes three F192 tables, `3 * 192 * 2^(m - 6 - t)` bits, then reads them back.
/// - On x86 a pass is bandwidth-bound with GFNI, and the AVX2 nibble lookups keep it cheap enough for the same choice.
/// - So storing pays once the tables are well below the bits: level 4, after two passes.
/// - On aarch64 the byte-table fold is compute-bound, its tables growing with the level.
/// - There a pass costs more than the stored tables' traffic: store at once.
const PAIR_PASSES: usize = if cfg!(target_arch = "aarch64") { 0 } else { 2 };

/// Smallest folded table a paired table pass takes.
///
/// Below it the tables fit L1, and one round at a time on this thread beats a parallel dispatch.
const PAIRED_MIN: usize = 1 << 10;

/// Build the equality coordinates that remain after the univariate skip.
fn equality_tail(m: usize, mut sample_vec: impl FnMut(usize) -> Vec<F192>) -> Vec<F192> {
    let outer = sample_vec(m - K_SKIP - N_INNER);
    small_challenges()
        .into_iter()
        .chain(medium_challenges())
        .chain(outer)
        .collect()
}

/// Where the zero padding of a batched witness lies, so the zerocheck can skip it.
///
/// The witness is `2^(m - k_log)` blocks of `2^k_log` bits.
///
/// Each block holds its data first and zero padding after it.
///
/// A chunk of zero bits adds nothing to a round message, so skipping it leaves the output unchanged.
#[derive(Clone, Copy, Debug)]
pub(crate) struct PaddingSpec {
    /// Log of the bits in one block.
    pub k_log: usize,
    /// Bits at the start of each block that carry data; the rest are zero.
    pub(crate) useful_bits_per_block: usize,
}

/// Evaluation claims on the multilinear extensions of a, b, c, all three at the
/// **same** point `(z, mlv_challenges)`: C rides the sumcheck with AB, so the
/// three claims share the point its challenges define, and lincheck can batch
/// them into one reduction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ZerocheckClaim {
    /// Univariate-skip challenge sampled after round 1 (binds the K_SKIP
    /// skip variables), represented directly in `F192`.
    pub z: F192,
    /// Sumcheck bind challenges, the batch's first `m - K_SKIP`.
    pub mlv_challenges: Vec<F192>,
    /// `â(z, mlv_challenges)`.
    pub(crate) a_eval: F192,
    /// `b̂(z, mlv_challenges)`.
    pub(crate) b_eval: F192,
    /// `ĉ(z, mlv_challenges)`. The batch's terminal identity ties it to the other
    /// claims, and lincheck's α-batched identity pins all three.
    pub(crate) c_eval: F192,
}

/// Why the zerocheck verifier rejects.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum ZerocheckError {
    /// Fewer variables than the univariate skip takes.
    #[error("log_n {log_n} is below k_skip {k_skip}")]
    LogNTooSmall { log_n: usize, k_skip: usize },
    /// The circuits' claims do not reproduce the sumcheck's final claim.
    #[error("the circuits' claims do not reproduce the zerocheck's final claim")]
    TerminalMismatch,
    /// The proof stream is malformed.
    #[error(transparent)]
    Transcript(#[from] TranscriptError),
}

/// One circuit's witness in a batched zerocheck: the packed `a`, `b`, `c` bits over
/// a cube of `2^m` bits.
///
/// Only round 1 reads `c`: the later passes derive `c = a AND b`, which an honest witness satisfies.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ZerocheckInput<'a> {
    pub bits: PackedWitness<'a>,
    pub c: &'a [u8],
    pub m: usize,
    pub padding: PaddingSpec,
}

/// The folded tables of one circuit, from the round that stores them on.
///
/// The tables stay behind the rounds: `pending` holds the challenges sent but not yet folded in, lowest first.
///
/// ```text
/// paired pass:   fold the pending challenges, then send two rounds from each quad of folded values
/// single round:  fold the pending challenges one at a time, then send one round
/// ```
///
/// A paired pass reads the tables once and writes a quarter of them for two rounds.
/// A single round covers the last round, and a round whose eq challenge is 1, which leaves G(0) to send.
struct Tables {
    t: [Vec<F192>; 3],
    /// Ping-pong scratch: a pass writes its folded tables into the spare capacity here, then the two swap.
    nxt: [Vec<F192>; 3],
    pending: Vec<F192>,
}

impl Tables {
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
/// bits of a, b       1 bit per slot, 2 * 2^m bits in all; c = a AND b is derived, not read
/// one F192 table     192 bits per slot, 2^(m - 6 - t) slots each
/// ```
///
/// While the tables would be larger than the bits, re-reading the bits is the cheaper pass.
/// Each such pass sends two rounds; the second waits on the first's challenge.
/// A last single-round pass stores the three folded tables for the tail.
///
/// The kernels take the eq challenges of the variables they do not bind.
/// They return the bare `(G(1), G(inf))`, from which [`Self::round`] makes the coefficients.
struct CircuitProver<'a> {
    bits: PackedWitness<'a>,
    padding: PaddingSpec,
    /// The eq challenges of this circuit's variables past the skip.
    r: &'a [F192],
    lagrange: Vec<F192>,
    chis: Vec<F192>,
    /// The running claim, `G` of the last round at its challenge.
    claim: F192,
    /// The round message just sent, as coefficients.
    message: [F192; 3],
    /// The rounds sent from the packed bits in pairs, before the tables are stored: the first [`PAIR_PASSES`] pairs that leave a round after them.
    paired_bit_rounds: usize,
    /// The second round of a paired pass, waiting on the first's challenge.
    pair: Option<RoundPair>,
    tables: Option<Tables>,
}

impl<'a> CircuitProver<'a> {
    /// The prover and its round-1 message: `P` on the coset, `P^{AB}` and `P^C` summed.
    fn new(input: &ZerocheckInput<'a>, r: &'a [F192], inv_table: &InvNttTableByteSingleGf8) -> (Self, Vec<F192>) {
        let ZerocheckInput { bits, c, m, padding } = *input;
        assert!(m >= MIN_LOG_N, "prove requires m >= k_skip + N_INNER (= {MIN_LOG_N})");
        let cube_bytes = (1usize << m) / 8;
        assert_eq!(bits.a.len(), cube_bytes);
        assert_eq!(bits.b.len(), cube_bytes);
        assert_eq!(c.len(), cube_bytes);
        let n_mlv = m - K_SKIP;
        assert_eq!(r.len(), n_mlv);

        // The optimized URM drops a `C_s = φ_8(0x1C)` scalar from its accumulators
        // (a prover-side optimization tied to the small-eq trick: see the
        // C_s factor analysis in `round1`). The wire format
        // must be in "naive" convention so the verifier doesn't need to know
        // about this internal optimization; we restore the C_s factor here.
        let (ab, c) = round1_shift_reduce_extract_c_packed_padded(bits.a, bits.b, c, m, r, inv_table, &padding);
        let c_s = c_s();
        let round1 = ab.iter().zip(&c).map(|(x, y)| c_s * (*x + *y)).collect();
        let prover = Self {
            bits,
            padding,
            r,
            lagrange: Vec::new(),
            chis: Vec::with_capacity(n_mlv),
            claim: F192::ZERO,
            message: [F192::ZERO; 3],
            paired_bit_rounds: 2 * (0..(n_mlv - 1) / 2).take(PAIR_PASSES).count(),
            pair: None,
            tables: None,
        };
        (prover, round1)
    }

    const fn n_mlv(&self) -> usize {
        self.r.len()
    }

    /// Take the univariate-skip challenge: the running claim is this circuit's `P(z)`.
    fn start(&mut self, z: F192, round1: &[F192]) {
        self.lagrange = skip_lagrange_weights(K_SKIP, z);
        let vanishing = SkipDomain::FLOCK.vanishing(&mut Native, z);
        self.claim = SkipDomain::FLOCK.first_round_at(&mut Native, z, vanishing, round1);
    }

    /// The next round's coefficients. `G(0)` comes from the eq split
    /// `(1 + r_eq)·G(0) + r_eq·G(1) = claim`, which leaves it free at `r_eq = 1`: then
    /// the round computes it, and only the table rounds can meet that, the earlier
    /// ones running on fixed challenges.
    fn round(&mut self) -> [F192; 3] {
        let j = self.chis.len();
        let r_eq = self.r[j];
        let (g0, g1, g_inf) = if let Some(pair) = self.pair.take() {
            let (g1, g_inf) = pair.second(self.chis[j - 1]);
            (None, g1, g_inf)
        } else if self.tables.is_none() {
            self.bit_round(j)
        } else {
            self.table_round(j)
        };
        let g0 = g0.unwrap_or_else(|| (self.claim + r_eq * g1) * (F192::ONE + r_eq).inv());
        // G(X) = G(0)·(1+X) + G(1)·X + G(inf)·X·(1+X).
        self.message = [g0, g0 + g1 + g_inf, g_inf];
        self.message
    }

    /// Bind the round just sent at `chi`.
    fn bind(&mut self, chi: F192) {
        self.claim = primitives::multilinear::poly_eval(&self.message, chi);
        self.chis.push(chi);
        if let Some(tables) = &mut self.tables {
            tables.pending.push(chi);
        }
    }

    /// A round straight from the packed bits: the first of a pair, or the one that stores the tables.
    fn bit_round(&mut self, j: usize) -> (Option<F192>, F192, F192) {
        let (bits, padding, r) = (self.bits, self.padding, self.r);
        let fold = BitFold::at_level(&self.lagrange, &self.chis);
        if j < self.paired_bit_rounds {
            let pair = bit_round_pair(bits, &fold, &r[j + 1..], &padding);
            self.pair = Some(pair);
            return (None, pair.first.0, pair.first.1);
        }
        let ((g1, g_inf), [a, b, c]) = bit_round_materialize(bits, &fold, &r[j + 1..], &padding);
        let room = a.len() / 2;
        let nxt = std::array::from_fn(|_| Vec::with_capacity(room));
        self.tables = Some(Tables {
            t: [a, b, c],
            nxt,
            pending: Vec::with_capacity(2),
        });
        (None, g1, g_inf)
    }

    /// A round on the stored tables: the first of a paired pass, or a single round.
    fn table_round(&mut self, j: usize) -> (Option<F192>, F192, F192) {
        let r = self.r;
        let n_mlv = r.len();
        let tb = self.tables.as_mut().expect("the tables are stored");

        // The tables' length once the pending challenges are folded in.
        let n_out = tb.t[0].len() >> tb.pending.len();
        let paired = j + 1 < n_mlv && n_out >= PAIRED_MIN && r[j] != F192::ONE && r[j + 1] != F192::ONE;
        if paired {
            let [a, b, c] = &tb.t;
            let outs = tb.nxt.each_mut().map(|t| {
                t.clear();
                &mut t.spare_capacity_mut()[..n_out]
            });
            let pair = fold_and_round_pair_into([a, b, c], outs, &tb.pending, &r[j + 1..]);
            // SAFETY: the pass wrote the first `n_out` slots of each table.
            unsafe { tb.swap_in(n_out) };
            tb.pending.clear();
            self.pair = Some(pair);
            return (None, pair.first.0, pair.first.1);
        }
        let [a, b, c] = &mut tb.t;
        for &rho in &tb.pending {
            fold_in_place_pair(a, b, rho);
            fold_in_place_single(c, rho);
        }
        tb.pending.clear();
        // The eq weights of the variables this round does not bind.
        let r_eq = &r[j + 1..];
        let (m1, mi) = round_pair_naive(a, b, r_eq);
        let m1 = m1 + round_single_naive(c, r_eq);
        let g0 = (r[j] == F192::ONE).then(|| {
            // happens only with probability 2^(-192). We keep it for completeness, but not strictly necessary in the real world
            let eq = primitives::multilinear::eq_table(r_eq);
            (0..eq.len()).fold(F192::ZERO, |acc, x| acc + eq[x] * (a[2 * x] * b[2 * x] + c[2 * x]))
        });
        (g0, m1, mi)
    }

    /// The three claims, once every round is bound.
    ///
    /// Only a and b are bound: ĉ comes from the terminal identity, so `c`'s last fold
    /// would be work for a value nobody reads. Deriving it rather than reading the
    /// table is what keeps the claims the ones the transcript implies on a DISHONEST
    /// witness too: the running claim descends from the round-1 message, whose
    /// reconstruction assumes the zeros on the skip domain.
    fn finish(self) -> (F192, F192, F192) {
        let claim = self.claim;
        let mut tb = self.tables.expect("every circuit stores its tables");
        let [a, b, _] = &mut tb.t;
        for &rho in &tb.pending {
            fold_in_place_pair(a, b, rho);
        }
        debug_assert_eq!(a.len(), 1);
        debug_assert_eq!(b.len(), 1);
        (a[0], b[0], claim + a[0] * b[0])
    }
}

/// THE zerocheck prover: proves `a·b ⊕ c = 0` for every circuit of a batch at once,
/// leaving each circuit's `(â, b̂, ĉ)` claimed at one point for lincheck to batch.
///
/// The circuits share every challenge (doc/leanvm Annex C, "Batching the circuits").
/// Their eq point is one vector `r`, circuit `f` of `n_f` variables past the skip
/// taking its first `n_f` coordinates, and the batch is the sum of the circuits'
/// polynomials times the powers of one challenge `λ`, each lifted onto the batch's
/// variables by summing it over those it does not use, where its eq factor sums to
/// one. So the round-1 message is the `λ`-combination of the circuits', the rounds
/// bind the lowest variable first, every circuit from the first round, and circuit
/// `f` is done after its `n_f` rounds: from then on it adds the constant `G` it
/// ended on, which reaches only the coefficient the claim fixes. Each circuit's
/// claims sit at the batch's challenges' first `n_f`.
pub(crate) fn prove(inputs: &[ZerocheckInput<'_>], ps: &mut ProverState) -> Vec<ZerocheckClaim> {
    let n_mlv = inputs.iter().map(|i| i.m).max().expect("a batch has a circuit") - K_SKIP;

    // r_rest layout:
    //   r_rest[0..3]               : protocol small-eq constants φ_8(0xF7..)
    //   r_rest[3..7]               : protocol medium-eq constants β_i
    //   r_rest[7..n_mlv]           : sampled outer equality coordinates
    // Prover and verifier use the same tower-valued challenges directly.
    let r_rest = equality_tail(n_mlv + K_SKIP, |n| ps.sample_vec(n));
    let lambdas = powers(ps.sample(), inputs.len());

    let span = tracing::info_span!("Round 1").entered();
    let ntt_s = AdditiveNttGf8::new(K_SKIP, F8::ZERO);
    let ntt_l = AdditiveNttGf8::new(K_SKIP, F8(1u8 << K_SKIP));
    let inv_table = InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l);
    let mut round1 = vec![F192::ZERO; 1 << K_SKIP];
    let provers: Vec<_> = (inputs.iter().zip(&lambdas))
        .map(|(input, &lambda)| {
            let (prover, own) = CircuitProver::new(input, &r_rest[..input.m - K_SKIP], &inv_table);
            for (x, y) in round1.iter_mut().zip(&own) {
                *x += lambda * *y;
            }
            (prover, own)
        })
        .collect();
    drop(span);
    ps.add_scalars(&round1);
    let z = ps.sample();
    let mut provers: Vec<CircuitProver<'_>> = (provers.into_iter())
        .map(|(mut prover, own)| {
            prover.start(z, &own);
            prover
        })
        .collect();

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

    // The claims ride the stream before the next challenge, lincheck's α, which
    // batches them: drawn after them, it cannot be steered by them.
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

/// What the batched zerocheck's replay leaves: its point, and each circuit's three evaluations, which the lincheck batches.
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
/// Walks the transcript in lockstep with the prover, samples the same challenges,
/// and carries the running claim through the rounds, then checks the terminal
/// identity `claim = Σ_f λ^f (â_f·b̂_f + ĉ_f)` on the claims read. Nothing else is
/// checked here: what makes the claims meaningful is lincheck, which pins every
/// circuit's three against its committed witness. Never call this alone and treat
/// `Ok` as acceptance.
///
/// The round-1 message is known on `Λ` and, by the zerocheck identity, zero on `S`.
/// Those `2·2^k_skip` values fix a polynomial of lower degree, which the running claim interpolates at `z`.
/// A dishonest witness breaks the zeros on `S`, and the chain ends at claims lincheck's α-batched identity rejects.
///
/// The running claim is the inner polynomial `G` at the round's challenge.
/// The next round's split `G_{r-1}(ρ) = (1 + r_eq)·G_r(0) + r_eq·G_r(1)` absorbs the eq factor of the variable just bound.
pub(crate) fn verify<V: Verifier>(log_ns: &[usize], v: &mut V) -> Result<ZerocheckReplay<V::E>, ZerocheckError> {
    if let Some(&log_n) = log_ns.iter().find(|&&m| m < MIN_LOG_N) {
        return Err(ZerocheckError::LogNTooSmall { log_n, k_skip: K_SKIP });
    }
    let m = log_ns.iter().copied().max().expect("a batch has a circuit");

    // The equality tail: the fixed inner coordinates, then the sampled outer ones; then the batching challenge.
    let outer = v.sample_vec(m - MIN_LOG_N);
    let lambda = v.sample();
    let lambdas = v.powers(lambda, log_ns.len());
    let fixed: Vec<V::E> = (small_challenges().into_iter().chain(medium_challenges()))
        .map(|c| v.constant(c))
        .collect();

    let domain = SkipDomain::FLOCK;
    let round1 = v.next_scalars(domain.size())?;
    let z = v.sample();
    let vanishing = domain.vanishing(v, z);
    let mut c_running = domain.first_round_at(v, z, vanishing, &round1);

    let mut mlv_challenges = Vec::with_capacity(m - K_SKIP);
    for &r_eq in fixed.iter().chain(&outer) {
        let g = v.next_round_poly(3, c_running, Some(r_eq))?;
        let chi = v.sample();
        mlv_challenges.push(chi);
        c_running = v.poly_eval(&g, chi);
    }

    // The terminal identity: the running claim is `sum_f lambda^f (a_f b_f + c_f)`.
    // A circuit done early carried its value unchanged since.
    let mut terminal = v.zero();
    let mut evals = Vec::with_capacity(log_ns.len());
    for &weight in &lambdas {
        let [a, b, c] = [v.next_scalar()?, v.next_scalar()?, v.next_scalar()?];
        let value = v.mul_add(a, b, c);
        terminal = v.mul_add(weight, value, terminal);
        evals.push([a, b, c]);
    }
    v.ensure_eq(terminal, c_running, || ZerocheckError::TerminalMismatch)?;
    Ok(ZerocheckReplay {
        z,
        vanishing,
        mlv_challenges,
        evals,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use fiat_shamir::transcript::VerifierState;
    use primitives::test_util::Rng;
    use round1::tests::pack_bits;

    impl PaddingSpec {
        // Every bit useful.
        pub(crate) const fn dense(m: usize) -> Self {
            Self {
                k_log: m,
                useful_bits_per_block: 1usize << m,
            }
        }
    }

    /// Test shim: one dense circuit.
    fn prove_packed(
        a_packed: &[u8],
        b_packed: &[u8],
        c_packed: &[u8],
        m: usize,
        ps: &mut ProverState,
    ) -> ZerocheckClaim {
        let input = ZerocheckInput {
            bits: PackedWitness {
                a: a_packed,
                b: b_packed,
            },
            c: c_packed,
            m,
            padding: PaddingSpec::dense(m),
        };
        prove(&[input], ps).pop().expect("one circuit")
    }

    /// Test shim: the replay of one circuit.
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

    /// The quirky evaluation `f̂(z, chi)` of a Boolean witness: the φ8-Lagrange
    /// combination, at `z`, of the multilinear extensions of its 2^K_SKIP bit
    /// slices. This is what the three zerocheck claims are supposed to be.
    fn quirky_eval(bits: &[bool], z: F192, chi: &[F192]) -> F192 {
        let ell = 1usize << K_SKIP;
        let weights = primitives::multilinear::skip_lagrange_weights(K_SKIP, z);
        let eq = primitives::multilinear::eq_table(chi);
        let mut acc = F192::ZERO;
        for (v, &e) in eq.iter().enumerate() {
            for (i, &w) in weights.iter().enumerate() {
                if bits[v * ell + i] {
                    acc += e * w;
                }
            }
        }
        acc
    }

    /// Pack three Boolean vectors into the (a_packed, b_packed, c_packed)
    /// shape that `prove_packed` consumes.
    fn pack_abc(a: &[bool], b: &[bool], c: &[bool]) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
        (pack_bits(a), pack_bits(b), pack_bits(c))
    }

    /// `prove` runs end-to-end at the smallest valid m (= k_skip + N_INNER = 13)
    /// without panicking, and produces output of the right shape.
    ///
    /// structural sanity here catches:
    ///   - mismatched observe/sample sequence
    ///   - wrong slice lengths in the eq-challenge tail at any round
    ///   - any unreachable assert in the underlying functions
    #[test]
    fn prove_runs_end_to_end() {
        for &m in &[13usize, 14, 15, 16] {
            let mut rng = Rng::new(m as u64);
            let a = rng.bits(1 << m);
            let b = rng.bits(1 << m);
            // Honest witness: c = a AND b, so a·b ⊕ c = 0 on the hypercube.
            let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();

            let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
            let mut ps = ProverState::from_label(b"flock-test-v0");
            let claim = prove_packed(&a_p, &b_p, &c_p, m, &mut ps);

            // Shape checks: the streamed proof is round1 ‖ (m − K_SKIP)
            // message pairs ‖ (final_a, final_b, final_c). C rides the sumcheck,
            // so there is no second Λ-vector.
            let stream = ps.into_proof().stream;
            assert_eq!(stream.len(), (1 << K_SKIP) + 2 * (m - K_SKIP) + 3, "m={m}");
            assert_eq!(claim.mlv_challenges.len(), m - K_SKIP, "m={m}");
            assert_eq!(claim.a_eval, stream[stream.len() - 3], "m={m}");
            assert_eq!(claim.b_eval, stream[stream.len() - 2], "m={m}");
            assert_eq!(claim.c_eval, stream[stream.len() - 1], "m={m}");
        }
    }

    /// **Prove→verify roundtrip**: an honest proof verifies cleanly, and the
    /// claim returned by `verify` is byte-for-byte equal to the claim returned
    /// by `prove`.
    #[test]
    fn prove_verify_roundtrip_honest() {
        for &m in &[13usize, 14, 15, 16] {
            let mut rng = Rng::new(1000 + m as u64);
            let a = rng.bits(1 << m);
            let b = rng.bits(1 << m);
            let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();

            let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
            let mut ch_prove = ProverState::from_label(b"flock-test-v0");
            let claim_p = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);

            let proof_t = ch_prove.into_proof();
            let mut ch_verify = VerifierState::from_label(b"flock-test-v0", &proof_t);
            let result = verify_one(m, &mut ch_verify);
            let claim_v = result.unwrap_or_else(|e| panic!("verify rejected at m={m}: {e:?}"));

            assert_eq!(claim_p, claim_v, "claim mismatch at m={m}");
        }
    }

    /// **The reduction is faithful.** On an honest witness the three claims
    /// the verifier ends up with are the true quirky evaluations of a, b and c
    /// at the sumcheck point.
    #[test]
    fn claims_are_true_evaluations() {
        // 16 and 17 reach the fused single-table kernel (gated on log_n ≥ 10),
        // which the smaller sizes never touch.
        for &m in &[13usize, 14, 15, 16, 17] {
            let mut rng = Rng::new(2024 + m as u64);
            let a = rng.bits(1 << m);
            let b = rng.bits(1 << m);
            let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();

            let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
            let mut ch_prove = ProverState::from_label(b"flock-test-v0");
            let _ = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);
            let proof_t = ch_prove.into_proof();
            let mut ch = VerifierState::from_label(b"flock-test-v0", &proof_t);
            let claim = verify_one(m, &mut ch).expect("honest proof");

            let chi = &claim.mlv_challenges;
            assert_eq!(claim.a_eval, quirky_eval(&a, claim.z, chi), "â at m={m}");
            assert_eq!(claim.b_eval, quirky_eval(&b, claim.z, chi), "b̂ at m={m}");
            assert_eq!(claim.c_eval, quirky_eval(&c, claim.z, chi), "ĉ at m={m}");
        }
    }

    /// **AUDIT: a false statement leaves a wrong claim.** The zerocheck does
    /// not reject a false statement on its own: an honest-shaped run on a
    /// witness violating `a·b ⊕ c = 0` passes the terminal identity, and is
    /// caught by lincheck, which pins all three claims against the committed
    /// witness. What must hold at this layer is that such a witness cannot
    /// leave all three claims true. A tampered proof word is either rejected by
    /// the terminal identity or moves a claim off the true evaluations.
    #[test]
    fn false_statement_or_tamper_leaves_a_wrong_claim() {
        for &m in &[13usize, 14, 15] {
            for seed in 0..20u64 {
                let mut rng = Rng::new(0xBADC0DE ^ seed ^ ((m as u64) << 32));
                let a = rng.bits(1 << m);
                let b = rng.bits(1 << m);
                let mut c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
                // Flip a random number of bits (1..=4): the statement is now false.
                let nflip = 1 + (rng.next_u64() as usize % 4);
                for _ in 0..nflip {
                    let idx = rng.next_u64() as usize % c.len();
                    c[idx] = !c[idx];
                }
                let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
                let mut ch_prove = ProverState::from_label(b"flock-test-v0");
                let _ = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);
                let proof_t = ch_prove.into_proof();
                let mut ch = VerifierState::from_label(b"flock-test-v0", &proof_t);
                let claim = verify_one(m, &mut ch).expect("shape is still valid");
                let chi = &claim.mlv_challenges;
                let all_true = claim.a_eval == quirky_eval(&a, claim.z, chi)
                    && claim.b_eval == quirky_eval(&b, claim.z, chi)
                    && claim.c_eval == quirky_eval(&c, claim.z, chi);
                assert!(!all_true, "false statement (m={m}, seed={seed}) left every claim true");
            }
        }

        // Every region of an honest proof: one flipped word must move a claim.
        let m = 14;
        let mut rng = Rng::new(5050);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
        let mut ch_prove = ProverState::from_label(b"flock-test-v0");
        let _ = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);
        let proof_t = ch_prove.into_proof();

        let ell = 1usize << K_SKIP;
        let n_mlv = m - K_SKIP;
        let mutations: [(&str, usize); 7] = [
            ("round1[0]", 0),
            ("round1[5]", 5),
            ("multilinear_rounds[0].0", ell),
            ("multilinear_rounds[mid].1", ell + 2 * (n_mlv / 2) + 1),
            ("final_a_eval", ell + 2 * n_mlv),
            ("final_b_eval", ell + 2 * n_mlv + 1),
            ("final_c_eval", ell + 2 * n_mlv + 2),
        ];
        for (label, word) in mutations {
            let mut bad = proof_t.clone();
            bad.stream[word].c0 ^= 1;
            let mut ch = VerifierState::from_label(b"flock-test-v0", &bad);
            match verify_one(m, &mut ch) {
                Err(ZerocheckError::TerminalMismatch) => {}
                Err(e) => panic!("tampered proof ({label}) failed on its shape: {e:?}"),
                Ok(claim) => {
                    let chi = &claim.mlv_challenges;
                    let all_true = claim.a_eval == quirky_eval(&a, claim.z, chi)
                        && claim.b_eval == quirky_eval(&b, claim.z, chi)
                        && claim.c_eval == quirky_eval(&c, claim.z, chi);
                    assert!(!all_true, "tampered proof ({label}) left every claim true");
                }
            }
        }
    }

    /// Shape rejections: a truncated stream and a too-small instance.
    #[test]
    fn verify_rejects_shape_errors() {
        let m = 14;
        let mut rng = Rng::new(606);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
        let mut ch_prove = ProverState::from_label(b"flock-test-v0");
        let _ = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);
        let proof_t = ch_prove.into_proof();

        // Truncated stream: a clean Transcript error, not a panic.
        let mut bad = proof_t.clone();
        bad.stream.truncate(bad.stream.len() - 3);
        let mut ch = VerifierState::from_label(b"flock-test-v0", &bad);
        assert!(matches!(verify_one(m, &mut ch), Err(ZerocheckError::Transcript(_))));

        // log_n too small.
        let mut ch = VerifierState::from_label(b"flock-test-v0", &proof_t);
        assert!(matches!(
            verify_one(K_SKIP + 6, &mut ch),
            Err(ZerocheckError::LogNTooSmall { .. })
        ));
    }

    /// AUDIT (Fiat-Shamir binding of the final â, b̂ claims). Regression test
    /// for the gap where `final_a_eval`/`final_b_eval` were not observed into
    /// the transcript.
    ///
    /// Downstream, lincheck reduces the three claims via a *single* random-
    /// linear-combination check in powers of α. That batching is only sound if
    /// α is sampled *after* the claims are bound: otherwise a prover that
    /// already knows α can pick them to satisfy the one batched equation while
    /// violating the individual ties.
    ///
    /// The tamper here is *product-preserving*, `(â, b̂) → (â·t, b̂·t⁻¹)`, so it
    /// leaves `â·b̂`, hence the terminal identity, untouched: the whole triple
    /// the reduction carries is as consistent as the honest one, and nothing
    /// downstream could tell the two runs apart except the transcript itself.
    /// The defense is that the claims are observed last, so the next challenge
    /// (the slot lincheck draws α from) must diverge.
    #[test]
    fn audit_final_ab_claims_bound_to_transcript() {
        let m = 14;
        let mut rng = Rng::new(0xF1A7_5A11);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);

        let mut ch_prove = ProverState::from_label(b"flock-test-v0");
        let claim_p = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);
        let proof_t = ch_prove.into_proof();

        // Honest verify, then capture the next challenge the transcript feeds
        // downstream: this is exactly the slot lincheck samples α from.
        let mut ch_honest = VerifierState::from_label(b"flock-test-v0", &proof_t);
        assert!(verify_one(m, &mut ch_honest).is_ok(), "honest verify rejected");
        let alpha_honest = Challenger::sample(&mut ch_honest);

        // Product-preserving tamper: â' = â·t, b̂' = b̂·t⁻¹ ⇒ â'·b̂' = â·b̂.
        let t = F192::new(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 0x55aa_aa55_0123_4567);
        assert!(t != F192::ZERO && t != F192::ONE, "t must be nontrivial");
        // The finals are the LAST three stream words of this standalone proof, `ĉ` last.
        let n = proof_t.stream.len();
        let mut bad = proof_t.clone();
        bad.stream[n - 3] *= t;
        bad.stream[n - 2] *= t.inv();
        assert_ne!(bad.stream[n - 3], proof_t.stream[n - 3], "tamper must change â");
        assert_ne!(bad.stream[n - 2], proof_t.stream[n - 2], "tamper must change b̂");
        assert_eq!(
            bad.stream[n - 3] * bad.stream[n - 2],
            claim_p.a_eval * claim_p.b_eval,
            "tamper must preserve the product",
        );

        // Replay the tampered proof to move the transcript to the same slot. Its
        // claims are as consistent as the honest ones (same product, same ĉ),
        // so nothing local distinguishes them.
        let mut ch_tampered = VerifierState::from_label(b"flock-test-v0", &bad);
        let tampered = verify_one(m, &mut ch_tampered).expect("the terminal identity still holds");
        assert_eq!(tampered.c_eval, claim_p.c_eval, "ĉ is untouched");
        let alpha_tampered = Challenger::sample(&mut ch_tampered);

        // The fix: observing â, b̂ makes the downstream challenge depend on them,
        // so lincheck's α (and everything after) diverges and rejects the
        // tampered pair. Before the fix these challenges were equal.
        assert_ne!(
            alpha_honest, alpha_tampered,
            "final â/b̂ claims are NOT bound into the transcript: a product-preserving \
             tamper leaves the downstream challenge unchanged, breaking lincheck's \
             α-batched reduction of (v_a, v_b)",
        );
    }

    /// Determinism: same witness + same transcript seed → same proof.
    #[test]
    fn prove_deterministic() {
        let m = 14;
        let mut rng = Rng::new(99);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();

        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
        let mut ch1 = ProverState::from_label(b"flock-test-v0");
        let mut ch2 = ProverState::from_label(b"flock-test-v0");
        let claim1 = prove_packed(&a_p, &b_p, &c_p, m, &mut ch1);
        let claim2 = prove_packed(&a_p, &b_p, &c_p, m, &mut ch2);

        assert_eq!(ch1.into_proof().stream, ch2.into_proof().stream);
        assert_eq!(claim1.z, claim2.z);
        assert_eq!(claim1.mlv_challenges, claim2.mlv_challenges);
    }

    /// One circuit of a test batch: its packed bits and the same bits unpacked.
    struct TestCircuit {
        m: usize,
        packed: [Vec<u8>; 3],
        dense: [Vec<bool>; 3],
    }

    /// An honest witness of `2^m` bits, `c = a·b`, with each 512-bit block's positions from 400 on empty.
    fn test_circuit(rng: &mut Rng, m: usize) -> TestCircuit {
        let n = 1usize << m;
        let a: Vec<bool> = (0..n).map(|i| i % 512 < 400 && rng.next_u64() & 1 == 1).collect();
        let b: Vec<bool> = (0..n).map(|i| i % 512 < 400 && rng.next_u64() & 1 == 1).collect();
        let c = a.iter().zip(&b).map(|(x, y)| x & y).collect();
        let dense = [a, b, c];
        TestCircuit {
            m,
            packed: dense.clone().map(|b| pack_bits(&b)),
            dense,
        }
    }

    /// The quirky values at `z` of a cube's bits, one per position past the skip.
    fn at_z(bits: &[bool], z: F192) -> Vec<F192> {
        let weights = skip_lagrange_weights(K_SKIP, z);
        (bits.chunks(1 << K_SKIP))
            .map(|row| (row.iter().zip(&weights)).fold(F192::ZERO, |acc, (&bit, &w)| if bit { acc + w } else { acc }))
            .collect()
    }

    /// **A batch sends the sum of its circuits' rounds.** On circuits of mixed sizes:
    /// the round-1 message interpolates to `Σ_f λ^f P_f(z)`, every round's
    /// coefficients are `Σ_f λ^f` of each circuit's own round on its cube, a circuit
    /// done early adding the constant it ended on, and the closing claims are each
    /// circuit's true evaluations.
    #[test]
    fn a_batch_sends_the_sum_of_its_circuits_rounds() {
        let mut rng = Rng::new(0xBA7C);
        let circuits: Vec<TestCircuit> = [13, 17, 15, 20, 16]
            .into_iter()
            .map(|m| test_circuit(&mut rng, m))
            .collect();
        let padding = PaddingSpec {
            k_log: 9,
            useful_bits_per_block: 400,
        };
        let inputs: Vec<ZerocheckInput<'_>> = (circuits.iter())
            .map(|c| {
                let [a, b, cc] = &c.packed;
                ZerocheckInput {
                    bits: PackedWitness { a, b },
                    c: cc,
                    m: c.m,
                    padding,
                }
            })
            .collect();
        let mut ps = ProverState::from_label(b"flock-test-v0");
        let claims = prove(&inputs, &mut ps);
        let proof = ps.into_proof();

        let mut vs = VerifierState::from_label(b"flock-test-v0", &proof);
        let n_mlv = circuits.iter().map(|c| c.m).max().unwrap() - K_SKIP;
        let r = equality_tail(n_mlv + K_SKIP, |n| Challenger::sample_vec(&mut vs, n));
        let lambdas = powers(Challenger::sample(&mut vs), circuits.len());
        let round1 = vs.next_scalars(1 << K_SKIP).unwrap();
        let z = Challenger::sample(&mut vs);
        let mut tables: Vec<[Vec<F192>; 3]> = circuits
            .iter()
            .map(|c| c.dense.clone().map(|bits| at_z(&bits, z)))
            .collect();
        let p_at_z = (tables.iter().zip(&lambdas)).fold(F192::ZERO, |acc, ([a, b, c], &lambda)| {
            let eq = primitives::multilinear::eq_table(&r[..a.len().trailing_zeros() as usize]);
            acc + lambda * (0..a.len()).fold(F192::ZERO, |acc, v| acc + eq[v] * (a[v] * b[v] + c[v]))
        });
        let vanishing = SkipDomain::FLOCK.vanishing(&mut Native, z);
        let mut claim = SkipDomain::FLOCK.first_round_at(&mut Native, z, vanishing, &round1);
        assert_eq!(claim, p_at_z, "round 1");

        // Each circuit's value once done: its `G` at its last challenge.
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
        for (([a, b, c], claim), f) in tables.iter().zip(&claims).zip(0..) {
            let finals = vs.next_scalars(3).unwrap();
            assert_eq!(finals, [a[0], b[0], c[0]], "circuit {f}'s claims");
            assert_eq!(
                [claim.a_eval, claim.b_eval, claim.c_eval],
                [a[0], b[0], c[0]],
                "circuit {f}'s claims"
            );
        }
        vs.finish().unwrap();
    }
}
