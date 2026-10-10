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

use fiat_shamir::arith::{Native, RoundPolynomial, Verifier};
use fiat_shamir::{ProverState, TranscriptError};
use primitives::bit_fold::BitFold;
use primitives::field::{F8, F192, powers};
use primitives::multilinear::skip_lagrange_weights;
use thiserror::Error;

use crate::lincheck::QuirkyPoint;
use multilinear::{PackedWitness, RoundPair, bind_low, bit_pass, bit_pass_storing, single_round, table_pass};
use ntt::{AdditiveNttGf8, InvNttTableByteSingleGf8};
use round1::{Round1, c_s, medium_challenges, small_challenges};

pub(crate) mod multilinear;
mod ntt;
mod padding;
mod round1;
mod skip_domain;

pub(crate) use padding::Padding;
pub use skip_domain::SkipDomain;

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
    let r = equality_tail(n_mlv + K_SKIP, |n| ps.verifier_messages(n));
    let lambdas = powers(ps.verifier_message(), inputs.len());

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
    ps.prover_messages(&round1);

    // Phase 3: the skip challenge sets each circuit's running claim.
    let z = ps.verifier_message();
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
        RoundPolynomial {
            coeffs: message.to_vec(),
        }
        .send(ps, true);
        let chi = ps.verifier_message();
        for prover in provers.iter_mut().filter(|p| j < p.n_mlv()) {
            prover.bind(chi);
        }
    }
    drop(span);

    // Phase 5: the claims are sent before the lincheck's challenge, which batches them.
    // Drawn after them, it cannot be steered by them.
    provers
        .into_iter()
        .map(|prover| {
            let mlv_challenges = prover.chis.clone();
            let (a_eval, b_eval, c_eval) = prover.finish();
            ps.prover_messages(&[a_eval, b_eval, c_eval]);
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
    let outer = v.verifier_messages(m - MIN_LOG_N);
    let lambda = v.verifier_message();
    let lambdas = v.powers(lambda, log_ns.len());
    let fixed: Vec<V::E> = (small_challenges().into_iter().chain(medium_challenges()))
        .map(|c| v.constant(c))
        .collect();

    // Phase 2: round 1, interpolated at the skip challenge.
    let domain = SkipDomain::FLOCK;
    let round1 = v.prover_messages(domain.size())?;
    let z = v.verifier_message();
    let vanishing = domain.vanishing(v, z);
    let mut claim = domain.first_round_at(v, z, vanishing, &round1);

    // Phase 3: the multilinear rounds.
    // The split `G_{j-1}(chi) = (1 + r_eq) G_j(0) + r_eq G_j(1)` absorbs the eq factor of each bound variable.
    let mut mlv_challenges = Vec::with_capacity(m - K_SKIP);
    for &r_eq in fixed.iter().chain(&outer) {
        let g = RoundPolynomial::read(v, 3, claim, Some(r_eq))?.coeffs;
        let chi = v.verifier_message();
        mlv_challenges.push(chi);
        claim = v.poly_eval(&g, chi);
    }

    // Phase 4: the terminal identity, a circuit done early having carried its value unchanged since.
    let mut terminal = v.zero();
    let mut evals = Vec::with_capacity(log_ns.len());
    for &weight in &lambdas {
        let [a, b, c] = [v.prover_message()?, v.prover_message()?, v.prover_message()?];
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

#[cfg(test)]
mod tests {
    use fiat_shamir::{Encoding, FromNarg, ProofTranscript, SessionId, VerifierState};
    use primitives::test_util::Rng;

    use super::*;
    use round1::tests::pack_bits;

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
        let mut ps = ProverState::new(&SessionId::new(LABEL), &0u64);
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
            assert_eq!(proof.narg.len() / 24, (1 << K_SKIP) + 2 * (m - K_SKIP) + 3, "m={m}");

            let mut vs = VerifierState::new(&SessionId::new(LABEL), &0u64, &proof);
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
                let mut vs = VerifierState::new(&SessionId::new(LABEL), &0u64, &proof);
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
            bad.narg[24 * word] ^= 1;
            let mut vs = VerifierState::new(&SessionId::new(LABEL), &0u64, &bad);
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
        short.narg.truncate(short.narg.len() - 3 * 24);
        let mut vs = VerifierState::new(&SessionId::new(LABEL), &0u64, &short);
        assert!(matches!(verify_one(m, &mut vs), Err(ZerocheckError::Transcript(_))));

        // Mutation: claim a cube below the skip and the fixed coordinates.
        let mut vs = VerifierState::new(&SessionId::new(LABEL), &0u64, &proof);
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

        let mut vs = VerifierState::new(&SessionId::new(LABEL), &0u64, &proof);
        verify_one(m, &mut vs).expect("honest");
        let alpha = Verifier::verifier_message(&mut vs);

        let t = F192::new(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 0x55aa_aa55_0123_4567);
        let n = proof.narg.len() / 24;
        let at = |i: usize| 24 * i..24 * i + 24;
        let mut bad = proof.clone();
        let a = F192::from_narg(&mut &bad.narg[at(n - 3)]).unwrap() * t;
        let b = F192::from_narg(&mut &bad.narg[at(n - 2)]).unwrap() * t.inv();
        bad.narg[at(n - 3)].copy_from_slice(&a.encode());
        bad.narg[at(n - 2)].copy_from_slice(&b.encode());
        assert_eq!(a * b, claim.a_eval * claim.b_eval);

        let mut vs = VerifierState::new(&SessionId::new(LABEL), &0u64, &bad);
        verify_one(m, &mut vs).expect("the terminal identity still holds");
        assert_ne!(Verifier::verifier_message(&mut vs), alpha, "the claims are not bound");
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
        let mut ps = ProverState::new(&SessionId::new(LABEL), &0u64);
        let claims = prove(&inputs, &mut ps);
        let proof = ps.into_proof();

        // Replay the challenges by hand, folding each circuit's tables naively alongside.
        let mut vs = VerifierState::new(&SessionId::new(LABEL), &0u64, &proof);
        let n_mlv = circuits.iter().map(|c| c.m).max().unwrap() - K_SKIP;
        let r = equality_tail(n_mlv + K_SKIP, |n| Verifier::verifier_messages(&mut vs, n));
        let lambdas = powers(Verifier::verifier_message(&mut vs), circuits.len());
        let round1 = vs.prover_messages(1 << K_SKIP).unwrap();
        let z = Verifier::verifier_message(&mut vs);
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
            let message = RoundPolynomial::read(&mut vs, 3, claim, Some(r[j])).unwrap().coeffs;
            assert_eq!(message, expected, "round {j}");
            let chi = Verifier::verifier_message(&mut vs);
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
            assert_eq!(
                vs.prover_messages::<F192>(3).unwrap(),
                [a[0], b[0], c[0]],
                "circuit {f}"
            );
            assert_eq!(
                [claim.a_eval, claim.b_eval, claim.c_eval],
                [a[0], b[0], c[0]],
                "circuit {f}"
            );
        }
        vs.check_eof().unwrap();
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
                let mut ps = ProverState::new(&SessionId::new(LABEL), &0u64);
                let claims = prove(&inputs, &mut ps);
                (claims, ps.into_proof().narg)
            };
            assert_eq!(run(true), run(false), "trial {trial}, live {lives:?}");
        }
    }
}
