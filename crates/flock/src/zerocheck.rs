// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Zerocheck PIOP: prove a(y) · b(y) ⊕ c(y) = 0 for all y ∈ {0,1}^m.
//!
//! Inputs are three bit vectors of length 2^m. Output is an evaluation claim
//! on the multilinear extensions â, b̂, ĉ at the protocol-derived point.
//!
//! Protocol shape (m = log_n, k_skip = [`K_SKIP`] = 6):
//!   1. Verifier constructs `r ∈ F_{2^192}^{m-k_skip}` from fixed inner
//!      coordinates and sampled outer coordinates.
//!   2. Prover sends `P(λ) = P^{AB}(λ) + P^C(λ)` for λ ∈ Λ, |Λ| = 2^k_skip.
//!   3. Verifier samples `z ∈ F_{2^192}` (univariate-skip fold point).
//!   4. For each of the `m - k_skip` multilinear rounds, prover sends
//!      the linear and quadratic coefficients; the verifier derives the constant from the claim and samples the round challenge.
//!   5. Prover sends final MLE evaluations `(â, b̂)`; `ĉ` is what the terminal
//!      identity leaves, `ĉ = claim + â·b̂`, so it never rides the wire.
//!
//! C rides the sumcheck rather than being split off at round 1, which is what
//! puts all three claims at ONE point and leaves lincheck a single family of
//! bit slices for ring switching (doc/leanvm Annex C).

use fiat_shamir::transcript::ProverState;
use primitives::field::{F8, F192};

use pcs::ntt::{AdditiveNttGf8, InvNttTableByteSingleGf8};

pub mod bit_fold;
pub mod multilinear;
pub mod univariate_skip;
pub mod univariate_skip_optimized;

use bit_fold::BitFold;
use multilinear::{
    PackedWitness, bit_round_materialize, bit_round_pair, fold_and_compute_round_pair_into,
    fold_and_compute_round_single_into, fold_in_place_pair, fold_in_place_single, interpolate_at_z_combined,
    round_pair_naive, round_single_naive,
};
use primitives::multilinear::lagrange_weights_naive;
use univariate_skip_optimized::{
    c_s, medium_challenges, round1_shift_reduce_extract_c_packed_padded, small_challenges,
};

/// Number of variables folded in round 1 via the additive-NTT univariate skip.
/// |Λ| = 2^K_SKIP = 64 elements, which is the round-1 prover message: one
/// length-64 vector of F192, the AB and C halves already summed.
pub const K_SKIP: usize = 6;
const N_INNER: usize = 7; // 3 small + 4 medium fixed-constant eq dimensions

/// Passes over the packed bits, two rounds each, before the folded tables are stored.
///
/// - A pass re-reads the three bit tables, `3 * 2^m` bits.
/// - Storing at level `t` writes three F192 tables, `3 * 192 * 2^(m - 6 - t)` bits, then reads them back.
/// - With GFNI a pass is bandwidth-bound, so storing pays once the tables are well below the bits: level 4, after two passes.
/// - The byte-table fold is compute-bound, its tables growing with the level, so a pass costs more than the stored tables' traffic: store at once.
const PAIR_PASSES: usize = if bit_fold::GFNI { 2 } else { 0 };

/// Build the equality coordinates that remain after the univariate skip.
fn equality_tail(m: usize, mut sample_vec: impl FnMut(usize) -> Vec<F192>) -> Vec<F192> {
    let outer = sample_vec(m - K_SKIP - N_INNER);
    small_challenges()
        .into_iter()
        .chain(medium_challenges())
        .chain(outer)
        .collect()
}

/// Witness padding descriptor for URM work-skipping.
///
/// The witness is a sequence of `2^(m - k_log)` blocks of `2^k_log` bits each;
/// inside each block, bits `[0, useful_bits_per_block)` carry real data and
/// bits `[useful_bits_per_block, 2^k_log)` are zero padding. URM contributions
/// from a chunk of all-zero bits are themselves zero, so we can skip those
/// chunks and produce byte-identical output.
pub use pcs::pack::PaddingSpec;

// ---------------------------------------------------------------------------
// The claim.
// ---------------------------------------------------------------------------

/// Evaluation claims on the multilinear extensions of a, b, c, all three at the
/// **same** point `(z, mlv_challenges)`: C rides the sumcheck with AB, so the
/// three claims share the point its challenges define, and lincheck can batch
/// them into one reduction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZerocheckClaim {
    /// Univariate-skip challenge sampled after round 1 (binds the K_SKIP
    /// skip variables), represented directly in `F192`.
    pub z: F192,
    /// Sumcheck bind challenges, one per multilinear round; length = `m - K_SKIP`.
    pub mlv_challenges: Vec<F192>,
    /// `â(z, mlv_challenges)`.
    pub a_eval: F192,
    /// `b̂(z, mlv_challenges)`.
    pub b_eval: F192,
    /// `ĉ(z, mlv_challenges)`, derived from the terminal identity rather than
    /// transmitted: the sumcheck ends at `â·b̂ + ĉ`, so `ĉ = claim + â·b̂`.
    /// Nothing checks it here; lincheck's α-batched identity pins all three.
    pub c_eval: F192,
}

// ---------------------------------------------------------------------------
// The prover.
// ---------------------------------------------------------------------------

/// Send one multilinear round and advance the running claim, the prover mirror
/// of the verifier's loop. `G(0)` never rides the wire: the eq split
/// `(1 + r_eq)·G(0) + r_eq·G(1) = claim` fixes the constant coefficient. At
/// `r_eq = 1` it leaves `G(0)` free, so the caller passes it: only the table
/// rounds can meet that, the earlier ones running on fixed challenges.
fn send_round(
    ps: &mut ProverState,
    claim: F192,
    r_eq: F192,
    g0: Option<F192>,
    g1: F192,
    g_inf: F192,
    chis: &mut Vec<F192>,
) -> F192 {
    let g0 = g0.unwrap_or_else(|| (claim + r_eq * g1) * (F192::ONE + r_eq).inv());
    ps.add_round_poly(&[g0, g0 + g1 + g_inf, g_inf], true);
    let chi = ps.sample();
    chis.push(chi);
    // G(X) = G(0)·(1+X) + G(1)·X + G(inf)·X·(1+X).
    g0 + chi * (g0 + g1 + (F192::ONE + chi) * g_inf)
}

/// THE zerocheck prover entry: proves `a·b ⊕ c = 0` over the padded cube,
/// leaving `(â, b̂, ĉ)` claimed at one point for lincheck to batch.
pub fn prove_packed_padded(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    m: usize,
    padding: &PaddingSpec,
    ps: &mut ProverState,
) -> ZerocheckClaim {
    let k_skip = K_SKIP;
    assert!(
        m >= k_skip + N_INNER,
        "prove requires m >= k_skip + N_INNER (= {})",
        k_skip + N_INNER
    );
    let expected_bytes = (1usize << m) / 8;
    assert_eq!(a_packed.len(), expected_bytes);
    assert_eq!(b_packed.len(), expected_bytes);
    assert_eq!(c_packed.len(), expected_bytes);
    let n_mlv = m - k_skip;

    // ---- Construct the equality tail (with fixed constants in the inner 7 dims) ----
    //
    // r_rest layout:
    //   r_rest[0..3]               : protocol small-eq constants φ_8(0xF7..)
    //   r_rest[3..7]               : protocol medium-eq constants β_i
    //   r_rest[7..m-k_skip]        : sampled outer equality coordinates
    // Prover and verifier use the same tower-valued challenges directly.
    let r_rest = equality_tail(m, |n| ps.sample_vec(n));

    // ---- Round 1: URM (extract_c, parallel) ----
    //
    // The optimized URM drops a `C_s = φ_8(0x1C)` scalar from its accumulators
    // (a prover-side optimization tied to the small-eq trick: see the
    // C_s factor analysis in `univariate_skip_optimized`). The wire format
    // must be in "naive" convention so the verifier doesn't need to know
    // about this internal optimization; we restore the C_s factor here.
    let span = tracing::info_span!("Round 1").entered();
    let ntt_s = AdditiveNttGf8::new(k_skip, F8::ZERO);
    let ntt_l = AdditiveNttGf8::new(k_skip, F8(1u8 << k_skip));
    let inv_table = InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l);
    let (round1_ab_opt, round1_c_opt) = round1_shift_reduce_extract_c_packed_padded(
        a_packed, b_packed, c_packed, m, k_skip, &r_rest, &inv_table, padding,
    );
    let c_s = c_s();
    let round1: Vec<F192> = round1_ab_opt
        .iter()
        .zip(&round1_c_opt)
        .map(|(x, y)| c_s * (*x + *y))
        .collect();
    drop(span);

    // ---- Transmit + bind round-1 message on the stream, sample z ----
    for &x in round1.iter() {
        ps.add_scalar(x);
    }
    let z = ps.sample();

    // ---- Rounds 2 onwards: straight from the packed bits ----
    //
    // Level `t` is the round with `rho_1..rho_t` already bound.
    //
    //     bits of a, b, c    1 bit per slot, 3 * 2^m bits in all
    //     one F192 table     192 bits per slot, 2^(m - 6 - t) slots each
    //
    // While the tables would be larger than the bits, re-reading the bits is the cheaper pass.
    // Each such pass sends two rounds; the second waits on the first's challenge.
    // A last single-round pass stores the three folded tables for the tail.
    //
    // The kernels take the eq challenges of the variables they do not bind.
    // They return the bare `(G(1), G(inf))` that goes on the wire.
    let span = tracing::info_span!("Bit rounds").entered();
    let bits = PackedWitness {
        a: a_packed,
        b: b_packed,
        c: c_packed,
    };
    let lagrange = lagrange_weights_naive(k_skip, z);
    // The running claim, mirrored from the verifier (same round-1 values, same z).
    // `(1 + r) G(0) + r G(1) = claim` lets the wire drop `G(0)`, so the prover needs it too.
    let mut c_running = interpolate_at_z_combined(&round1, k_skip, z);
    let mut mlv_chis: Vec<F192> = Vec::with_capacity(n_mlv);
    for t in (0..(n_mlv - 1) & !1).step_by(2).take(PAIR_PASSES) {
        let fold = BitFold::at_level(&lagrange, &mlv_chis);
        let pair = bit_round_pair(bits, &fold, &r_rest[t + 1..], padding);
        let (g1, g_inf) = pair.first;
        c_running = send_round(ps, c_running, r_rest[t], None, g1, g_inf, &mut mlv_chis);
        let (g1, g_inf) = pair.second(mlv_chis[t]);
        c_running = send_round(ps, c_running, r_rest[t + 1], None, g1, g_inf, &mut mlv_chis);
    }
    let materialize_level = mlv_chis.len();
    let fold = BitFold::at_level(&lagrange, &mlv_chis);
    let ((g1, g_inf), [mut a_mlv, mut b_mlv, mut c_mlv]) =
        bit_round_materialize(bits, &fold, &r_rest[materialize_level + 1..], padding);
    c_running = send_round(ps, c_running, r_rest[materialize_level], None, g1, g_inf, &mut mlv_chis);
    drop(span);
    let span = tracing::info_span!("Table rounds").entered();

    // ---- Remaining rounds, on the stored tables ----
    //
    // Iter i: fold (a, b, c) at ρ_{i+1}, compute the next round's message, sample
    // ρ_{i+2}. Use the fused parallel path while log_n ≥ 10; below that the
    // SplitEq inner can't form lo_size ≥ 2, so we fall back to
    // fold_in_place_* + round_*_naive.
    //
    // Ping-pong scratch buffers for the fused path: each fused round folds
    // (a_mlv, b_mlv, c_mlv) of size N into size N/2. Rather than allocating a
    // fresh buffer per round, we alternate between persistent ones, one per
    // folded table. Scratch capacity = N/2 (the largest fused output); only
    // needed when the first round is actually fused.
    let n_in = a_mlv.len();
    let (mut a_nxt, mut b_nxt, mut c_nxt) = if n_in >= 1024 {
        // SAFETY (x3): the fused rounds below write every slot they read; a
        // buffer is only ever read over the prefix a round just wrote.
        unsafe {
            (
                primitives::uninit_vec::<F192>(n_in / 2),
                primitives::uninit_vec::<F192>(n_in / 2),
                primitives::uninit_vec::<F192>(n_in / 2),
            )
        }
    } else {
        (Vec::new(), Vec::new(), Vec::new())
    };

    for i in materialize_level..(n_mlv - 1) {
        let chi_prev = mlv_chis[i];
        let log_n_before = a_mlv.len().trailing_zeros() as usize;

        // The eq weights of the variables the next round does not bind.
        let r_eq = &r_rest[i + 2..];

        let (m1, mi) = if log_n_before >= 10 {
            let half = a_mlv.len() / 2;
            let (m1, mi) = fold_and_compute_round_pair_into(
                &a_mlv,
                &b_mlv,
                &mut a_nxt[..half],
                &mut b_nxt[..half],
                chi_prev,
                r_eq,
            );
            let m1c = fold_and_compute_round_single_into(&c_mlv, &mut c_nxt[..half], chi_prev, r_eq);
            // Swap current <-> scratch, then shrink the new current to the
            // folded size. The old (larger) buffer becomes scratch; we only
            // ever write its leading `half` slots next round, so its stale
            // length is harmless.
            std::mem::swap(&mut a_mlv, &mut a_nxt);
            std::mem::swap(&mut b_mlv, &mut b_nxt);
            std::mem::swap(&mut c_mlv, &mut c_nxt);
            a_mlv.truncate(half);
            b_mlv.truncate(half);
            c_mlv.truncate(half);
            (m1 + m1c, mi)
        } else {
            fold_in_place_pair(&mut a_mlv, &mut b_mlv, chi_prev);
            fold_in_place_single(&mut c_mlv, chi_prev);
            let (m1, mi) = round_pair_naive(&a_mlv, &b_mlv, r_eq);
            (m1 + round_single_naive(&c_mlv, r_eq), mi)
        };

        let r = r_rest[i + 1];
        let g0 = (r == F192::ONE).then(|| {
            // happens only with probability 2^(-192). We keep it for completeness, but not strictly necessary in the real world
            let eq = primitives::multilinear::eq_table(r_eq);
            (0..eq.len()).fold(F192::ZERO, |acc, x| {
                acc + eq[x] * (a_mlv[2 * x] * b_mlv[2 * x] + c_mlv[2 * x])
            })
        });
        c_running = send_round(ps, c_running, r, g0, m1, mi, &mut mlv_chis);
    }

    // ---- Final binding at ρ_{n_mlv} (the last challenge) ----
    //
    // Only a and b are bound: ĉ comes from the terminal identity below, so
    // `c_mlv`'s last fold would be work for a value nobody reads.
    let chi_last = *mlv_chis.last().expect("at least one ρ sampled");
    fold_in_place_pair(&mut a_mlv, &mut b_mlv, chi_last);
    debug_assert_eq!(a_mlv.len(), 1);
    debug_assert_eq!(b_mlv.len(), 1);

    let final_a_eval = a_mlv[0];
    let final_b_eval = b_mlv[0];
    // The terminal identity `claim = â·b̂ + ĉ` solved for ĉ, the same way the
    // verifier does it. Deriving it here rather than reading `c_mlv[0]` is what
    // keeps the two sides identical on a DISHONEST witness too: the two agree
    // only when `a·b ⊕ c = 0` actually holds, since the running claim descends
    // from the round-1 message, whose reconstruction assumes it.
    let final_c_eval = c_running + final_a_eval * final_b_eval;

    // ---- Fiat-Shamir: bind the final â, b̂ claims into the transcript ----
    //
    // The three claims are reduced downstream by lincheck via a *single*
    // random-linear-combination check in powers of α (see `lincheck`). That
    // batching is only sound if α is sampled *after* they are committed to the
    // transcript: otherwise a prover that knows α can pick them to satisfy the
    // one batched equation while violating the individual checks. So observe
    // them here, before any later challenge (the next one drawn is lincheck's
    // α). `final_c_eval` is NOT transmitted: both sides derive it from the
    // terminal identity, so it is bound by the values that produced it.
    ps.add_scalar(final_a_eval);
    ps.add_scalar(final_b_eval);

    drop(span);

    ZerocheckClaim {
        z,
        mlv_challenges: mlv_chis,
        a_eval: final_a_eval,
        b_eval: final_b_eval,
        c_eval: final_c_eval,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    /// Test shim for the dense-prove entry.
    fn prove_packed(
        a_packed: &[u8],
        b_packed: &[u8],
        c_packed: &[u8],
        m: usize,
        ps: &mut fiat_shamir::transcript::ProverState,
    ) -> ZerocheckClaim {
        prove_packed_padded(a_packed, b_packed, c_packed, m, &PaddingSpec::dense(m), ps)
    }

    /// The quirky evaluation `f̂(z, chi)` of a Boolean witness: the φ8-Lagrange
    /// combination, at `z`, of the multilinear extensions of its 2^K_SKIP bit
    /// slices. This is what the three zerocheck claims are supposed to be.
    fn quirky_eval(bits: &[bool], z: F192, chi: &[F192]) -> F192 {
        let ell = 1usize << K_SKIP;
        let weights = primitives::multilinear::lagrange_weights_naive(K_SKIP, z);
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
        use univariate_skip::pack_bits;
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
            let mut ps = fiat_shamir::transcript::ProverState::from_label(b"flock-test-v0");
            let claim = prove_packed(&a_p, &b_p, &c_p, m, &mut ps);

            // Shape checks: the streamed proof is round1 ‖ (m − K_SKIP)
            // message pairs ‖ (final_a, final_b). C rides the sumcheck, so
            // there is no second Λ-vector and no transmitted ĉ.
            let stream = ps.into_proof().stream;
            assert_eq!(stream.len(), (1 << K_SKIP) + 2 * (m - K_SKIP) + 2, "m={m}");
            assert_eq!(claim.mlv_challenges.len(), m - K_SKIP, "m={m}");

            // Claim's eval fields agree with the streamed final evals (both are
            // now tower values: the prover streams eval).
            assert_eq!(claim.a_eval, stream[stream.len() - 2], "m={m}");
            assert_eq!(claim.b_eval, stream[stream.len() - 1], "m={m}");
        }
    }

    /// **The reduction is faithful.** On an honest witness the three claims
    /// the prover is left with are the true quirky evaluations of a, b and c
    /// at the sumcheck point: including `ĉ`, which nobody transmits and both
    /// sides read off the terminal identity.
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
            let mut ps = fiat_shamir::transcript::ProverState::from_label(b"flock-test-v0");
            let claim = prove_packed(&a_p, &b_p, &c_p, m, &mut ps);

            let chi = &claim.mlv_challenges;
            assert_eq!(claim.a_eval, quirky_eval(&a, claim.z, chi), "â at m={m}");
            assert_eq!(claim.b_eval, quirky_eval(&b, claim.z, chi), "b̂ at m={m}");
            assert_eq!(claim.c_eval, quirky_eval(&c, claim.z, chi), "ĉ at m={m}");
        }
    }

    /// **A false statement leaves a wrong claim.** The zerocheck does not
    /// reject on its own: `ĉ` is whatever the terminal identity leaves, so a
    /// witness violating `a·b ⊕ c = 0` is not caught here but by lincheck,
    /// which pins all three claims against the committed witness. What must
    /// hold at this layer is that such a witness cannot leave all three
    /// claims true.
    #[test]
    fn false_statement_leaves_a_wrong_claim() {
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
                let mut ps = fiat_shamir::transcript::ProverState::from_label(b"flock-test-v0");
                let claim = prove_packed(&a_p, &b_p, &c_p, m, &mut ps);
                let chi = &claim.mlv_challenges;
                let all_true = claim.a_eval == quirky_eval(&a, claim.z, chi)
                    && claim.b_eval == quirky_eval(&b, claim.z, chi)
                    && claim.c_eval == quirky_eval(&c, claim.z, chi);
                assert!(!all_true, "false statement (m={m}, seed={seed}) left every claim true");
            }
        }
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
        let mut ch1 = fiat_shamir::transcript::ProverState::from_label(b"flock-test-v0");
        let mut ch2 = fiat_shamir::transcript::ProverState::from_label(b"flock-test-v0");
        let claim1 = prove_packed(&a_p, &b_p, &c_p, m, &mut ch1);
        let claim2 = prove_packed(&a_p, &b_p, &c_p, m, &mut ch2);

        assert_eq!(ch1.into_proof().stream, ch2.into_proof().stream);
        assert_eq!(claim1.z, claim2.z);
        assert_eq!(claim1.mlv_challenges, claim2.mlv_challenges);
    }
}
