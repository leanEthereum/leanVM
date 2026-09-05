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
//!      `(P_r(1), P_r(∞))` and verifier samples `ρ_r`.
//!   5. Prover sends final MLE evaluations `(â, b̂)`; `ĉ` is what the terminal
//!      identity leaves, `ĉ = claim + â·b̂`, so it never rides the wire.
//!
//! C rides the sumcheck rather than being split off at round 1, which is what
//! puts all three claims at ONE point and leaves lincheck a single family of
//! bit slices for ring switching (doc/leanvm Annex C).
//!
//! Both `prove` and `verify` are wired end-to-end. The prove→verify roundtrip
//! is tested on honest witnesses; verify also rejects byte-mutated proofs and
//! shape-corrupted ones.

use fiat_shamir::transcript::{Challenger, ProverState, Receiver, Transmitter, VerifierState};
use primitives::field::{F8, F192};
use zk_alloc::ArenaVec;

use pcs::ntt::{AdditiveNttGf8, InvNttTableByteSingleGf8};

pub mod multilinear;
pub mod round1;
pub mod univariate_skip;

use multilinear::{
    UniSkipFoldTable, fold_and_compute_round_pair_into, fold_and_compute_round_single_into, fold_in_place_pair,
    fold_in_place_single, interpolate_at_z_combined, round_pair_naive, round_single_naive,
    uni_skip_fold_and_round_pair_optimized_packed_padded, uni_skip_fold_and_round_single_optimized_packed_padded,
};
use round1::{N_INNER, round1_message_packed_padded};

/// Number of variables folded in round 1 via the additive-NTT univariate skip.
/// |Λ| = 2^K_SKIP = 64 elements, which is the round-1 prover message: one
/// length-64 vector of F192, the AB and C halves already summed.
pub const K_SKIP: usize = 6;

/// Witness padding descriptor for URM work-skipping.
///
/// The witness is a sequence of `2^(m - k_log)` blocks of `2^k_log` bits each;
/// inside each block, bits `[0, useful_bits_per_block)` carry real data and
/// bits `[useful_bits_per_block, 2^k_log)` are zero padding. URM contributions
/// from a chunk of all-zero bits are themselves zero, so we can skip those
/// chunks and produce byte-identical output.
pub use pcs::pack::PaddingSpec;

// ---------------------------------------------------------------------------
// Public types: claim, proof, error.
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
    /// Equality coordinates for the variables left after the univariate skip.
    /// Length = `m - K_SKIP`.
    pub r_rest: Vec<F192>,
    /// `â(z, mlv_challenges)`.
    pub a_eval: F192,
    /// `b̂(z, mlv_challenges)`.
    pub b_eval: F192,
    /// `ĉ(z, mlv_challenges)`, derived from the terminal identity rather than
    /// transmitted: the sumcheck ends at `â·b̂ + ĉ`, so `ĉ = claim + â·b̂`.
    /// Nothing checks it here; lincheck's α-batched identity pins all three.
    pub c_eval: F192,
}

// (No ZerocheckProof struct: every round message rides the shared transcript
// stream, in protocol order.)

/// Reasons the verifier may reject a proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    /// `log_n` doesn't satisfy `log_n >= K_SKIP`.
    LogNTooSmall { log_n: usize, k_skip: usize },
    /// The proof stream ran out while reading a message.
    Transcript(fiat_shamir::transcript::Error),
}

// ---------------------------------------------------------------------------
// API: prove / verify.
// ---------------------------------------------------------------------------

/// Send one multilinear round and advance the running claim, the prover mirror
/// of the verifier's loop. `G(0)` never rides the wire: the eq split
/// `(1 + r_eq)·G(0) + r_eq·G(1) = claim` fixes it. All three evaluations bind.
fn send_round(ps: &mut impl Transmitter, claim: F192, r_eq: F192, g1: F192, g_inf: F192, chis: &mut Vec<F192>) -> F192 {
    let g0 = (claim + r_eq * g1) * (F192::ONE + r_eq).inv();
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

    // The equality tail, every coordinate sampled.
    let r_rest = ps.sample_vec(m - K_SKIP);

    // ---- Round 1: the univariate skip message ----
    let zc_timing = std::env::var_os("FLOCK_ZC_TIMING").is_some();
    let t_round1 = std::time::Instant::now();
    let ntt_s = AdditiveNttGf8::new(k_skip, F8::ZERO);
    let ntt_l = AdditiveNttGf8::new(k_skip, F8(1u8 << k_skip));
    let inv_table = InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l);
    let (round1_ab, round1_c) =
        round1_message_packed_padded(a_packed, b_packed, c_packed, m, k_skip, &r_rest, &inv_table, padding);
    let round1: Vec<F192> = round1_ab.iter().zip(&round1_c).map(|(x, y)| *x + *y).collect();
    if zc_timing {
        eprintln!("[zc-timing] round1: {:.2} ms", t_round1.elapsed().as_secs_f64() * 1e3);
    }

    // ---- Transmit + bind round-1 message on the stream, sample z ----
    for &x in round1.iter() {
        ps.add_scalar(x);
    }
    let z = ps.sample();

    // ---- Round 2: fused fold + first multilinear message ----
    //
    // The kernels take the eq challenges of the variables they do NOT bind and
    // return the bare `(G(1), G(∞))` that goes on the wire. The verifier
    // samples ρ_1 after observing this message. C is linear, so it contributes
    // to `G(1)` only.
    let t_round2 = std::time::Instant::now();
    let fold_table = UniSkipFoldTable::new(k_skip, z);
    let (mut a_mlv, mut b_mlv, msg_1, msg_inf) = uni_skip_fold_and_round_pair_optimized_packed_padded(
        a_packed,
        b_packed,
        m,
        k_skip,
        &fold_table,
        &r_rest[1..],
        padding,
    );
    let (mut c_mlv, msg_c1) =
        uni_skip_fold_and_round_single_optimized_packed_padded(c_packed, m, k_skip, &fold_table, &r_rest[1..], padding);
    let msg_1 = msg_1 + msg_c1;

    if zc_timing {
        eprintln!(
            "[zc-timing] round2 fused fold: {:.2} ms",
            t_round2.elapsed().as_secs_f64() * 1e3
        );
    }
    let t_tail = std::time::Instant::now();
    // The running claim, mirrored from the verifier exactly (same interpolation
    // of the same round-1 values at the same z). `(1+r)·G(0) + r·G(1) = claim`
    // is what lets the wire drop `G(0)`, so the prover has to know it too.
    let mut c_running = interpolate_at_z_combined(&round1, k_skip, z);
    let mut mlv_chis: Vec<F192> = Vec::with_capacity(n_mlv);
    c_running = send_round(ps, c_running, r_rest[0], msg_1, msg_inf, &mut mlv_chis);

    // ---- Rounds 3..(n_mlv + 1) ----
    //
    // Iter i: fold (a, b, c) at ρ_{i+1}, compute round (i+3) message, sample
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
                ArenaVec::<F192>::uninitialized(n_in / 2),
                ArenaVec::<F192>::uninitialized(n_in / 2),
                ArenaVec::<F192>::uninitialized(n_in / 2),
            )
        }
    } else {
        (ArenaVec::new(), ArenaVec::new(), ArenaVec::new())
    };

    for i in 0..(n_mlv - 1) {
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

        c_running = send_round(ps, c_running, r_rest[i + 1], m1, mi, &mut mlv_chis);
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

    if zc_timing {
        eprintln!(
            "[zc-timing] rounds 3+ tail: {:.2} ms",
            t_tail.elapsed().as_secs_f64() * 1e3
        );
    }

    ZerocheckClaim {
        z,
        mlv_challenges: mlv_chis,
        r_rest,
        a_eval: final_a_eval,
        b_eval: final_b_eval,
        c_eval: final_c_eval,
    }
}

/// Replay a zerocheck proof for an instance over `{0,1}^log_n`.
///
/// Walks the transcript in lockstep with the prover, samples the same challenges,
/// and carries the running claim through the rounds. It is a REDUCTION, not a
/// check: `ĉ` is whatever the terminal identity leaves, so no round message can
/// fail here. The only errors are structural (shape, truncated stream). What
/// makes the claims meaningful is lincheck, which pins all three against the
/// committed witness: never call this alone and treat `Ok` as acceptance.
///
/// On accept: returns the [`ZerocheckClaim`] for lincheck and the PCS.
/// On reject: returns a [`VerifyError`] indicating which check failed.
pub fn verify(log_n: usize, vs: &mut VerifierState<'_>) -> Result<ZerocheckClaim, VerifyError> {
    let m = log_n;
    let k_skip = K_SKIP;

    if m < k_skip + N_INNER {
        return Err(VerifyError::LogNTooSmall { log_n: m, k_skip });
    }
    let n_mlv = m - k_skip;
    let ell = 1usize << k_skip;

    // The equality tail, in lockstep with `prove_packed_padded`.
    let r_rest = vs.sample_vec(m - K_SKIP);

    // ---- Read + bind the round-1 message off the stream, sample z ----
    let round1: Vec<F192> = vs.next_scalars(ell).map_err(VerifyError::Transcript)?;
    let z = vs.sample();

    // ---- Reconstruct the initial running claim ----
    //
    // `P = P^{AB} + P^C` has degree < 2·ell in λ. The prover sent only ell
    // evaluations on Λ: not enough on its own. The verifier uses the
    // **zerocheck assumption** `P(λ) = 0` for `λ ∈ S`: together with the ell
    // Λ-evaluations that is 2·ell, enough to interpolate P at z.
    //
    // If the prover's witness is dishonest the S-zero assumption fails and the
    // reconstructed claim is wrong; the chain then ends at a `ĉ` that is not
    // the true evaluation, and lincheck's α-batched identity rejects.
    let mut c_running = interpolate_at_z_combined(&round1, k_skip, z);

    // ---- Multilinear sumcheck chain ----
    //
    // The propagated running claim is the *inner* polynomial value G(ρ),
    // not the full per-round polynomial P(ρ) = eq(r_eq, ρ) · G(ρ). The eq
    // factor for the just-bound variable is absorbed by the next round's
    // consistency check via the identity
    //   G_{r-1}(ρ_{r-1}) = (1 + r_eq_r) · G_r(0) + r_eq_r · G_r(1).
    //
    // Round r (0-indexed i = r − 2) binds the i-th rest variable with eq weight
    // r_rest[i]. The prover sends `(G(1), G(∞))` (Convention A: no
    // factor). Verifier:
    //   1. reconstruct G(0) from consistency `c_running = (1+r_eq)·G(0) + r_eq·G(1)`,
    //   2. observe message, sample ρ_i,
    //   3. update `c_running ← G(ρ_i)`,
    //      where `G(X) = G(0)·(1+X) + G(1)·X + G(∞)·X·(X+1)` (char-2 quadratic
    //      interpolation through G(0), G(1), G(∞)).
    let mut mlv_chis: Vec<F192> = Vec::with_capacity(n_mlv);
    for i in 0..n_mlv {
        let r_eq = r_rest[i];
        let g = vs
            .next_round_poly(3, c_running, Some(r_eq))
            .map_err(VerifyError::Transcript)?;
        let chi = vs.sample();
        mlv_chis.push(chi);
        c_running = primitives::multilinear::poly_eval(&g, chi);
    }

    // ---- Terminal identity ----
    //
    // After all variables are bound, the inner running claim is the polynomial
    // without the eq weighting:
    //   G_final(ρ) = â(z, ρ)·b̂(z, ρ) + ĉ(z, ρ).
    // (The eq factors were absorbed round-by-round into the consistency checks,
    // never accumulating into the running claim.)
    //
    // Read + bind the final â, b̂ claims off the stream: binding must land
    // before the next challenge (lincheck's α) is drawn, so the α-batched
    // reduction of the three claims is sound. `ĉ` is not transmitted: it is
    // what the identity leaves, so there is nothing to check here. A prover who
    // lies about anything upstream just shifts the lie into `ĉ`, and lincheck,
    // which pins all three against the committed witness, rejects it.
    let final_a_eval = vs.next_scalar().map_err(VerifyError::Transcript)?;
    let final_b_eval = vs.next_scalar().map_err(VerifyError::Transcript)?;
    let final_c_eval = c_running + final_a_eval * final_b_eval;

    Ok(ZerocheckClaim {
        z,
        mlv_challenges: mlv_chis,
        r_rest,
        a_eval: final_a_eval,
        b_eval: final_b_eval,
        c_eval: final_c_eval,
    })
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
        ps: &mut pcs::ProverState,
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

    /// `prove` runs end-to-end from the smallest valid m (= k_skip + N_INNER)
    /// up without panicking, and produces output of the right shape.
    ///
    /// structural sanity here catches:
    ///   - mismatched observe/sample sequence
    ///   - wrong slice lengths in the eq-challenge tail at any round
    ///   - any unreachable assert in the underlying functions
    #[test]
    fn prove_runs_end_to_end() {
        for &m in &[10usize, 13, 14, 15, 16] {
            let mut rng = Rng::new(m as u64);
            let a = rng.bits(1 << m);
            let b = rng.bits(1 << m);
            // Honest witness: c = a AND b, so a·b ⊕ c = 0 on the hypercube.
            let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();

            let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
            let mut ps = pcs::ProverState::from_label(b"flock-test-v0");
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
            let mut ch_prove = pcs::ProverState::from_label(b"flock-test-v0");
            let claim_p = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);

            let proof_t = ch_prove.into_proof();
            let mut ch_verify = pcs::VerifierState::from_label(b"flock-test-v0", &proof_t);
            let result = verify(m, &mut ch_verify);
            let claim_v = result.unwrap_or_else(|e| panic!("verify rejected at m={m}: {e:?}"));

            assert_eq!(claim_p, claim_v, "claim mismatch at m={m}");
        }
    }

    /// **The reduction is faithful.** On an honest witness the three claims
    /// the verifier ends up with are the true quirky evaluations of a, b and c
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
            let mut ch_prove = pcs::ProverState::from_label(b"flock-test-v0");
            let _ = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);
            let proof_t = ch_prove.into_proof();
            let mut ch = pcs::VerifierState::from_label(b"flock-test-v0", &proof_t);
            let claim = verify(m, &mut ch).expect("honest proof");

            let chi = &claim.mlv_challenges;
            assert_eq!(claim.a_eval, quirky_eval(&a, claim.z, chi), "â at m={m}");
            assert_eq!(claim.b_eval, quirky_eval(&b, claim.z, chi), "b̂ at m={m}");
            assert_eq!(claim.c_eval, quirky_eval(&c, claim.z, chi), "ĉ at m={m}");
        }
    }

    /// **AUDIT: a false statement leaves a wrong claim.** The zerocheck no
    /// longer rejects on its own: `ĉ` is whatever the terminal identity
    /// leaves, so a witness violating `a·b ⊕ c = 0` is not caught here but by
    /// lincheck, which pins all three claims against the committed witness.
    /// What must hold at this layer is that such a witness cannot leave all
    /// three claims true. Same for a tampered proof word: it moves the
    /// derived claims off the true evaluations.
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
                let mut ch_prove = pcs::ProverState::from_label(b"flock-test-v0");
                let _ = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);
                let proof_t = ch_prove.into_proof();
                let mut ch = pcs::VerifierState::from_label(b"flock-test-v0", &proof_t);
                let claim = verify(m, &mut ch).expect("shape is still valid");
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
        let mut ch_prove = pcs::ProverState::from_label(b"flock-test-v0");
        let _ = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);
        let proof_t = ch_prove.into_proof();

        let ell = 1usize << K_SKIP;
        let n_mlv = m - K_SKIP;
        let mutations: [(&str, usize); 6] = [
            ("round1[0]", 0),
            ("round1[5]", 5),
            ("multilinear_rounds[0].0", ell),
            ("multilinear_rounds[mid].1", ell + 2 * (n_mlv / 2) + 1),
            ("final_a_eval", ell + 2 * n_mlv),
            ("final_b_eval", ell + 2 * n_mlv + 1),
        ];
        for (label, word) in mutations {
            let mut bad = proof_t.clone();
            bad.stream[word].c0 ^= 1;
            let mut ch = pcs::VerifierState::from_label(b"flock-test-v0", &bad);
            let claim = verify(m, &mut ch).expect("shape is still valid");
            let chi = &claim.mlv_challenges;
            let all_true = claim.a_eval == quirky_eval(&a, claim.z, chi)
                && claim.b_eval == quirky_eval(&b, claim.z, chi)
                && claim.c_eval == quirky_eval(&c, claim.z, chi);
            assert!(!all_true, "tampered proof ({label}) left every claim true");
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
        let mut ch_prove = pcs::ProverState::from_label(b"flock-test-v0");
        let _ = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);
        let proof_t = ch_prove.into_proof();

        // Truncated stream: a clean Transcript error, not a panic.
        let mut bad = proof_t.clone();
        bad.stream.truncate(bad.stream.len() - 3);
        let mut ch = pcs::VerifierState::from_label(b"flock-test-v0", &bad);
        assert!(matches!(verify(m, &mut ch), Err(VerifyError::Transcript(_))));

        // log_n too small.
        let mut ch = pcs::VerifierState::from_label(b"flock-test-v0", &proof_t);
        assert!(matches!(
            verify(K_SKIP + N_INNER - 1, &mut ch),
            Err(VerifyError::LogNTooSmall { .. })
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
    /// leaves `â·b̂` and therefore the derived `ĉ` untouched: the whole triple
    /// the reduction carries is unchanged, and nothing downstream could tell
    /// the two runs apart except the transcript itself. The defense is that
    /// both claims are observed last, so the next challenge (the slot lincheck
    /// draws α from) must diverge. This assertion FAILS before the observe was
    /// added (identical post-state) and passes now.
    #[test]
    fn audit_final_ab_claims_bound_to_transcript() {
        let m = 14;
        let mut rng = Rng::new(0xF1A7_5A11);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);

        let mut ch_prove = pcs::ProverState::from_label(b"flock-test-v0");
        let claim_p = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);
        let proof_t = ch_prove.into_proof();

        // Honest verify, then capture the next challenge the transcript feeds
        // downstream: this is exactly the slot lincheck samples α from.
        let mut ch_honest = pcs::VerifierState::from_label(b"flock-test-v0", &proof_t);
        assert!(verify(m, &mut ch_honest).is_ok(), "honest verify rejected");
        let alpha_honest = ch_honest.sample();

        // Product-preserving tamper: â' = â·t, b̂' = b̂·t⁻¹ ⇒ â'·b̂' = â·b̂, so the
        // derived ĉ = claim + â·b̂ is unchanged too.
        // The stream now carries tower (F192) values, so tamper in F192.
        let t = F192::new(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 0x55aa_aa55_0123_4567);
        assert!(t != F192::ZERO && t != F192::ONE, "t must be nontrivial");
        // The finals are the LAST two stream words of this standalone proof.
        let n = proof_t.stream.len();
        let mut bad = proof_t.clone();
        bad.stream[n - 2] *= t;
        bad.stream[n - 1] *= t.inv();
        assert_ne!(bad.stream[n - 2], proof_t.stream[n - 2], "tamper must change â");
        assert_ne!(bad.stream[n - 1], proof_t.stream[n - 1], "tamper must change b̂");
        assert_eq!(
            bad.stream[n - 2] * bad.stream[n - 1],
            claim_p.a_eval * claim_p.b_eval,
            "tamper must preserve the product",
        );

        // Replay the tampered proof to move the transcript to the same slot. Its
        // claims are as consistent as the honest ones (same product, same ĉ),
        // so nothing local distinguishes them.
        let mut ch_tampered = pcs::VerifierState::from_label(b"flock-test-v0", &bad);
        let tampered = verify(m, &mut ch_tampered).expect("shape is still valid");
        assert_eq!(
            tampered.a_eval * tampered.b_eval,
            claim_p.a_eval * claim_p.b_eval,
            "the tamper must preserve the product the reduction carries",
        );
        assert_eq!(tampered.c_eval, claim_p.c_eval, "and therefore the derived ĉ");
        let alpha_tampered = ch_tampered.sample();

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
        let mut ch1 = pcs::ProverState::from_label(b"flock-test-v0");
        let mut ch2 = pcs::ProverState::from_label(b"flock-test-v0");
        let claim1 = prove_packed(&a_p, &b_p, &c_p, m, &mut ch1);
        let claim2 = prove_packed(&a_p, &b_p, &c_p, m, &mut ch2);

        assert_eq!(ch1.into_proof().stream, ch2.into_proof().stream);
        assert_eq!(claim1.z, claim2.z);
        assert_eq!(claim1.mlv_challenges, claim2.mlv_challenges);
    }
}
