//! The tables' local constraints (§sec:air), proven by one sumcheck for all tables.
//!
//! Each table folds its identities with a DISJOINT range of one `η`'s powers, so
//! the batch is a polynomial in `η` whose coefficients are the individual sums and
//! matching the batch's target still pins each one. The three bus forms are the
//! exception: they SHARE their three powers across tables
//! ([`crate::cpu::xi_form_base`]), so those coefficients are per-side totals and
//! the target pins the total, which is all the bus needs. The identities vanish on a
//! valid row, but a table also attaches its three bus forms, whose sums are the
//! values the bus is owed, so the target is those rather than zero. It is the
//! caller's, not read off the stream: see [`crate::cpu::verify`].
//!
//! Tables of different heights are combined by back-loaded batching: table `t`'s
//! summand is lifted onto the common `n`-cube by `∏_{i ≥ τ_t} X_i`, which leaves
//! its hypercube sum alone. Rounds bind `X_{n-1}` first, so table `t` sits out the
//! first `n − τ_t` and joins at round `n − τ_t` weighted by the challenges it sat
//! out. Two payoffs: every table active in a round binds the same variable, so one
//! eq table serves the round; and the claims land on nested points `ρ[..τ_t]`.
//!
//! With nonzero sums the waiting tables stop dropping out: in a round it sits out, a
//! table's variable reaches its summand once, through the padding product, so its
//! contribution is degree 1 in that variable and vanishes at 0, and all of them
//! share the same challenge product. The round polynomial is the cubic
//! `eq(ζ_m, Y)·p(Y) + Y·u`. Its constant, quadratic and cubic coefficients are
//! sent; the running claim fixes the linear coefficient. The verifier evaluates
//! it at the challenge. Heights and `ζ` enter only the per-table `weights`, which
//! may be accumulated along the way or deferred to the end, as the recursion guest does.
//!
//! The eq point is the caller's, not a fresh one (the bus's GKR point `ζ`), which
//! is what lets the forms' sums settle the bus. Batching derived in `doc/leanvm/main.tex`
//! §sec:air. Both sides take `n = max τ_t` from the announced heights; a recursive
//! verifier certifies that maximum with one hinted `g`-power (§recursion), so there
//! are no rounds in which no table has joined.

use crate::PAR_THRESHOLD;
use crate::colval::ColVal;
use crate::transcript::{Challenger, ProverState, Receiver, Transmitter, VerifierState};
use primitives::field::{F64, F192, F192Unreduced, powers};
use primitives::multilinear::{eq_table_arena, fold_high_inplace, fold_high_k, poly_eval, shrink_eq_high};
use zk_alloc::ArenaVec;

/// One table's involved columns' evaluations at its table-sumcheck point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claims {
    pub chi: Vec<F192>,
    pub evals: Vec<F192>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Truncated,
    FinalMismatch,
}

/// One table's row constraint: identity `i` is weighted by `pows[i]`; `true` selects its homogeneous quadratic part.
pub type Constraint<'a> = Box<dyn Fn(&[F192], &[F192], bool) -> F192 + Sync + 'a>;
/// The same form over `K`-valued columns, for the round a table joins the batch.
pub type ConstraintK<'a> = Box<dyn Fn(&[F192], &[F64], bool) -> F192 + Sync + 'a>;

/// One table's place in the shared batch.
pub struct Air<'a> {
    pub tau: usize,
    pub n_cols: usize,
    pub n_constraints: usize,
    pub eval: Constraint<'a>,
    pub eval_k: ConstraintK<'a>,
}

/// Start of each table's disjoint range of `η`-powers.
pub fn xi_offsets(n_constraints: impl Iterator<Item = usize>) -> Vec<usize> {
    n_constraints
        .scan(0usize, |off, n| {
            let start = *off;
            *off += n;
            Some(start)
        })
        .collect()
}

/// An active round: one endpoint evaluation and the quadratic coefficient.
///
/// Generic twice over: in the column element, `K` before a table's columns are
/// folded and `E` after ([`ColVal`]), and in the container, `Vec` for the former
/// and `ArenaVec` for the latter. `#[inline(always)]` matters here, on this and on
/// every `ColVal` method: this is the body of the constraint sumcheck's innermost
/// loop, and without it the generic stops inlining and costs measurable prover
/// time. Nothing is lifted into `E`, so a `K` round evaluates the identity and the
/// bus forms in 64-bit arithmetic, and its scratch is a third the size.
#[inline(always)]
fn table_message<T: ColVal, C: std::ops::Deref<Target = [T]> + Sync>(
    cols: &[C],
    eval: &(impl Fn(&[F192], &[T], bool) -> F192 + Sync + ?Sized),
    pows: &[F192],
    half: usize,
    eqr: &[F192],
    at_one: bool,
) -> [F192; 2] {
    let ncols = cols.len();
    // The X² coefficient is Q(hi + lo); linear and constant terms cannot contribute.
    let summand = |i: usize, scratch: &mut [T]| -> [F192Unreduced; 2] {
        let e = eqr[i];
        let (endpoint, slope) = scratch.split_at_mut(ncols);
        for (ci, c) in cols.iter().enumerate() {
            let (lo, hi) = (c[i], c[i + half]);
            endpoint[ci] = if at_one { hi } else { lo };
            slope[ci] = lo + hi;
        }
        [
            e.mul_unreduced(eval(pows, endpoint, false)),
            e.mul_unreduced(eval(pows, slope, true)),
        ]
    };
    let xor = |a: [F192Unreduced; 2], b: [F192Unreduced; 2]| [a[0] ^ b[0], a[1] ^ b[1]];
    let acc = if half >= PAR_THRESHOLD {
        // The `2 * ncols` scratch is per-worker, not per-row: `map_reduce_with_state`
        // creates it once and threads it through every row that worker claims.
        parallel::map_reduce_with_state(
            half,
            || vec![T::ZERO; 2 * ncols],
            || [F192Unreduced::ZERO; 2],
            |scratch, acc, i| *acc = xor(*acc, summand(i, scratch)),
            xor,
        )
    } else {
        let mut scratch = vec![T::ZERO; 2 * ncols];
        (0..half).fold([F192Unreduced::ZERO; 2], |acc, i| xor(acc, summand(i, &mut scratch)))
    };
    acc.map(F192Unreduced::reduce)
}

fn round_polynomial([endpoint, quadratic]: [F192; 2], zeta: F192, claim: F192, waiting: F192) -> [F192; 4] {
    let eq_z = F192::ONE + zeta;
    // claim = (1 + zeta) p(0) + zeta p(1) + waiting.
    let (p0, p1) = if zeta.is_zero() {
        (claim + waiting, endpoint)
    } else {
        (endpoint, (claim + waiting + eq_z * endpoint) * zeta.inv())
    };
    let h2 = eq_z * quadratic + p0 + p1 + quadratic;
    [eq_z * p0, claim + h2 + quadratic, h2, quadratic]
}

/// Prove that every table's batched constraint vanishes on all of its rows, as ONE
/// sumcheck over `max τ_t` variables. `cols[t]` holds table `t`'s involved columns
/// (`2^{τ_t}` values each, folded in place). Returns the per-table claims, in input
/// order, on the nested points `ρ[..τ_t]`.
pub fn prove(
    airs: &[Air<'_>],
    cols: &[Vec<&[F64]>],
    xi: F192,
    zeta: &[F192],
    sigma: &[F192],
    ps: &mut ProverState,
) -> Vec<Claims> {
    let n = airs.iter().map(|a| a.tau).max().unwrap_or(0);
    debug_assert!(zeta.len() >= n, "the eq point must cover the tallest table");
    let offsets = xi_offsets(airs.iter().map(|a| a.n_constraints));
    let pows = powers(xi, airs.iter().map(|a| a.n_constraints).sum());
    // η^{offset_t}, already inside `pows`; the rounds then fold in the pre-join
    // challenges and the eq factor, so `weights` is the whole per-table state.
    let mut weights = vec![F192::ONE; airs.len()];
    // ONE eq table over the low (still free) variables serves every active table.
    let mut eqr = eq_table_arena(&zeta[..n.saturating_sub(1)]);
    let mut chi = vec![F192::ZERO; n];
    // The folded tables are the batch's largest transients: one E-lifted copy of
    // every column of every still-active table. Arena-backed, so they are bumped
    // rather than mapped afresh each round.
    let mut folded: Vec<Option<Vec<ArenaVec<F192>>>> = (0..airs.len()).map(|_| None).collect();
    // `k`, the challenges drawn so far, common to every air that is still waiting.
    let mut k = F192::ONE;
    let mut claim = sigma.iter().copied().fold(F192::ZERO, |a, b| a + b);
    for j in 0..n {
        let m = n - 1 - j; // the variable this round binds
        // The waiting airs contribute the line `Y·k·Σσ`, whose slope `u` is all there
        // is to it. It is NOT sent on its own: it folds into `h` below, and only `h`
        // travels. `msg` is the joined airs' degree-2 cofactor, `h`'s multiplicand.
        let waiting = airs
            .iter()
            .zip(sigma)
            .filter(|(a, _)| a.tau <= m)
            .fold(F192::ZERO, |acc, (_, &s)| acc + s);
        let u = k * waiting;
        let mut msg = [F192::ZERO; 2];
        for (t, air) in airs.iter().enumerate() {
            if air.tau > m {
                let w = &pows[offsets[t]..offsets[t] + air.n_constraints];
                let p = if let Some(table) = &folded[t] {
                    table_message(table, &*air.eval, w, 1 << m, &eqr, zeta[m].is_zero())
                } else {
                    table_message(&cols[t], &*air.eval_k, w, 1 << m, &eqr, zeta[m].is_zero())
                };
                for i in 0..2 {
                    msg[i] += weights[t] * p[i];
                }
            }
        }
        shrink_eq_high(&mut eqr);
        // The running claim recovers the missing endpoint of the quadratic cofactor.
        // The fold stays separate: its challenge only exists after this message is bound.
        let h = round_polynomial(msg, zeta[m], claim, u);
        ps.add_round_poly(&h, false);
        let rk = ps.sample();
        claim = poly_eval(&h, rk);
        chi[m] = rk;
        k *= rk;
        let eq_k = F192::ONE + zeta[m] + rk;
        for (t, air) in airs.iter().enumerate() {
            weights[t] *= if air.tau > m { eq_k } else { rk };
            if air.tau <= m {
                continue;
            }
            if let Some(table) = &mut folded[t] {
                if m >= PAR_THRESHOLD.trailing_zeros() as usize {
                    let cols = parallel::Chunks::new(table, 1);
                    parallel::for_each(cols.count(), |ci| {
                        // SAFETY: column `ci` is folded by exactly one task.
                        let col = unsafe { &mut cols.get(ci)[0] };
                        fold_high_inplace(col, rk);
                    });
                } else {
                    table.iter_mut().for_each(|c| fold_high_inplace(c, rk));
                }
            } else {
                // The round a table joins is the largest fold it ever does, so it
                // fans out like the in-place ones below rather than running on the
                // dispatcher alone.
                folded[t] = Some(parallel::map_collect(cols[t].len(), |ci| fold_high_k(cols[t][ci], rk)));
            }
        }
    }

    airs.iter()
        .enumerate()
        .map(|(t, air)| {
            let evals: Vec<F192> = if let Some(table) = &folded[t] {
                table.iter().map(|c| c[0]).collect()
            } else {
                cols[t].iter().map(|c| F192::from(c[0])).collect()
            };
            ps.add_scalars(&evals);
            Claims {
                chi: chi[..air.tau].to_vec(),
                evals,
            }
        })
        .collect()
}

/// Verify the table sumcheck, returning the per-table claims for the caller to
/// settle against the commitment.
pub fn verify(
    airs: &[Air<'_>],
    xi: F192,
    zeta: &[F192],
    target: F192,
    vs: &mut VerifierState,
) -> Result<Vec<Claims>, Error> {
    let n = airs.iter().map(|a| a.tau).max().unwrap_or(0);
    if zeta.len() < n {
        return Err(Error::Truncated);
    }
    let offsets = xi_offsets(airs.iter().map(|a| a.n_constraints));
    let pows = powers(xi, airs.iter().map(|a| a.n_constraints).sum());
    let mut weights = vec![F192::ONE; airs.len()];
    // An ordinary sumcheck for `target`, which the caller supplies. Each round
    // arrives as the round polynomial itself at `nd`, so the two steps are the
    // textbook ones and nothing has to be reapplied: no eq factor, no separate
    // waiting term. `ζ` and the heights enter only `weights`, never the check.
    let mut claim = target;
    let mut chi = vec![F192::ZERO; n];
    for j in 0..n {
        let m = n - 1 - j;
        // The running claim fixes the linear coefficient.
        let h = vs.next_round_poly(4, claim, None).map_err(|_| Error::Truncated)?;
        let rk = vs.sample();
        chi[m] = rk;
        claim = poly_eval(&h, rk);
        let eq_k = F192::ONE + zeta[m] + rk;
        for (t, air) in airs.iter().enumerate() {
            weights[t] *= if air.tau > m { eq_k } else { rk };
        }
    }

    let mut acc = F192::ZERO;
    let mut claims = Vec::with_capacity(airs.len());
    for (t, air) in airs.iter().enumerate() {
        let evals = vs.next_scalars(air.n_cols).map_err(|_| Error::Truncated)?;
        let w = &pows[offsets[t]..offsets[t] + air.n_constraints];
        acc += weights[t] * (air.eval)(w, &evals, false);
        claims.push(Claims {
            chi: chi[..air.tau].to_vec(),
            evals,
        });
    }
    if acc != claim {
        return Err(Error::FinalMismatch);
    }
    Ok(claims)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transcript::{Proof, ProverState, VerifierState};
    use primitives::field::F64;

    fn synth_eval<T: crate::colval::ColVal>(pows: &[F192], v: &[T], quadratic: bool) -> F192 {
        if quadratic {
            return (v[0] * v[1]).mul_e(pows[0]);
        }
        (v[0] * v[1] + v[2]).mul_e(pows[0]) + (v[0] + v[3]).mul_e(pows[1])
    }

    #[test]
    fn round_coefficients_match_full_evaluations() {
        fn check<T: ColVal + Into<F192>>(cols: &[Vec<T>]) {
            let weights = powers(F192::new(3, 5, 7), 3);
            let eq = eq_table_arena(&[F192::new(11, 13, 17), F192::new(19, 23, 29)]);
            let eval = |p: &[F192], v: &[T], quadratic| {
                synth_eval_attached(p, v, quadratic) + if quadratic { F192::ZERO } else { F192::ONE }
            };
            let full_eval = |r| {
                (0..4).fold(F192::ZERO, |sum, i| {
                    let v: Vec<_> = cols
                        .iter()
                        .map(|c| primitives::multilinear::interp(c[i].into(), c[i + 4].into(), r))
                        .collect();
                    sum + eq[i] * (synth_eval_attached(&weights, &v, false) + F192::ONE)
                })
            };
            let waiting = F192::new(43, 47, 53);
            for zeta in [F192::ZERO, F192::ONE, F192::new(59, 61, 67)] {
                let message = table_message(cols, &eval, &weights, 4, &eq, zeta.is_zero());
                let claim = (F192::ONE + zeta) * full_eval(F192::ZERO) + zeta * full_eval(F192::ONE) + waiting;
                let h = round_polynomial(message, zeta, claim, waiting);
                for r in [F192::ZERO, F192::ONE, F192::new(31, 37, 41)] {
                    assert_eq!(poly_eval(&h, r), (F192::ONE + zeta + r) * full_eval(r) + r * waiting);
                }
            }
        }
        let base: Vec<Vec<F64>> = (0..4)
            .map(|j| (0..8).map(|i| F64(13 * i + 17 * j + 1)).collect())
            .collect();
        check(&base);
        let ext: Vec<Vec<F192>> = base
            .iter()
            .map(|c| c.iter().map(|v| F192::new(v.0, 3 * v.0, 7 * v.0)).collect())
            .collect();
        check(&ext);
    }

    fn good_table(tau: usize, salt: u64) -> Vec<Vec<F64>> {
        let n = 1usize << tau;
        let a: Vec<F64> = (0..n).map(|i| F64(i as u64 + salt)).collect();
        let b: Vec<F64> = (0..n).map(|i| F64(3 * i as u64 + 1 + salt)).collect();
        let ab: Vec<F64> = a.iter().zip(&b).map(|(&x, &y)| x * y).collect();
        vec![a.clone(), b, ab, a]
    }

    /// A third, attached "identity": the linear form `vals[1]`, whose claimed sum
    /// is an evaluation of column 1 rather than zero.
    fn synth_eval_attached<T: crate::colval::ColVal>(pows: &[F192], v: &[T], quadratic: bool) -> F192 {
        synth_eval(pows, v, quadratic) + if quadratic { F192::ZERO } else { v[1].mul_e(pows[2]) }
    }

    fn airs_for(taus: &[usize], attached: bool) -> Vec<Air<'static>> {
        taus.iter()
            .map(|&tau| Air {
                tau,
                n_cols: 4,
                n_constraints: if attached { 3 } else { 2 },
                eval: Box::new(if attached {
                    synth_eval_attached::<F192>
                } else {
                    synth_eval::<F192>
                }),
                eval_k: Box::new(if attached {
                    synth_eval_attached::<F64>
                } else {
                    synth_eval::<F64>
                }),
            })
            .collect()
    }

    /// The eq point and `η` are the caller's; the tests fix them.
    fn xi_zeta(taus: &[usize]) -> (F192, Vec<F192>) {
        let n = taus.iter().copied().max().unwrap_or(0);
        let xi = F192::new(0x9e37_79b9_7f4a_7c15, 0x1234_5678_9abc_def0, 7);
        let zeta = (0..n)
            .map(|i| F192::new(i as u64 + 3, 0x5555 * (i as u64 + 1), i as u64 + 11))
            .collect();
        (xi, zeta)
    }

    fn run(taus: &[usize], cols: Vec<Vec<Vec<F64>>>) -> (Proof, Result<Vec<Claims>, Error>) {
        let airs = airs_for(taus, false);
        let (xi, zeta) = xi_zeta(taus);
        let zeros = vec![F192::ZERO; taus.len()];
        let mut ps = ProverState::from_label(b"zc-test");
        let views: Vec<Vec<&[F64]>> = cols.iter().map(|t| t.iter().map(|c| &c[..]).collect()).collect();
        let pclaims = prove(&airs, &views, xi, &zeta, &zeros, &mut ps);
        let proof = ps.into_proof();
        let mut vs = VerifierState::from_label(b"zc-test", &proof);
        let vclaims = verify(&airs, xi, &zeta, F192::ZERO, &mut vs);
        if let Ok(vc) = &vclaims {
            assert_eq!(&pclaims, vc);
        }
        (proof, vclaims)
    }

    #[test]
    fn ragged_batch_verifies() {
        let taus = [5usize, 3, 5, 0, 1];
        let cols = taus.iter().enumerate().map(|(i, &t)| good_table(t, i as u64)).collect();
        let claims = run(&taus, cols).1.expect("honest batch verifies");
        let tallest = claims.iter().max_by_key(|c| c.chi.len()).unwrap().chi.clone();
        for (c, &tau) in claims.iter().zip(&taus) {
            assert_eq!(c.chi, tallest[..tau]);
        }
    }

    #[test]
    fn one_bad_row_in_any_table_is_rejected() {
        let taus = [5usize, 3, 5, 0, 1];
        for bad in 0..taus.len() {
            for col in [2usize, 3] {
                let mut cols: Vec<Vec<Vec<F64>>> =
                    taus.iter().enumerate().map(|(i, &t)| good_table(t, i as u64)).collect();
                cols[bad][col][(1usize << taus[bad]) - 1] += F64::ONE;
                assert!(run(&taus, cols).1.is_err());
            }
        }
    }

    /// An ATTACHED evaluation claim: the extra identity's claimed
    /// sum is `η^2 · col_1(ζ[..τ])`, not zero, so the batch's target is nonzero and
    /// every table that has not joined yet rides a deferred line. Checks the honest
    /// batch verifies and that perturbing ANY table's claimed sum is caught,
    /// including a short table whose line is carried through most of the rounds.
    #[test]
    fn attached_eval_claims_verify_and_bind() {
        let taus = [5usize, 3, 5, 0, 1];
        let cols: Vec<Vec<Vec<F64>>> = taus.iter().enumerate().map(|(i, &t)| good_table(t, i as u64)).collect();
        let (xi, zeta) = xi_zeta(&taus);
        let pows = powers(xi, 3 * taus.len());
        // σ_t = η^{offset_t + 2} · col_1(ζ[..τ_t]): the attached identity is `vals[1]`,
        // so its eq-weighted sum over the table's cube is that column's evaluation.
        let sigmas: Vec<F192> = taus
            .iter()
            .enumerate()
            .map(|(t, &tau)| pows[3 * t + 2] * primitives::multilinear::mle_eval(&cols[t][1], &zeta[..tau]))
            .collect();

        let settle = |sig: &[F192], cols: Vec<Vec<Vec<F64>>>| -> Result<Vec<Claims>, Error> {
            let airs = airs_for(&taus, true);
            let target = sig.iter().fold(F192::ZERO, |a, &b| a + b);
            let mut ps = ProverState::from_label(b"zc-test");
            let views: Vec<Vec<&[F64]>> = cols.iter().map(|t| t.iter().map(|c| &c[..]).collect()).collect();
            let pclaims = prove(&airs, &views, xi, &zeta, sig, &mut ps);
            let proof = ps.into_proof();
            let mut vs = VerifierState::from_label(b"zc-test", &proof);
            let out = verify(&airs, xi, &zeta, target, &mut vs);
            if let Ok(vc) = &out {
                assert_eq!(&pclaims, vc);
            }
            out
        };
        settle(&sigmas, cols.clone()).expect("honest attached claims verify");
        for bad in 0..taus.len() {
            let mut wrong = sigmas.clone();
            wrong[bad] += F192::ONE;
            assert!(
                settle(&wrong, cols.clone()).is_err(),
                "a wrong claimed sum for table {bad} must be rejected"
            );
        }
    }

    /// Tampering any transmitted word breaks the chain: the batch is one sumcheck,
    /// so there is no per-table slack.
    #[test]
    fn tampered_transcript_is_rejected() {
        let taus = [4usize, 2, 4];
        let cols = taus.iter().enumerate().map(|(i, &t)| good_table(t, i as u64)).collect();
        let (proof, ok) = run(&taus, cols);
        assert!(ok.is_ok());
        let airs = airs_for(&taus, false);
        let (xi, zeta) = xi_zeta(&taus);
        for i in 0..proof.stream.len() {
            let mut bad = proof.clone();
            bad.stream[i] += F192::ONE;
            let mut vs = VerifierState::from_label(b"zc-test", &bad);
            assert!(
                verify(&airs, xi, &zeta, F192::ZERO, &mut vs).is_err(),
                "tampered word {i} must be rejected"
            );
        }
    }
}
