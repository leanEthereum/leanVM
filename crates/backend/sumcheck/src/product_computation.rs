use fiat_shamir::*;
use field::*;
use poly::*;
use tracing::instrument;
use zk_alloc::ArenaVec;

use crate::{SumcheckComputation, sumcheck_prove_many_rounds};

#[derive(Debug)]
pub struct ProductComputation;

impl<EF: ExtensionField<PF<EF>>> SumcheckComputation<EF> for ProductComputation {
    type ExtraData = Vec<EF>;

    fn degree(&self) -> usize {
        2
    }
    #[inline(always)]
    fn eval_base(&self, _point: &[PF<EF>], _: &Self::ExtraData) -> EF {
        unreachable!()
    }
    #[inline(always)]
    fn eval_extension(&self, point: &[EF], _: &Self::ExtraData) -> EF {
        point[0] * point[1]
    }
    #[inline(always)]
    fn eval_packed_base(&self, point: &[PFPacking<EF>], _: &Self::ExtraData) -> EFPacking<EF> {
        EFPacking::<EF>::from(point[0] * point[1])
    }
    #[inline(always)]
    fn eval_packed_extension(&self, point: &[EFPacking<EF>], _: &Self::ExtraData) -> EFPacking<EF> {
        point[0] * point[1]
    }
}

#[instrument(skip_all)]
pub fn run_product_sumcheck<EF: ExtensionField<PF<EF>>>(
    pol_a: &MleRef<'_, EF>, // evals
    pol_b: &MleRef<'_, EF>, // weights
    prover_state: &mut impl FSProver<EF>,
    mut sum: EF,
    n_rounds: usize,
    pow_bits: usize,
) -> (MultilinearPoint<EF>, EF, MleOwned<EF>, MleOwned<EF>) {
    assert!(n_rounds >= 1);
    if let (MleRef::BasePacked(evals), MleRef::ExtensionPacked(weights)) = (pol_a, pol_b) {
        if EF::DIMENSION == 3 {
            // Lazy path for large instances only; the eager path stays the
            // fallback (and keeps bytecode_claims' small-domain call site on
            // its existing code).
            let n_vars = (evals.len() * PFPacking::<EF>::WIDTH).trailing_zeros() as usize;
            if n_vars >= 18 && n_rounds >= 2 {
                return run_product_sumcheck_base_lazy::<3, EF>(evals, weights, prover_state, sum, n_rounds, pow_bits);
            }
            return run_product_sumcheck_base_eager::<3, EF>(evals, weights, prover_state, sum, n_rounds, pow_bits);
        }
        unimplemented!()
    }
    let first_sumcheck_poly = match (pol_a, pol_b) {
        (MleRef::ExtensionPacked(evals), MleRef::ExtensionPacked(weights)) => {
            compute_product_sumcheck_polynomial(evals, weights, sum, |e| EFPacking::<EF>::to_ext_iter([e]).collect())
        }
        (MleRef::Base(evals), MleRef::Extension(weights)) => {
            compute_product_sumcheck_polynomial(evals, weights, sum, |e| vec![e])
        }
        (MleRef::Extension(evals), MleRef::Extension(weights)) => {
            compute_product_sumcheck_polynomial(evals, weights, sum, |e| vec![e])
        }
        _ => unimplemented!(),
    };

    prover_state.add_sumcheck_polynomial(&first_sumcheck_poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r1: EF = prover_state.sample();
    sum = first_sumcheck_poly.evaluate(r1);

    if n_rounds == 1 {
        return (MultilinearPoint(vec![r1]), sum, pol_a.fold(r1), pol_b.fold(r1));
    }

    let (second_sumcheck_poly, folded) = match (pol_a, pol_b) {
        (MleRef::ExtensionPacked(evals), MleRef::ExtensionPacked(weights)) => {
            let (second_sumcheck_poly, folded) =
                fold_and_compute_product_sumcheck_polynomial(evals, weights, r1, sum, |e| {
                    EFPacking::<EF>::to_ext_iter([e]).collect()
                });
            (second_sumcheck_poly, MleGroupOwned::ExtensionPacked(folded))
        }
        (MleRef::Base(evals), MleRef::Extension(weights)) => {
            let (second_sumcheck_poly, folded) =
                fold_and_compute_product_sumcheck_polynomial(evals, weights, r1, sum, |e| vec![e]);
            (second_sumcheck_poly, MleGroupOwned::Extension(folded))
        }
        (MleRef::Extension(evals), MleRef::Extension(weights)) => {
            let (second_sumcheck_poly, folded) =
                fold_and_compute_product_sumcheck_polynomial(evals, weights, r1, sum, |e| vec![e]);
            (second_sumcheck_poly, MleGroupOwned::Extension(folded))
        }
        _ => unimplemented!(),
    };

    prover_state.add_sumcheck_polynomial(&second_sumcheck_poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r2: EF = prover_state.sample();
    sum = second_sumcheck_poly.evaluate(r2);

    let (mut challenges, folds, sum) = sumcheck_prove_many_rounds(
        folded,
        Some(r2),
        &ProductComputation {},
        &vec![],
        None,
        prover_state,
        sum,
        None,
        n_rounds - 2,
        false,
        pow_bits,
    );

    challenges.splice(0..0, [r1, r2]);
    let [pol_a, pol_b] = folds.split().try_into().unwrap();
    (challenges, sum, pol_a, pol_b)
}

/// Eager path for the (BasePacked, ExtensionPacked) arm, extracted verbatim from
/// `run_product_sumcheck`. Kept as the equality oracle for the lazy path and as
/// the fallback for small instances. Generic over `DIM` so the full path is
/// exercisable by the KoalaBear (DIM = 5) test harness.
pub fn run_product_sumcheck_base_eager<const DIM: usize, EF: ExtensionField<PF<EF>>>(
    evals: &[PFPacking<EF>],
    weights: &[EFPacking<EF>],
    prover_state: &mut impl FSProver<EF>,
    mut sum: EF,
    n_rounds: usize,
    pow_bits: usize,
) -> (MultilinearPoint<EF>, EF, MleOwned<EF>, MleOwned<EF>) {
    assert!(n_rounds >= 1);
    let first_sumcheck_poly =
        compute_product_sumcheck_polynomial_base_ext_packed::<DIM, _, _, _, EF>(evals, weights, sum);

    prover_state.add_sumcheck_polynomial(&first_sumcheck_poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r1: EF = prover_state.sample();
    sum = first_sumcheck_poly.evaluate(r1);

    if n_rounds == 1 {
        return (
            MultilinearPoint(vec![r1]),
            sum,
            MleRef::<EF>::BasePacked(evals).fold(r1),
            MleRef::<EF>::ExtensionPacked(weights).fold(r1),
        );
    }

    let (second_sumcheck_poly, folded) = {
        let (second_sumcheck_poly, folded) =
            fold_and_compute_product_sumcheck_polynomial(evals, weights, r1, sum, |e| {
                EFPacking::<EF>::to_ext_iter([e]).collect()
            });
        (second_sumcheck_poly, MleGroupOwned::ExtensionPacked(folded))
    };

    prover_state.add_sumcheck_polynomial(&second_sumcheck_poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r2: EF = prover_state.sample();
    sum = second_sumcheck_poly.evaluate(r2);

    let (mut challenges, folds, sum) = sumcheck_prove_many_rounds(
        folded,
        Some(r2),
        &ProductComputation {},
        &vec![],
        None,
        prover_state,
        sum,
        None,
        n_rounds - 2,
        false,
        pow_bits,
    );

    challenges.splice(0..0, [r1, r2]);
    let [pol_a, pol_b] = folds.split().try_into().unwrap();
    (challenges, sum, pol_a, pol_b)
}

/// Lazy-fold path for the (BasePacked, ExtensionPacked) arm.
///
/// Round 1 never materializes the folded eval array: evals stay as two implicit
/// base streams `a_i = P[i]`, `b_i = P[half+i] - P[i]` (the fold by `r1` is kept
/// challenge-symbolic and bound once per accumulator), while the weights are
/// folded eagerly in the same pass. Round 2 entry then materializes the
/// double-folded evals directly from `P` via the 4-term basis comb
/// `E''[i] = a_i + r1 b_i + r2 da_i + r1 r2 db_i` fused with the W''-fold and the
/// round-2 quadratic. All reorderings are exact field identities, so the
/// transcript is bit-identical to the eager path (enforced by the equality
/// tests below and the e2e proof byte-diff gate).
pub fn run_product_sumcheck_base_lazy<const DIM: usize, EF: ExtensionField<PF<EF>>>(
    evals: &[PFPacking<EF>],
    weights: &[EFPacking<EF>],
    prover_state: &mut impl FSProver<EF>,
    mut sum: EF,
    n_rounds: usize,
    pow_bits: usize,
) -> (MultilinearPoint<EF>, EF, MleOwned<EF>, MleOwned<EF>) {
    assert!(n_rounds >= 2);
    let first_sumcheck_poly =
        compute_product_sumcheck_polynomial_base_ext_packed::<DIM, _, _, _, EF>(evals, weights, sum);

    prover_state.add_sumcheck_polynomial(&first_sumcheck_poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r1: EF = prover_state.sample();
    sum = first_sumcheck_poly.evaluate(r1);

    let (second_sumcheck_poly, w_folded) =
        fold_weights_and_compute_lazy_round1::<DIM, _, _, _, EF>(evals, weights, r1, sum);

    prover_state.add_sumcheck_polynomial(&second_sumcheck_poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r2: EF = prover_state.sample();
    sum = second_sumcheck_poly.evaluate(r2);

    let decompose = |e| EFPacking::<EF>::to_ext_iter([e]).collect::<Vec<EF>>();

    if n_rounds == 2 {
        let (_, e2, w2) = materialize_double_fold_and_compute_round2::<DIM, _, _, _, EF>(
            evals, &w_folded, r1, r2, sum, false, decompose,
        );
        return (
            MultilinearPoint(vec![r1, r2]),
            sum,
            MleOwned::ExtensionPacked(e2),
            MleOwned::ExtensionPacked(w2),
        );
    }

    let (third_sumcheck_poly, e2, w2) =
        materialize_double_fold_and_compute_round2::<DIM, _, _, _, EF>(evals, &w_folded, r1, r2, sum, true, decompose);
    let third_sumcheck_poly = third_sumcheck_poly.unwrap();

    prover_state.add_sumcheck_polynomial(&third_sumcheck_poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r3: EF = prover_state.sample();
    sum = third_sumcheck_poly.evaluate(r3);

    let (mut challenges, folds, sum) = sumcheck_prove_many_rounds(
        MleGroupOwned::ExtensionPacked(vec![e2, w2]),
        Some(r3),
        &ProductComputation {},
        &vec![],
        None,
        prover_state,
        sum,
        None,
        n_rounds - 3,
        false,
        pow_bits,
    );

    challenges.splice(0..0, [r1, r2, r3]);
    let [pol_a, pol_b] = folds.split().try_into().unwrap();
    (challenges, sum, pol_a, pol_b)
}

/// Round-1 kernel of the lazy path: folds the weights by `r1` (the only array
/// that must be materialized) and computes the round-1 quadratic with the eval
/// fold kept challenge-symbolic: writing `E'[j] = a_j + r1 b_j` (`a_j = P[j]`,
/// `b_j = P[half+j] - P[j]`, both base field) and pairing `(j, q+j)`,
///
///   c0 = sum_j E'[j] W'[j]                 = S_c0a + r1 S_c0b
///   c2 = sum_j (E'[q+j]-E'[j])(W'[q+j]-W'[j]) = S_c2a + r1 S_c2b
///
/// with the four S-streams pure base-x-ext lazy-accumulator sums; `r1` is bound
/// once per stream after the horizontal lane sum. Per L2-resident chunk the
/// work is five passes (W'-fold + one per stream), each holding DIM lazy
/// accumulators (3 groups x 4 zmm — the register budget proven by the round-0
/// kernel above).
#[allow(clippy::needless_range_loop)]
pub fn fold_weights_and_compute_lazy_round1<
    const DIM: usize,
    F: PrimeField64,
    PF: PackedField<Scalar = F>,
    EFP: BasedVectorSpace<PF> + Algebra<PF> + From<EF> + Copy + Send + Sync + 'static,
    EF: Field + BasedVectorSpace<F>,
>(
    pol_0: &[PF],
    pol_1: &[EFP],
    r1: EF,
    sum: EF,
) -> (DensePolynomial<EF>, ArenaVec<EFP>) {
    assert_eq!(DIM, EF::DIMENSION);
    let n = pol_0.len();
    assert_eq!(n, pol_1.len());
    assert!(n.is_power_of_two());
    assert!(n >= 4);
    let half = n / 2;
    let q = half / 2;
    let r1_packed = EFP::from(r1);

    let mut w_folded = unsafe { ArenaVec::<EFP>::uninitialized(half) };
    let wf_ptr = parallel::SendPtr(w_folded.as_mut_ptr());

    let chunk_size = 1024;
    let n_chunks = q.div_ceil(chunk_size);

    // Four unreduced streams (n_sub = 0: every term is a raw positive product
    // of canonical elements; chunk length 1024 <= 2^20 honors the protocol
    // bound, see the round-0 kernel comment).
    type Streams<PF, const DIM: usize> = ([PF; DIM], [PF; DIM], [PF; DIM], [PF; DIM]);
    let (c0a_acc, c0b_acc, c2a_acc, c2b_acc): Streams<PF, DIM> = parallel::map_reduce(
        n_chunks,
        || ([PF::ZERO; DIM], [PF::ZERO; DIM], [PF::ZERO; DIM], [PF::ZERO; DIM]),
        |chunk| {
            let start = chunk * chunk_size;
            let end = (start + chunk_size).min(q);

            // Pass A: fold the weights for both halves of the pair range and
            // store into W' (the only materialized array).
            for i in start..end {
                let w_lo = r1_packed * (pol_1[half + i] - pol_1[i]) + pol_1[i];
                let w_hi = r1_packed * (pol_1[half + q + i] - pol_1[q + i]) + pol_1[q + i];
                unsafe {
                    *wf_ptr.add(i) = w_lo;
                    *wf_ptr.add(q + i) = w_hi;
                }
            }
            let w_lo_chunk: &[EFP] = unsafe { core::slice::from_raw_parts(wf_ptr.add(start), end - start) };
            let w_hi_chunk: &[EFP] = unsafe { core::slice::from_raw_parts(wf_ptr.add(q + start), end - start) };

            // Pass B: S_c0a += a_lo * w_lo.
            let mut c0a: [[PF; 4]; DIM] = core::array::from_fn(|_| PF::lazy_acc_zero());
            for i in 0..(end - start) {
                let a = pol_0[start + i];
                let w = w_lo_chunk[i].as_basis_coefficients_slice();
                for j in 0..DIM {
                    c0a[j] = PF::lazy_acc_add(c0a[j], PF::unreduced_mul(w[j], a));
                }
            }
            // Pass C: S_c0b += b_lo * w_lo.
            let mut c0b: [[PF; 4]; DIM] = core::array::from_fn(|_| PF::lazy_acc_zero());
            for i in 0..(end - start) {
                let b = pol_0[half + start + i] - pol_0[start + i];
                let w = w_lo_chunk[i].as_basis_coefficients_slice();
                for j in 0..DIM {
                    c0b[j] = PF::lazy_acc_add(c0b[j], PF::unreduced_mul(w[j], b));
                }
            }
            // Pass D1: S_c2a += (a_hi - a_lo) * (w_hi - w_lo).
            let mut c2a: [[PF; 4]; DIM] = core::array::from_fn(|_| PF::lazy_acc_zero());
            for i in 0..(end - start) {
                let da = pol_0[q + start + i] - pol_0[start + i];
                let dw = w_hi_chunk[i] - w_lo_chunk[i];
                let dw_coords = dw.as_basis_coefficients_slice();
                for j in 0..DIM {
                    c2a[j] = PF::lazy_acc_add(c2a[j], PF::unreduced_mul(dw_coords[j], da));
                }
            }
            // Pass D2: S_c2b += (b_hi - b_lo) * (w_hi - w_lo).
            let mut c2b: [[PF; 4]; DIM] = core::array::from_fn(|_| PF::lazy_acc_zero());
            for i in 0..(end - start) {
                let b_lo = pol_0[half + start + i] - pol_0[start + i];
                let b_hi = pol_0[half + q + start + i] - pol_0[q + start + i];
                let db = b_hi - b_lo;
                let dw = w_hi_chunk[i] - w_lo_chunk[i];
                let dw_coords = dw.as_basis_coefficients_slice();
                for j in 0..DIM {
                    c2b[j] = PF::lazy_acc_add(c2b[j], PF::unreduced_mul(dw_coords[j], db));
                }
            }
            (
                core::array::from_fn(|j| PF::lazy_acc_finish(c0a[j], 0)),
                core::array::from_fn(|j| PF::lazy_acc_finish(c0b[j], 0)),
                core::array::from_fn(|j| PF::lazy_acc_finish(c2a[j], 0)),
                core::array::from_fn(|j| PF::lazy_acc_finish(c2b[j], 0)),
            )
        },
        |(mut a0, mut a1, mut a2, mut a3): Streams<PF, DIM>, (b0, b1, b2, b3): Streams<PF, DIM>| {
            for j in 0..DIM {
                a0[j] += b0[j];
                a1[j] += b1[j];
                a2[j] += b2[j];
                a3[j] += b3[j];
            }
            (a0, a1, a2, a3)
        },
    );

    let lane_sum = |p: PF| {
        let mut s = F::ZERO;
        for &v in p.as_slice() {
            s += v;
        }
        s
    };
    let s_c0a = EF::from_basis_coefficients_fn(|j| lane_sum(c0a_acc[j]));
    let s_c0b = EF::from_basis_coefficients_fn(|j| lane_sum(c0b_acc[j]));
    let s_c2a = EF::from_basis_coefficients_fn(|j| lane_sum(c2a_acc[j]));
    let s_c2b = EF::from_basis_coefficients_fn(|j| lane_sum(c2b_acc[j]));

    // Bind r1 once per stream.
    let c0 = s_c0a + r1 * s_c0b;
    let c2 = s_c2a + r1 * s_c2b;
    let c1 = sum - c0.double() - c2;

    (DensePolynomial::new(vec![c0, c1, c2]), w_folded)
}

/// Round-2 entry of the lazy path: materializes the double-folded evals
/// directly from the original base array via the 4-term basis comb, folds the
/// weights by `r2`, and (unless `compute_quad` is false, i.e. `n_rounds == 2`)
/// computes the round-2 quadratic — all in one parallel pass.
#[allow(clippy::too_many_arguments)]
pub fn materialize_double_fold_and_compute_round2<
    const DIM: usize,
    F: PrimeField64,
    PF: PackedField<Scalar = F>,
    EFP: BasedVectorSpace<PF> + Algebra<PF> + From<EF> + Copy + Send + Sync + 'static,
    EF: Field + BasedVectorSpace<F>,
>(
    pol_0: &[PF],
    w_folded: &[EFP],
    r1: EF,
    r2: EF,
    sum: EF,
    compute_quad: bool,
    decompose: impl Fn(EFP) -> Vec<EF>,
) -> (Option<DensePolynomial<EF>>, ArenaVec<EFP>, ArenaVec<EFP>) {
    assert_eq!(DIM, EF::DIMENSION);
    let n = pol_0.len();
    assert!(n.is_power_of_two());
    assert!(n >= 8);
    let half = n / 2;
    let q = half / 2;
    assert_eq!(w_folded.len(), half);
    let e = q / 2;

    let r1_packed = EFP::from(r1);
    let r2_packed = EFP::from(r2);
    let r12_packed = EFP::from(r1 * r2);

    let mut e2 = unsafe { ArenaVec::<EFP>::uninitialized(q) };
    let mut w2 = unsafe { ArenaVec::<EFP>::uninitialized(q) };
    let e2_ptr = parallel::SendPtr(e2.as_mut_ptr());
    let w2_ptr = parallel::SendPtr(w2.as_mut_ptr());

    // E''[j] = a_j + r1 b_j + r2 da_j + r1 r2 db_j, from P only.
    let comb = |j: usize| -> EFP {
        let a = pol_0[j];
        let b = pol_0[half + j] - pol_0[j];
        let da = pol_0[q + j] - pol_0[j];
        let db = (pol_0[half + q + j] - pol_0[q + j]) - b;
        r1_packed * b + (r2_packed * da + (r12_packed * db + a))
    };

    let (c0_packed, c2_packed) = parallel::map_reduce(
        e,
        || (EFP::ZERO, EFP::ZERO),
        |i| {
            let e_lo = comb(i);
            let e_hi = comb(e + i);
            let w_lo = r2_packed * (w_folded[q + i] - w_folded[i]) + w_folded[i];
            let w_hi = r2_packed * (w_folded[q + e + i] - w_folded[e + i]) + w_folded[e + i];
            unsafe {
                *e2_ptr.add(i) = e_lo;
                *e2_ptr.add(e + i) = e_hi;
                *w2_ptr.add(i) = w_lo;
                *w2_ptr.add(e + i) = w_hi;
            }
            if compute_quad {
                (w_lo * e_lo, (w_hi - w_lo) * (e_hi - e_lo))
            } else {
                (EFP::ZERO, EFP::ZERO)
            }
        },
        |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
    );

    let poly = if compute_quad {
        let c0 = decompose(c0_packed).into_iter().sum::<EF>();
        let c2 = decompose(c2_packed).into_iter().sum::<EF>();
        let c1 = sum - c0.double() - c2;
        Some(DensePolynomial::new(vec![c0, c1, c2]))
    } else {
        None
    };

    (poly, e2, w2)
}

pub fn compute_product_sumcheck_polynomial<
    F: PrimeCharacteristicRing + Copy + Send + Sync,
    EF: Field,
    EFPacking: Algebra<F> + Copy + Send + Sync,
>(
    pol_0: &[F],         // evals
    pol_1: &[EFPacking], // weights
    sum: EF,
    decompose: impl Fn(EFPacking) -> Vec<EF>,
) -> DensePolynomial<EF> {
    let n = pol_0.len();
    assert_eq!(n, pol_1.len());
    assert!(n.is_power_of_two());

    let num_elements = n;

    let (c0_packed, c2_packed) = if num_elements < PARALLEL_THRESHOLD {
        pol_0[..n / 2]
            .iter()
            .zip(pol_0[n / 2..].iter())
            .zip(pol_1[..n / 2].iter().zip(pol_1[n / 2..].iter()))
            .map(sumcheck_quadratic)
            .fold((EFPacking::ZERO, EFPacking::ZERO), |(a0, a2), (b0, b2)| {
                (a0 + b0, a2 + b2)
            })
    } else {
        let half = n / 2;
        parallel::map_reduce(
            half,
            || (EFPacking::ZERO, EFPacking::ZERO),
            |i| sumcheck_quadratic(((&pol_0[i], &pol_0[half + i]), (&pol_1[i], &pol_1[half + i]))),
            |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
        )
    };

    let c0 = decompose(c0_packed).into_iter().sum::<EF>();
    let c2 = decompose(c2_packed).into_iter().sum::<EF>();
    let c1 = sum - c0.double() - c2;

    DensePolynomial::new(vec![c0, c1, c2])
}

// Generic over PrimeField64 (Goldilocks and Goldilocks both qualify). The Goldilocks-specific
// delayed u128/i128 accumulation path is retained as a specialization candidate for a future
// pass — see `crates/backend/goldilocks/README.md`.
pub fn compute_product_sumcheck_polynomial_base_ext_packed<
    const DIM: usize,
    F: PrimeField64,
    PF: PackedField<Scalar = F>,
    EFP: BasedVectorSpace<PF> + Copy + Send + Sync,
    EF: Field + BasedVectorSpace<F>,
>(
    pol_0: &[PF],
    pol_1: &[EFP],
    sum: EF,
) -> DensePolynomial<EF> {
    assert_eq!(DIM, EF::DIMENSION);
    let n = pol_0.len();
    assert_eq!(n, pol_1.len());
    assert!(n.is_power_of_two());
    let half = n / 2;

    let chunk_size = 1024;

    let n_chunks = half.div_ceil(chunk_size);
    // Deferred-reduction packed accumulation (lazy-accumulator protocol, see
    // PrimeCharacteristicRing::unreduced_mul): each chunk keeps 2*DIM unreduced
    // accumulators and reduces once at chunk exit. All terms are raw products
    // added positively, so n_sub = 0. Chunk length 1024 <= 2^20 honors the
    // protocol bound (1 term per accumulator per iteration).
    let (c0_acc, c2_acc) = parallel::map_reduce(
        n_chunks,
        || ([PF::ZERO; DIM], [PF::ZERO; DIM]),
        |chunk| {
            let start = chunk * chunk_size;
            let end = (start + chunk_size).min(half);
            let b_lo = &pol_0[start..end];
            let b_hi = &pol_0[half + start..half + end];
            let e_lo = &pol_1[start..end];
            let e_hi = &pol_1[half + start..half + end];
            // Two passes: 6 accumulators x 4 zmm = 24 spills; split to 3 x 4 = 12.
            let mut c0_lazy: [[PF; 4]; DIM] = core::array::from_fn(|_| PF::lazy_acc_zero());
            for i in 0..b_lo.len() {
                let x0 = b_lo[i];
                let y0_coords = e_lo[i].as_basis_coefficients_slice();
                for j in 0..DIM {
                    c0_lazy[j] = PF::lazy_acc_add(c0_lazy[j], PF::unreduced_mul(y0_coords[j], x0));
                }
            }
            let mut c2_lazy: [[PF; 4]; DIM] = core::array::from_fn(|_| PF::lazy_acc_zero());
            for i in 0..b_lo.len() {
                let dx = b_hi[i] - b_lo[i];
                let y0_coords = e_lo[i].as_basis_coefficients_slice();
                let y1_coords = e_hi[i].as_basis_coefficients_slice();
                for j in 0..DIM {
                    let dy = y1_coords[j] - y0_coords[j];
                    c2_lazy[j] = PF::lazy_acc_add(c2_lazy[j], PF::unreduced_mul(dy, dx));
                }
            }
            (
                core::array::from_fn(|j| PF::lazy_acc_finish(c0_lazy[j], 0)),
                core::array::from_fn(|j| PF::lazy_acc_finish(c2_lazy[j], 0)),
            )
        },
        |(mut a0, mut a2): ([PF; DIM], [PF; DIM]), (b0, b2): ([PF; DIM], [PF; DIM])| {
            for j in 0..DIM {
                a0[j] += b0[j];
                a2[j] += b2[j];
            }
            (a0, a2)
        },
    );

    // Horizontal lane sum once at the very end.
    let lane_sum = |p: PF| {
        let mut s = F::ZERO;
        for &v in p.as_slice() {
            s += v;
        }
        s
    };
    let c0 = EF::from_basis_coefficients_fn(|j| lane_sum(c0_acc[j]));
    let c2 = EF::from_basis_coefficients_fn(|j| lane_sum(c2_acc[j]));
    let c1 = sum - c0.double() - c2;

    DensePolynomial::new(vec![c0, c1, c2])
}

pub fn fold_and_compute_product_sumcheck_polynomial<
    F: PrimeCharacteristicRing + Copy + Send + Sync + 'static,
    EF: Field,
    EFPacking: Algebra<F> + From<EF> + Copy + Send + Sync + 'static,
>(
    pol_0: &[F],         // evals
    pol_1: &[EFPacking], // weights
    prev_folding_factor: EF,
    sum: EF,
    decompose: impl Fn(EFPacking) -> Vec<EF>,
) -> (DensePolynomial<EF>, Vec<ArenaVec<EFPacking>>) {
    let n = pol_0.len();
    assert_eq!(n, pol_1.len());
    assert!(n.is_power_of_two());
    let prev_folding_factor_packed = EFPacking::from(prev_folding_factor);

    let mut pol_0_folded = unsafe { ArenaVec::<EFPacking>::uninitialized(n / 2) };
    let mut pol_1_folded = unsafe { ArenaVec::<EFPacking>::uninitialized(n / 2) };

    #[allow(clippy::type_complexity)]
    let process_element = |(p0_prev, p0_f): (((&F, &F), (&F, &F)), (&mut EFPacking, &mut EFPacking)),
                           (p1_prev, p1_f): (
        ((&EFPacking, &EFPacking), (&EFPacking, &EFPacking)),
        (&mut EFPacking, &mut EFPacking),
    )| {
        let diff_0 = *p0_prev.1.0 - *p0_prev.0.0;
        let diff_1 = *p0_prev.1.1 - *p0_prev.0.1;
        let x_0 = prev_folding_factor_packed * diff_0 + *p0_prev.0.0;
        let x_1 = prev_folding_factor_packed * diff_1 + *p0_prev.0.1;
        *p0_f.0 = x_0;
        *p0_f.1 = x_1;

        let y_0 = prev_folding_factor_packed * (*p1_prev.1.0 - *p1_prev.0.0) + *p1_prev.0.0;
        let y_1 = prev_folding_factor_packed * (*p1_prev.1.1 - *p1_prev.0.1) + *p1_prev.0.1;
        *p1_f.0 = y_0;
        *p1_f.1 = y_1;

        sumcheck_quadratic(((&x_0, &x_1), (&y_0, &y_1)))
    };

    let (c0_packed, c2_packed) = if n < PARALLEL_THRESHOLD {
        zip_fold_2(pol_0, &mut pol_0_folded)
            .zip(zip_fold_2(pol_1, &mut pol_1_folded))
            .map(|(p0, p1)| process_element(p0, p1))
            .fold((EFPacking::ZERO, EFPacking::ZERO), |(a0, a2), (b0, b2)| {
                (a0 + b0, a2 + b2)
            })
    } else {
        let quarter = n / 4;
        let p0f = parallel::SendPtr(pol_0_folded.as_mut_ptr());
        let p1f = parallel::SendPtr(pol_1_folded.as_mut_ptr());
        parallel::map_reduce(
            quarter,
            || (EFPacking::ZERO, EFPacking::ZERO),
            |i| {
                let diff_0 = pol_0[2 * quarter + i] - pol_0[i];
                let diff_1 = pol_0[3 * quarter + i] - pol_0[quarter + i];
                let x_0 = prev_folding_factor_packed * diff_0 + pol_0[i];
                let x_1 = prev_folding_factor_packed * diff_1 + pol_0[quarter + i];

                let y_0 = prev_folding_factor_packed * (pol_1[2 * quarter + i] - pol_1[i]) + pol_1[i];
                let y_1 =
                    prev_folding_factor_packed * (pol_1[3 * quarter + i] - pol_1[quarter + i]) + pol_1[quarter + i];

                unsafe {
                    *p0f.add(i) = x_0;
                    *p0f.add(quarter + i) = x_1;
                    *p1f.add(i) = y_0;
                    *p1f.add(quarter + i) = y_1;
                }

                sumcheck_quadratic(((&x_0, &x_1), (&y_0, &y_1)))
            },
            |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
        )
    };

    let c0 = decompose(c0_packed).into_iter().sum::<EF>();
    let c2 = decompose(c2_packed).into_iter().sum::<EF>();
    let c1 = sum - c0.double() - c2;

    (DensePolynomial::new(vec![c0, c1, c2]), vec![pol_0_folded, pol_1_folded])
}

#[inline(always)]
pub fn sumcheck_quadratic<F, EF>(((&x_0, &x_1), (&y_0, &y_1)): ((&F, &F), (&EF, &EF))) -> (EF, EF)
where
    F: PrimeCharacteristicRing + Copy,
    EF: Algebra<F> + Copy,
{
    let constant = y_0 * x_0;
    let quadratic = (y_1 - y_0) * (x_1 - x_0);
    (constant, quadratic)
}
