use fiat_shamir::*;
use field::*;
use poly::*;
use tracing::instrument;
use zk_alloc::ArenaVec;

use crate::{SumcheckComputation, packing_unpack_sum, sumcheck_prove_many_rounds};

#[derive(Debug)]
pub struct ProductComputation;

impl<EF: KoalaBearExtension> SumcheckComputation<EF> for ProductComputation {
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
pub fn run_product_sumcheck<EF: KoalaBearExtension>(
    pol_a: &MleRef<'_, EF>, // evals
    pol_b: &MleRef<'_, EF>, // weights
    prover_state: &mut impl FSProver<EF>,
    mut sum: EF,
    n_rounds: usize,
    pow_bits: usize,
) -> (MultilinearPoint<EF>, EF, MleOwned<EF>, MleOwned<EF>) {
    assert!(n_rounds >= 1);
    let first_sumcheck_poly = match (pol_a, pol_b) {
        (MleRef::BasePacked(evals), MleRef::ExtensionPacked(weights)) => {
            compute_product_sumcheck_polynomial(evals, weights, sum, |e| (e).to_ext_lanes().collect())
        }
        (MleRef::ExtensionPacked(evals), MleRef::ExtensionPacked(weights)) => {
            compute_product_sumcheck_polynomial(evals, weights, sum, |e| (e).to_ext_lanes().collect())
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

    run_product_sumcheck_from_round1(pol_a, pol_b, prover_state, r1, sum, n_rounds, pow_bits)
}

/// Rounds 1+ of the product sumcheck, for callers that computed round 0 themselves.
/// `sum` is the running sum after binding `r1`.
pub fn run_product_sumcheck_from_round1<EF: KoalaBearExtension>(
    pol_a: &MleRef<'_, EF>, // evals
    pol_b: &MleRef<'_, EF>, // weights
    prover_state: &mut impl FSProver<EF>,
    r1: EF,
    mut sum: EF,
    n_rounds: usize,
    pow_bits: usize,
) -> (MultilinearPoint<EF>, EF, MleOwned<EF>, MleOwned<EF>) {
    if n_rounds == 1 {
        return (MultilinearPoint(vec![r1]), sum, pol_a.fold(r1), pol_b.fold(r1));
    }

    let (second_sumcheck_poly, folded) = match (pol_a, pol_b) {
        (MleRef::BasePacked(evals), MleRef::ExtensionPacked(weights)) => {
            let (second_sumcheck_poly, folded) =
                fold_and_compute_product_sumcheck_polynomial(evals, weights, r1, sum, |e| (e).to_ext_lanes().collect());
            (second_sumcheck_poly, MleGroupOwned::ExtensionPacked(folded))
        }
        (MleRef::ExtensionPacked(evals), MleRef::ExtensionPacked(weights)) => {
            let (second_sumcheck_poly, folded) =
                fold_and_compute_product_sumcheck_polynomial(evals, weights, r1, sum, |e| (e).to_ext_lanes().collect());
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

/// Algo 3 of https://eprint.iacr.org/2024/1046.pdf. Requires n_rounds >= 3.
#[allow(clippy::too_many_arguments)]
pub fn run_product_sumcheck_from_round1_delayed<EF: KoalaBearExtension>(
    evals: &[PFPacking<EF>],
    weights: &[EFPacking<EF>],
    prover_state: &mut impl FSProver<EF>,
    r1: EF,
    sum_after_r1: EF,
    n_rounds: usize,
    pow_bits: usize,
) -> (MultilinearPoint<EF>, EF, MleOwned<EF>, MleOwned<EF>) {
    assert!(n_rounds >= 3);
    let n = evals.len();
    assert_eq!(n, weights.len());
    let q = n / 4;
    type Quad<EF> = (EFPacking<EF>, EFPacking<EF>, EFPacking<EF>, EFPacking<EF>);
    let quad_add = |(a, b, c, d): Quad<EF>, (e, f, g, h): Quad<EF>| (a + e, b + f, c + g, d + h);
    let make_poly = |(p0, p1, s0, s1): Quad<EF>, sum: EF| {
        let c0 = packing_unpack_sum::<EF>(p0) + r1 * packing_unpack_sum::<EF>(p1);
        let c2 = packing_unpack_sum::<EF>(s0) + r1 * packing_unpack_sum::<EF>(s1);
        let c1 = sum - c0.double() - c2;
        DensePolynomial::new(vec![c0, c1, c2])
    };

    // Pass A: fold weights at r1, round-2 poly via 2-slice evals.
    let r1p = EFPacking::<EF>::from(r1);
    let mut w_folded = unsafe { ArenaVec::<EFPacking<EF>>::uninitialized(n / 2) };
    let wf = parallel::SendPtr(w_folded.as_mut_ptr());
    let partials = parallel::map_reduce(
        q,
        Default::default,
        |i| {
            let y_0 = r1p * (weights[2 * q + i] - weights[i]) + weights[i];
            let y_1 = r1p * (weights[3 * q + i] - weights[q + i]) + weights[q + i];
            unsafe {
                *wf.add(i) = y_0;
                *wf.add(q + i) = y_1;
            }
            // s0(j) = e[j], s1(j) = e[n/2+j] − e[j]
            let s0_lo = evals[i];
            let s1_lo = evals[2 * q + i] - evals[i];
            let ds0 = evals[q + i] - evals[i];
            let ds1 = (evals[3 * q + i] - evals[q + i]) - s1_lo;
            let d = y_1 - y_0;
            (y_0 * s0_lo, y_0 * s1_lo, d * ds0, d * ds1)
        },
        quad_add,
    );
    let second_poly = make_poly(partials, sum_after_r1);

    prover_state.add_sumcheck_polynomial(&second_poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r2: EF = prover_state.sample();
    let sum_after_r2 = second_poly.evaluate(r2);

    // Pass B: fold weights at r2, collapse evals at (r1, r2) to EFP, round-3 poly.
    let q2 = q / 2;
    let r2p = EFPacking::<EF>::from(r2);
    let mut w_folded2 = unsafe { ArenaVec::<EFPacking<EF>>::uninitialized(q) };
    let mut x_folded2 = unsafe { ArenaVec::<EFPacking<EF>>::uninitialized(q) };
    let wf2 = parallel::SendPtr(w_folded2.as_mut_ptr());
    let xf2 = parallel::SendPtr(x_folded2.as_mut_ptr());
    let partials = parallel::map_reduce(
        q2,
        Default::default,
        |i| {
            // t0(m) = s0(m) + r2·(s0(q+m) − s0(m)), same for t1; pair is (i, q2+i).
            let (a, b) = (i, q2 + i);
            let s1_a = evals[2 * q + a] - evals[a];
            let s1_b = evals[2 * q + b] - evals[b];
            let t0_lo = r2p * (evals[q + a] - evals[a]) + evals[a];
            let t1_lo = r2p * ((evals[3 * q + a] - evals[q + a]) - s1_a) + s1_a;
            let t0_hi = r2p * (evals[q + b] - evals[b]) + evals[b];
            let t1_hi = r2p * ((evals[3 * q + b] - evals[q + b]) - s1_b) + s1_b;
            let y_lo = r2p * (w_folded[q + a] - w_folded[a]) + w_folded[a];
            let y_hi = r2p * (w_folded[q + b] - w_folded[b]) + w_folded[b];
            let x_lo = t0_lo + r1p * t1_lo;
            let x_hi = t0_hi + r1p * t1_hi;
            unsafe {
                *wf2.add(a) = y_lo;
                *wf2.add(b) = y_hi;
                *xf2.add(a) = x_lo;
                *xf2.add(b) = x_hi;
            }
            let d = y_hi - y_lo;
            (y_lo * t0_lo, y_lo * t1_lo, d * (t0_hi - t0_lo), d * (t1_hi - t1_lo))
        },
        quad_add,
    );
    let third_poly = make_poly(partials, sum_after_r2);

    prover_state.add_sumcheck_polynomial(&third_poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r3: EF = prover_state.sample();
    let sum_after_r3 = third_poly.evaluate(r3);

    let (mut challenges, folds, sum) = sumcheck_prove_many_rounds(
        MleGroupOwned::ExtensionPacked(vec![x_folded2, w_folded2]),
        Some(r3),
        &ProductComputation {},
        &vec![],
        None,
        prover_state,
        sum_after_r3,
        None,
        n_rounds - 3,
        false,
        pow_bits,
    );

    challenges.splice(0..0, [r1, r2, r3]);
    let [pol_a, pol_b] = folds.split().try_into().unwrap();
    (challenges, sum, pol_a, pol_b)
}
