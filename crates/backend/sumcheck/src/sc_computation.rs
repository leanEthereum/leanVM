use crate::*;
use air::*;
use field::*;
use poly::*;
use std::any::TypeId;
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub};
use zk_alloc::ArenaVec;

fn add_assign_vec<T: AddAssign>(mut a: Vec<T>, b: Vec<T>) -> Vec<T> {
    for (x, y) in a.iter_mut().zip(b) {
        *x += y;
    }
    a
}

pub trait SumcheckComputation<EF: ExtensionField<PF<EF>>>: Sync {
    type ExtraData: Send + Sync + 'static;

    fn degree(&self) -> usize;
    fn eval_base(&self, point_f: &[PF<EF>], extra_data: &Self::ExtraData) -> EF;
    fn eval_extension(&self, point_f: &[EF], extra_data: &Self::ExtraData) -> EF;
    fn eval_packed_base(&self, point_f: &[PFPacking<EF>], extra_data: &Self::ExtraData) -> EFPacking<EF>;
    fn eval_packed_extension(&self, point_f: &[EFPacking<EF>], extra_data: &Self::ExtraData) -> EFPacking<EF>;
}

macro_rules! impl_air_eval {
    ($self:expr, $point_f:expr, $extra_data:expr, $folder_ty:ident) => {{
        let n_cols = $self.n_columns();
        let mut folder = $folder_ty::new(&$point_f[..n_cols], &$point_f[n_cols..], $extra_data);
        Air::eval($self, &mut folder, $extra_data);
        folder.accumulator
    }};
}

impl<EF, A> SumcheckComputation<EF> for A
where
    EF: ExtensionField<PF<EF>>,
    A: Send + Sync + Air,
    A::ExtraData: AlphaPowers<EF>,
{
    type ExtraData = A::ExtraData;

    #[inline(always)]
    fn eval_base(&self, point_f: &[PF<EF>], extra_data: &Self::ExtraData) -> EF {
        impl_air_eval!(self, point_f, extra_data, ConstraintFolder)
    }

    #[inline(always)]
    fn eval_extension(&self, point_f: &[EF], extra_data: &Self::ExtraData) -> EF {
        impl_air_eval!(self, point_f, extra_data, ConstraintFolder)
    }

    #[inline(always)]
    fn eval_packed_base(&self, point_f: &[PFPacking<EF>], extra_data: &Self::ExtraData) -> EFPacking<EF> {
        impl_air_eval!(self, point_f, extra_data, ConstraintFolderPacked)
    }

    #[inline(always)]
    fn eval_packed_extension(&self, point_f: &[EFPacking<EF>], extra_data: &Self::ExtraData) -> EFPacking<EF> {
        impl_air_eval!(self, point_f, extra_data, ConstraintFolderPacked)
    }

    fn degree(&self) -> usize {
        self.degree_air()
    }
}

fn build_evals<EF: ExtensionField<PF<EF>>>(
    sums: impl IntoIterator<Item = EF>,
    missing_mul_factor: Option<EF>,
) -> Vec<EF> {
    sums.into_iter()
        .map(|sum| missing_mul_factor.map_or(sum, |f| sum * f))
        .collect()
}

#[inline(always)]
fn poly_to_evals<EF: ExtensionField<PF<EF>>>(poly: &DensePolynomial<EF>) -> Vec<EF> {
    vec![poly.coeffs[0], poly.evaluate(EF::TWO)]
}

#[inline(always)]
pub(crate) fn identity_decompose<EF: Field>(e: EF) -> Vec<EF> {
    vec![e]
}

#[inline(always)]
pub(crate) fn packing_decompose<EF: ExtensionField<PF<EF>>>(e: EFPacking<EF>) -> Vec<EF> {
    EFPacking::<EF>::to_ext_iter([e]).collect()
}

#[inline(always)]
fn packing_unpack_sum<EF: ExtensionField<PF<EF>>>(s: EFPacking<EF>) -> EF {
    EFPacking::<EF>::to_ext_iter([s]).sum::<EF>()
}

fn handle_product_computation<'a, EF: ExtensionField<PF<EF>>>(group: &MleGroupRef<'a, EF>, sum: EF) -> Vec<EF> {
    let poly = match group {
        MleGroupRef::Extension(multilinears) => {
            compute_product_sumcheck_polynomial(multilinears[0], multilinears[1], sum, identity_decompose)
        }
        MleGroupRef::ExtensionPacked(multilinears) => {
            compute_product_sumcheck_polynomial(multilinears[0], multilinears[1], sum, packing_decompose)
        }
        _ => unimplemented!(),
    };
    poly_to_evals(&poly)
}

#[allow(clippy::type_complexity)]
fn handle_product_computation_with_fold<'a, EF: ExtensionField<PF<EF>>>(
    group: &MleGroupRef<'a, EF>,
    prev_folding_factor: EF,
    sum: EF,
) -> (Vec<EF>, MleGroupOwned<EF>) {
    let (poly, folded_f) = match group {
        MleGroupRef::Extension(multilinears) => {
            let (poly, folded) = fold_and_compute_product_sumcheck_polynomial(
                multilinears[0],
                multilinears[1],
                prev_folding_factor,
                sum,
                identity_decompose,
            );
            (poly, MleGroupOwned::Extension(folded))
        }
        MleGroupRef::ExtensionPacked(multilinears) => {
            let (poly, folded) = fold_and_compute_product_sumcheck_polynomial(
                multilinears[0],
                multilinears[1],
                prev_folding_factor,
                sum,
                packing_decompose,
            );
            (poly, MleGroupOwned::ExtensionPacked(folded))
        }
        _ => unimplemented!(),
    };
    (poly_to_evals(&poly), folded_f)
}

pub struct SumcheckComputeParams<'a, EF: ExtensionField<PF<EF>>, SC: SumcheckComputation<EF>> {
    pub split_eq: Option<&'a SplitEq<EF>>,
    pub computation: &'a SC,
    pub extra_data: &'a SC::ExtraData,
    pub missing_mul_factor: Option<EF>,
    pub sum: EF,
}

pub fn sumcheck_compute<'a, EF: ExtensionField<PF<EF>>, SC>(
    group: &MleGroupRef<'a, EF>,
    params: SumcheckComputeParams<'a, EF, SC>,
    degree: usize,
) -> Vec<EF>
where
    SC: SumcheckComputation<EF> + 'static,
    SC::ExtraData: AlphaPowers<EF>,
{
    let SumcheckComputeParams {
        split_eq,
        computation,
        extra_data,
        missing_mul_factor,
        sum,
    } = params;

    let fold_size = 1 << (group.n_vars() - 1);
    let packed_fold_size = if group.is_packed() {
        fold_size / packing_width::<EF>()
    } else {
        fold_size
    };

    // Handle ProductComputation special case
    if TypeId::of::<SC>() == TypeId::of::<ProductComputation>() && split_eq.is_none() {
        assert!(missing_mul_factor.is_none());
        assert!(extra_data.alpha_powers().is_empty());
        assert_eq!(group.n_columns(), 2);
        return handle_product_computation(group, sum);
    }

    match group {
        MleGroupRef::ExtensionPacked(multilinears) if split_eq.is_some() => {
            assert!(!split_eq.unwrap().is_remainder_mode());
            sumcheck_compute_with_split_eq(
                multilinears,
                degree,
                split_eq.unwrap(),
                computation,
                extra_data,
                missing_mul_factor,
                packed_fold_size,
                |sc, pf, ed| sc.eval_packed_extension(pf, ed),
                packing_unpack_sum,
            )
        }
        MleGroupRef::ExtensionPacked(multilinears) => sumcheck_compute_core(
            multilinears,
            degree,
            |i| split_eq.map(|seq| seq.get_packed(i)),
            computation,
            extra_data,
            missing_mul_factor,
            packed_fold_size,
            |sc, pf, ed| sc.eval_packed_extension(pf, ed),
            packing_unpack_sum,
        ),
        MleGroupRef::BasePacked(multilinears) => {
            if let Some(seq) = split_eq {
                assert!(
                    !seq.is_remainder_mode(),
                    "BasePacked sumcheck received SplitEq in remainder mode"
                );
            }
            sumcheck_compute_core(
                multilinears,
                degree,
                |i| split_eq.map(|seq| seq.get_packed(i)),
                computation,
                extra_data,
                missing_mul_factor,
                packed_fold_size,
                |sc, pf, ed| sc.eval_packed_base(pf, ed),
                packing_unpack_sum,
            )
        }
        MleGroupRef::Base(multilinears) => sumcheck_compute_core(
            multilinears,
            degree,
            |i| split_eq.map(|seq| seq.get_unpacked(i)),
            computation,
            extra_data,
            missing_mul_factor,
            fold_size,
            |sc, pf, ed| sc.eval_base(pf, ed),
            |s| s,
        ),
        MleGroupRef::Extension(multilinears) => sumcheck_compute_core(
            multilinears,
            degree,
            |i| split_eq.map(|seq| seq.get_unpacked(i)),
            computation,
            extra_data,
            missing_mul_factor,
            fold_size,
            |sc, pf, ed| sc.eval_extension(pf, ed),
            |s| s,
        ),
    }
}

#[allow(clippy::type_complexity)]
pub fn fold_and_sumcheck_compute<'a, EF: ExtensionField<PF<EF>>, SC>(
    prev_folding_factor: EF,
    group: &MleGroupRef<'a, EF>,
    params: SumcheckComputeParams<'a, EF, SC>,
    degree: usize,
) -> (Vec<EF>, MleGroupOwned<EF>)
where
    SC: SumcheckComputation<EF> + 'static,
    SC::ExtraData: AlphaPowers<EF>,
{
    let SumcheckComputeParams {
        split_eq,
        computation,
        extra_data,
        missing_mul_factor,
        sum,
    } = params;

    let fold_size = 1 << (group.n_vars() - 2);
    let compute_fold_size = if group.is_packed() {
        fold_size / packing_width::<EF>()
    } else {
        fold_size
    };

    // Handle ProductComputation special case
    if TypeId::of::<SC>() == TypeId::of::<ProductComputation>() && split_eq.is_none() {
        assert!(missing_mul_factor.is_none());
        assert!(extra_data.alpha_powers().is_empty());
        assert_eq!(group.n_columns(), 2);
        return handle_product_computation_with_fold(group, prev_folding_factor, sum);
    }

    match group {
        MleGroupRef::ExtensionPacked(multilinears) if split_eq.is_some() => {
            assert!(!split_eq.unwrap().is_remainder_mode());
            let prev_folded_size = multilinears[0].len() / 2;
            sumcheck_fold_and_compute_with_split_eq(
                multilinears,
                degree,
                split_eq.unwrap(),
                computation,
                extra_data,
                missing_mul_factor,
                compute_fold_size,
                |m, id| (m[id + prev_folded_size] - m[id]) * prev_folding_factor + m[id],
                |sc, pf, ed| sc.eval_packed_extension(pf, ed),
                packing_unpack_sum,
                MleGroupOwned::ExtensionPacked,
            )
        }
        MleGroupRef::ExtensionPacked(multilinears) => {
            let prev_folded_size = multilinears[0].len() / 2;
            sumcheck_fold_and_compute_core(
                multilinears,
                degree,
                |i| split_eq.map(|seq| seq.get_packed(i)),
                computation,
                extra_data,
                missing_mul_factor,
                compute_fold_size,
                |m, id| (m[id + prev_folded_size] - m[id]) * prev_folding_factor + m[id],
                |sc, pf, ed| sc.eval_packed_extension(pf, ed),
                packing_unpack_sum,
                MleGroupOwned::ExtensionPacked,
            )
        }
        MleGroupRef::BasePacked(multilinears) => {
            if let Some(seq) = split_eq {
                assert!(
                    !seq.is_remainder_mode(),
                    "BasePacked fold-and-compute received SplitEq in remainder mode"
                );
            }
            let prev_folded_size = multilinears[0].len() / 2;
            let prev_folding_factor_packed = EFPacking::<EF>::from(prev_folding_factor);
            sumcheck_fold_and_compute_core(
                multilinears,
                degree,
                |i| split_eq.map(|seq| seq.get_packed(i)),
                computation,
                extra_data,
                missing_mul_factor,
                compute_fold_size,
                |m, id| prev_folding_factor_packed * (m[id + prev_folded_size] - m[id]) + m[id],
                |sc, pf, ed| sc.eval_packed_extension(pf, ed),
                packing_unpack_sum,
                MleGroupOwned::ExtensionPacked,
            )
        }
        MleGroupRef::Base(multilinears) => {
            let prev_folded_size = multilinears[0].len() / 2;
            sumcheck_fold_and_compute_core(
                multilinears,
                degree,
                |i| split_eq.map(|seq| seq.get_unpacked(i)),
                computation,
                extra_data,
                missing_mul_factor,
                compute_fold_size,
                |m, id| prev_folding_factor * (m[id + prev_folded_size] - m[id]) + m[id],
                |sc, pf, ed| sc.eval_extension(pf, ed),
                |s| s,
                MleGroupOwned::Extension,
            )
        }
        MleGroupRef::Extension(multilinears) => {
            let prev_folded_size = multilinears[0].len() / 2;
            sumcheck_fold_and_compute_core(
                multilinears,
                degree,
                |i| split_eq.map(|seq| seq.get_unpacked(i)),
                computation,
                extra_data,
                missing_mul_factor,
                compute_fold_size,
                |m, id| (m[id + prev_folded_size] - m[id]) * prev_folding_factor + m[id],
                |sc, pf, ed| sc.eval_extension(pf, ed),
                |s| s,
                MleGroupOwned::Extension,
            )
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn sumcheck_compute_core<EF, IF, EFT, SC>(
    multilinears: &[&[IF]],
    degree: usize,
    eq_at: impl Fn(usize) -> Option<EFT> + Sync + Send,
    computation: &SC,
    extra_data: &SC::ExtraData,
    missing_mul_factor: Option<EF>,
    fold_size: usize,
    eval_fn: impl Fn(&SC, &[IF], &SC::ExtraData) -> EFT + Sync + Send,
    unpack_sum: impl Fn(EFT) -> EF,
) -> Vec<EF>
where
    EF: ExtensionField<PF<EF>>,
    IF: Copy + Sub<Output = IF> + Add<Output = IF> + AddAssign + Send + Sync,
    EFT: PrimeCharacteristicRing
        + Copy
        + Sub<Output = EFT>
        + Add<Output = EFT>
        + Send
        + Sync
        + Mul<EFT, Output = EFT>
        + MulAssign,
    SC: SumcheckComputation<EF>,
{
    let n_mult = multilinears.len();
    let sums = parallel::map_reduce_with_state(
        fold_size,
        || (Vec::<[IF; 3]>::with_capacity(n_mult), Vec::<IF>::with_capacity(n_mult)),
        || EFT::zero_vec(degree),
        |(rows, point), acc, i| {
            let eq_val = eq_at(i);

            rows.clear();
            rows.extend(multilinears.iter().map(|m| {
                let lo = m[i];
                let hi = m[i + fold_size];
                [lo, hi - lo, hi]
            }));

            // z = 0
            point.clear();
            point.extend(rows.iter().map(|row| row[0]));
            let mut eval_0 = eval_fn(computation, point, extra_data);
            if let Some(eq) = eq_val {
                eval_0 *= eq;
            }
            acc[0] += eval_0;

            // z = 2, 3, ...
            for acc_d in acc.iter_mut().skip(1) {
                for [_, diff_hi_lo, running] in rows.iter_mut() {
                    *running += *diff_hi_lo;
                }
                point.clear();
                point.extend(rows.iter().map(|row| row[2]));
                let mut eval = eval_fn(computation, point, extra_data);
                if let Some(eq) = eq_val {
                    eval *= eq;
                }
                *acc_d += eval;
            }
        },
        add_assign_vec,
    );
    let unpacked_sums = sums.into_iter().map(&unpack_sum);
    build_evals(unpacked_sums, missing_mul_factor)
}

#[allow(clippy::too_many_arguments)]
#[allow(clippy::type_complexity)]
fn sumcheck_fold_and_compute_core<EF, IF, FT, SC>(
    multilinears: &[&[IF]],
    degree: usize,
    eq_at: impl Fn(usize) -> Option<FT> + Sync + Send,
    computation: &SC,
    extra_data: &SC::ExtraData,
    missing_mul_factor: Option<EF>,
    compute_fold_size: usize,
    fold_f: impl Fn(&[IF], usize) -> FT + Sync + Send,
    eval_fn: impl Fn(&SC, &[FT], &SC::ExtraData) -> FT + Sync + Send,
    unpack_sum: impl Fn(FT) -> EF,
    wrap_f: impl FnOnce(Vec<ArenaVec<FT>>) -> MleGroupOwned<EF>,
) -> (Vec<EF>, MleGroupOwned<EF>)
where
    EF: ExtensionField<PF<EF>>,
    IF: Copy + Send + Sync,
    FT: PrimeCharacteristicRing + Copy + Sub<Output = FT> + Add<Output = FT> + Send + Sync,
    SC: SumcheckComputation<EF>,
{
    let prev_folded_size = 2 * compute_fold_size;

    let folded_f: Vec<ArenaVec<FT>> = (0..multilinears.len())
        .map(|_| unsafe { ArenaVec::<FT>::zeroed(prev_folded_size) })
        .collect();

    let n_mult = multilinears.len();
    let sums = parallel::map_reduce_with_state(
        compute_fold_size,
        || (Vec::<[FT; 3]>::with_capacity(n_mult), Vec::<FT>::with_capacity(n_mult)),
        || FT::zero_vec(degree),
        |(rows_f, point), acc, i| {
            let eq_mle_eval = eq_at(i);

            rows_f.clear();
            rows_f.extend(multilinears.iter().enumerate().map(|(j, m)| {
                let lo = fold_f(m, i);
                let hi = fold_f(m, i + compute_fold_size);
                unsafe {
                    let ptr = folded_f[j].as_ptr() as *mut FT;
                    *ptr.add(i) = lo;
                    *ptr.add(i + compute_fold_size) = hi;
                }
                [lo, hi - lo, hi]
            }));

            // z = 0
            point.clear();
            point.extend(rows_f.iter().map(|row| row[0]));
            let mut eval_0 = eval_fn(computation, point, extra_data);
            if let Some(eq) = eq_mle_eval {
                eval_0 *= eq;
            }
            acc[0] += eval_0;

            // z = 2, 3, ...
            for acc_d in acc.iter_mut().skip(1) {
                for [_, diff_hi_lo, running] in rows_f.iter_mut() {
                    *running += *diff_hi_lo;
                }
                point.clear();
                point.extend(rows_f.iter().map(|row| row[2]));
                let mut eval = eval_fn(computation, point, extra_data);
                if let Some(eq) = eq_mle_eval {
                    eval *= eq;
                }
                *acc_d += eval;
            }
        },
        add_assign_vec,
    );
    let unpacked_sums = sums.into_iter().map(&unpack_sum);
    (build_evals(unpacked_sums, missing_mul_factor), wrap_f(folded_f))
}

#[allow(clippy::too_many_arguments, clippy::needless_range_loop)]
fn sumcheck_compute_with_split_eq<EF, SC>(
    multilinears: &[&[EFPacking<EF>]],
    degree: usize,
    split_eq: &SplitEq<EF>,
    computation: &SC,
    extra_data: &SC::ExtraData,
    missing_mul_factor: Option<EF>,
    fold_size: usize,
    eval_fn: impl Fn(&SC, &[EFPacking<EF>], &SC::ExtraData) -> EFPacking<EF> + Sync + Send,
    unpack_sum: impl Fn(EFPacking<EF>) -> EF,
) -> Vec<EF>
where
    EF: ExtensionField<PF<EF>>,
    SC: SumcheckComputation<EF>,
{
    let n_lo = split_eq.n_lo();
    let packed_hi = split_eq.packed_hi();
    let log_packed_hi = split_eq.log_packed_hi;
    let eq_lo = &split_eq.eq_lo;
    let eq_hi = &split_eq.eq_hi_packed;

    let n_mult = multilinears.len();
    let sums: Vec<EFPacking<EF>> = parallel::map_reduce_with_state(
        n_lo,
        || {
            (
                Vec::<[EFPacking<EF>; 3]>::with_capacity(n_mult),
                Vec::<EFPacking<EF>>::with_capacity(n_mult),
                EFPacking::<EF>::zero_vec(degree),
            )
        },
        || EFPacking::<EF>::zero_vec(degree),
        |(rows, point, block_acc), acc, b_lo| {
            let eq_lo_bc = EFPacking::<EF>::from(eq_lo[b_lo]);
            let base = b_lo << log_packed_hi;
            block_acc.iter_mut().for_each(|x| *x = EFPacking::<EF>::ZERO);
            for k in 0..packed_hi {
                let i = base + k;
                let eq_val = eq_hi[k];

                rows.clear();
                rows.extend(multilinears.iter().map(|m| {
                    let lo = m[i];
                    let hi = m[i + fold_size];
                    [lo, hi - lo, hi]
                }));

                // z = 0
                point.clear();
                point.extend(rows.iter().map(|r| r[0]));
                let mut e0 = eval_fn(computation, point, extra_data);
                e0 *= eq_val;
                block_acc[0] += e0;

                // z = 2, 3, ...
                for d in 1..degree {
                    for [_, diff, running] in rows.iter_mut() {
                        *running += *diff;
                    }
                    point.clear();
                    point.extend(rows.iter().map(|r| r[2]));
                    let mut ev = eval_fn(computation, point, extra_data);
                    ev *= eq_val;
                    block_acc[d] += ev;
                }
            }
            for (a, b) in acc.iter_mut().zip(block_acc.iter()) {
                *a += *b * eq_lo_bc;
            }
        },
        add_assign_vec,
    );

    let unpacked = sums.into_iter().map(&unpack_sum);
    build_evals(unpacked, missing_mul_factor)
}

#[allow(clippy::too_many_arguments, clippy::needless_range_loop)]
#[allow(clippy::type_complexity)]
fn sumcheck_fold_and_compute_with_split_eq<EF, IF, SC>(
    multilinears: &[&[IF]],
    degree: usize,
    split_eq: &SplitEq<EF>,
    computation: &SC,
    extra_data: &SC::ExtraData,
    missing_mul_factor: Option<EF>,
    compute_fold_size: usize,
    fold_f: impl Fn(&[IF], usize) -> EFPacking<EF> + Sync + Send,
    eval_fn: impl Fn(&SC, &[EFPacking<EF>], &SC::ExtraData) -> EFPacking<EF> + Sync + Send,
    unpack_sum: impl Fn(EFPacking<EF>) -> EF,
    wrap_f: impl FnOnce(Vec<ArenaVec<EFPacking<EF>>>) -> MleGroupOwned<EF>,
) -> (Vec<EF>, MleGroupOwned<EF>)
where
    EF: ExtensionField<PF<EF>>,
    IF: Copy + Send + Sync,
    SC: SumcheckComputation<EF>,
{
    let prev_folded_size = 2 * compute_fold_size;
    let folded_f: Vec<ArenaVec<EFPacking<EF>>> = (0..multilinears.len())
        .map(|_| unsafe { ArenaVec::<EFPacking<EF>>::zeroed(prev_folded_size) })
        .collect();

    let n_lo = split_eq.n_lo();
    let packed_hi = split_eq.packed_hi();
    let log_packed_hi = split_eq.log_packed_hi;
    let eq_lo = &split_eq.eq_lo;
    let eq_hi = &split_eq.eq_hi_packed;

    let n_mult = multilinears.len();
    let sums: Vec<EFPacking<EF>> = parallel::map_reduce_with_state(
        n_lo,
        || {
            (
                Vec::<[EFPacking<EF>; 3]>::with_capacity(n_mult),
                Vec::<EFPacking<EF>>::with_capacity(n_mult),
                EFPacking::<EF>::zero_vec(degree),
            )
        },
        || EFPacking::<EF>::zero_vec(degree),
        |(rows_f, point, block_acc), acc, b_lo| {
            let eq_lo_bc = EFPacking::<EF>::from(eq_lo[b_lo]);
            let base = b_lo << log_packed_hi;
            block_acc.iter_mut().for_each(|x| *x = EFPacking::<EF>::ZERO);
            for k in 0..packed_hi {
                let i = base + k;
                let eq_val = eq_hi[k];

                rows_f.clear();
                rows_f.extend(multilinears.iter().enumerate().map(|(j, m)| {
                    let lo = fold_f(m, i);
                    let hi = fold_f(m, i + compute_fold_size);
                    unsafe {
                        let ptr = folded_f[j].as_ptr() as *mut EFPacking<EF>;
                        *ptr.add(i) = lo;
                        *ptr.add(i + compute_fold_size) = hi;
                    }
                    [lo, hi - lo, hi]
                }));

                // z = 0
                point.clear();
                point.extend(rows_f.iter().map(|r| r[0]));
                let mut e0 = eval_fn(computation, point, extra_data);
                e0 *= eq_val;
                block_acc[0] += e0;

                // z = 2, 3, ...
                for d in 1..degree {
                    for [_, diff, running] in rows_f.iter_mut() {
                        *running += *diff;
                    }
                    point.clear();
                    point.extend(rows_f.iter().map(|r| r[2]));
                    let mut ev = eval_fn(computation, point, extra_data);
                    ev *= eq_val;
                    block_acc[d] += ev;
                }
            }
            for (a, b) in acc.iter_mut().zip(block_acc.iter()) {
                *a += *b * eq_lo_bc;
            }
        },
        add_assign_vec,
    );

    let unpacked = sums.into_iter().map(&unpack_sum);
    (build_evals(unpacked, missing_mul_factor), wrap_f(folded_f))
}
