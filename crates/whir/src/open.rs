// Credits: whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).

use ::utils::log2_strict_usize;
use fiat_shamir::{FSProver, MerklePath, ProofResult};
use field::PrimeCharacteristicRing;
use field::{ExtensionField, Field, PackedFieldExtension, TwoAdicField};
use sumcheck::{ProductComputation, run_product_sumcheck, run_product_sumcheck_from_round1, sumcheck_prove_many_rounds};
use tracing::{info_span, instrument};
use zk_alloc::{ArenaVec, arena_vec};

use crate::{config::WhirConfig, *};

impl<EF> WhirConfig<EF>
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: TwoAdicField,
{
    fn validate_parameters(&self) -> bool {
        self.num_variables == self.folding_factor.total_number(self.n_rounds()) + self.final_sumcheck_rounds
    }

    fn validate_statement(&self, statement: &[SparseStatement<EF>]) {
        statement.iter().for_each(|e| {
            assert_eq!(e.total_num_variables, self.num_variables);
            assert!(!e.values.is_empty());
            assert!(e.values.iter().all(|v| v.selector < 1 << e.selector_num_variables()));
        });
    }

    fn validate_witness(&self, witness: &Witness<EF>, polynomial: &MleRef<'_, EF>) -> bool {
        assert_eq!(witness.ood_points.len(), witness.ood_answers.len());
        polynomial.n_vars() == self.num_variables
    }

    #[instrument(name = "WHIR prove", skip_all)]
    pub fn prove(
        &self,
        prover_state: &mut impl FSProver<EF>,
        statement: Vec<SparseStatement<EF>>,
        witness: Witness<EF>,
        polynomial: &MleRef<'_, EF>,
    ) -> MultilinearPoint<EF> {
        assert!(self.validate_parameters());
        assert!(self.validate_witness(&witness, polynomial));
        self.validate_statement(&statement);

        let mut round_state =
            RoundState::initialize_first_round_state(self, prover_state, statement, witness, polynomial).unwrap();

        for round in 0..=self.n_rounds() {
            self.round(round, prover_state, &mut round_state).unwrap();
        }

        MultilinearPoint(round_state.randomness_vec)
    }

    fn round(
        &self,
        round_index: usize,
        prover_state: &mut impl FSProver<EF>,
        round_state: &mut RoundState<EF>,
    ) -> ProofResult<()> {
        let folded_evaluations = &round_state.sumcheck_prover.evals;
        let num_variables = self.num_variables - self.folding_factor.total_number(round_index);

        // Base case: final round reached
        if round_index == self.n_rounds() {
            return self.final_round(round_index, prover_state, round_state);
        }

        let round_params = &self.round_parameters[round_index];

        // Compute the folding factors for later use
        let folding_factor_next = self.folding_factor.at_round(round_index + 1);

        // Compute polynomial evaluations and build Merkle tree
        let domain_reduction = 1 << self.rs_reduction_factor(round_index);
        let new_domain_size = round_state.domain_size / domain_reduction;
        let inv_rate = new_domain_size >> num_variables;
        let folded_matrix = info_span!("FFT").in_scope(|| {
            reorder_and_dft(
                &folded_evaluations.by_ref(),
                folding_factor_next,
                log2_strict_usize(inv_rate),
                1 << folding_factor_next,
            )
        });

        let full = 1 << folding_factor_next;
        let (prover_data, root) = MerkleData::build(folded_matrix, full, full);

        prover_state.add_base_scalars(&root);

        // Handle OOD (Out-Of-Domain) samples
        let (ood_points, ood_answers) =
            sample_ood_points::<EF, _>(prover_state, round_params.ood_samples, num_variables, |point| {
                info_span!("ood evaluation").in_scope(|| folded_evaluations.evaluate(point))
            });

        prover_state.pow_grinding(round_params.query_pow_bits);

        let (ood_challenges, stir_challenges, stir_challenges_indexes) = self.compute_stir_queries(
            prover_state,
            round_state,
            num_variables,
            round_params,
            &ood_points,
            round_index,
        )?;

        let folding_randomness = round_state.folding_randomness(
            self.folding_factor.at_round(round_index) + round_state.commitment_merkle_prover_data_b.is_some() as usize,
        );

        let stir_evaluations = if let Some(data_b) = &round_state.commitment_merkle_prover_data_b {
            let answers_a =
                open_merkle_tree_at_challenges(&round_state.merkle_prover_data, prover_state, &stir_challenges_indexes);
            let answers_b = open_merkle_tree_at_challenges(data_b, prover_state, &stir_challenges_indexes);
            let mut stir_evaluations = Vec::new();
            for (answer_a, answer_b) in answers_a.iter().zip(&answers_b) {
                let vars_a = answer_a.by_ref().n_vars();
                let vars_b = answer_b.by_ref().n_vars();
                let a_trunc = folding_randomness[1..].to_vec();
                let eval_a = answer_a.evaluate(&MultilinearPoint(a_trunc));
                let b_trunc = folding_randomness[vars_a - vars_b + 1..].to_vec();
                let eval_b = answer_b.evaluate(&MultilinearPoint(b_trunc));
                let last_fold_rand_a = folding_randomness[0];
                let last_fold_rand_b = folding_randomness[..vars_a - vars_b + 1]
                    .iter()
                    .map(|&x| EF::ONE - x)
                    .product::<EF>();
                stir_evaluations.push(eval_a * last_fold_rand_a + eval_b * last_fold_rand_b);
            }

            stir_evaluations
        } else {
            open_merkle_tree_at_challenges(&round_state.merkle_prover_data, prover_state, &stir_challenges_indexes)
                .iter()
                .map(|answer| answer.evaluate(&folding_randomness))
                .collect()
        };

        // Randomness for combination
        prover_state.duplex();
        let combination_randomness_gen: EF = prover_state.sample();
        let ood_combination_randomness: Vec<_> = combination_randomness_gen.powers().collect_n(ood_challenges.len());
        round_state
            .sumcheck_prover
            .add_new_equality(&ood_challenges, &ood_answers, &ood_combination_randomness);
        let stir_combination_randomness = combination_randomness_gen
            .powers()
            .skip(ood_challenges.len())
            .take(stir_challenges.len())
            .collect::<Vec<_>>();

        round_state.sumcheck_prover.add_new_base_equality(
            &stir_challenges,
            &stir_evaluations,
            &stir_combination_randomness,
        );

        let next_folding_randomness = round_state.sumcheck_prover.run_sumcheck_many_rounds(
            None,
            prover_state,
            folding_factor_next,
            round_params.folding_pow_bits,
        );

        round_state.randomness_vec.extend_from_slice(&next_folding_randomness.0);

        // Update round state
        round_state.domain_size = new_domain_size;
        round_state.next_domain_gen =
            PF::<EF>::two_adic_generator(log2_strict_usize(new_domain_size) - folding_factor_next);
        round_state.merkle_prover_data = prover_data;
        round_state.commitment_merkle_prover_data_b = None;

        Ok(())
    }

    fn final_round(
        &self,
        round_index: usize,
        prover_state: &mut impl FSProver<EF>,
        round_state: &mut RoundState<EF>,
    ) -> ProofResult<()> {
        // Convert evaluations to coefficient form and send to the verifier.
        let mut coeffs = match &round_state.sumcheck_prover.evals {
            MleOwned::Extension(evals) => evals.clone(),
            MleOwned::ExtensionPacked(evals) => unpack_extension(evals),
            _ => unreachable!(),
        };
        evals_to_coeffs(&mut coeffs);
        prover_state.add_extension_scalars(&coeffs);

        prover_state.pow_grinding(self.final_query_pow_bits);

        // Final verifier queries and answers. The indices are over the folded domain.
        let final_challenge_indexes = get_challenge_stir_queries(
            // The size of the original domain before folding
            round_state.domain_size >> self.folding_factor.at_round(round_index),
            self.final_queries,
            prover_state,
        );

        let mut base_paths = Vec::new();
        let mut ext_paths = Vec::new();
        for challenge in final_challenge_indexes {
            let (answer, sibling_hashes) = round_state.merkle_prover_data.open(challenge);

            match answer {
                MleOwned::Base(leaf) => {
                    base_paths.push(MerklePath {
                        leaf_data: leaf.to_vec(),
                        sibling_hashes,
                        leaf_index: challenge,
                    });
                }
                MleOwned::Extension(leaf) => {
                    ext_paths.push(MerklePath {
                        leaf_data: leaf.to_vec(),
                        sibling_hashes,
                        leaf_index: challenge,
                    });
                }
                _ => unreachable!(),
            }
        }
        if !base_paths.is_empty() {
            prover_state.hint_merkle_paths_base(base_paths);
        }
        if !ext_paths.is_empty() {
            prover_state.hint_merkle_paths_extension(ext_paths);
        }

        // Run final sumcheck if required
        if self.final_sumcheck_rounds > 0 {
            let final_folding_randomness =
                round_state
                    .sumcheck_prover
                    .run_sumcheck_many_rounds(None, prover_state, self.final_sumcheck_rounds, 0);

            round_state.randomness_vec.extend(final_folding_randomness.0);
        }

        Ok(())
    }

    #[allow(clippy::type_complexity)]
    fn compute_stir_queries(
        &self,
        prover_state: &mut impl FSProver<EF>,
        round_state: &RoundState<EF>,
        num_variables: usize,
        round_params: &RoundConfig<EF>,
        ood_points: &[EF],
        round_index: usize,
    ) -> ProofResult<(Vec<MultilinearPoint<EF>>, Vec<MultilinearPoint<PF<EF>>>, Vec<usize>)> {
        let stir_challenges_indexes = get_challenge_stir_queries(
            round_state.domain_size >> self.folding_factor.at_round(round_index),
            round_params.num_queries,
            prover_state,
        );

        let domain_scaled_gen = round_state.next_domain_gen;
        let ood_challenges = ood_points
            .iter()
            .map(|univariate| MultilinearPoint::expand_from_univariate(*univariate, num_variables))
            .collect();
        let stir_challenges = stir_challenges_indexes
            .iter()
            .map(|i| MultilinearPoint::expand_from_univariate(domain_scaled_gen.exp_u64(*i as u64), num_variables))
            .collect();

        Ok((ood_challenges, stir_challenges, stir_challenges_indexes))
    }
}

fn open_merkle_tree_at_challenges<EF: ExtensionField<PF<EF>>>(
    merkle_tree: &MerkleData<EF>,
    prover_state: &mut impl FSProver<EF>,
    stir_challenges_indexes: &[usize],
) -> Vec<MleOwned<EF>> {
    let mut answers = Vec::new();
    let mut base_paths = Vec::new();
    let mut ext_paths = Vec::new();

    for &challenge in stir_challenges_indexes {
        let (answer, sibling_hashes) = merkle_tree.open(challenge);

        match &answer {
            MleOwned::Base(leaf) => {
                base_paths.push(MerklePath {
                    leaf_data: leaf.to_vec(),
                    sibling_hashes,
                    leaf_index: challenge,
                });
            }
            MleOwned::Extension(leaf) => {
                ext_paths.push(MerklePath {
                    leaf_data: leaf.to_vec(),
                    sibling_hashes,
                    leaf_index: challenge,
                });
            }
            _ => unreachable!(),
        }
        answers.push(answer);
    }

    if !base_paths.is_empty() {
        prover_state.hint_merkle_paths_base(base_paths);
    }
    if !ext_paths.is_empty() {
        prover_state.hint_merkle_paths_extension(ext_paths);
    }

    answers
}

#[derive(Debug, Clone)]
pub struct SumcheckSingle<EF: ExtensionField<PF<EF>>> {
    /// Evaluations of the polynomial `p(X)`.
    pub(crate) evals: MleOwned<EF>,
    /// Evaluations of the equality polynomial used for enforcing constraints.
    pub(crate) weights: MleOwned<EF>,
    /// Accumulated sum incorporating equality constraints.
    pub(crate) sum: EF,
}

impl<EF: Field> SumcheckSingle<EF>
where
    EF: ExtensionField<PF<EF>>,
{
    #[instrument(skip_all)]
    pub(crate) fn add_new_equality(
        &mut self,
        points: &[MultilinearPoint<EF>],
        evaluations: &[EF],
        combination_randomness: &[EF],
    ) {
        assert_eq!(combination_randomness.len(), points.len());
        assert_eq!(evaluations.len(), points.len());

        points
            .iter()
            .zip(combination_randomness.iter())
            .for_each(|(point, &rand)| {
                compute_eval_eq_packed::<_, true>(point, self.weights.as_extension_packed_mut().unwrap(), rand);
            });

        self.sum += combination_randomness
            .iter()
            .zip(evaluations.iter())
            .map(|(&rand, &eval)| rand * eval)
            .sum::<EF>();
    }

    #[instrument(skip_all)]
    pub(crate) fn add_new_base_equality(
        &mut self,
        points: &[MultilinearPoint<PF<EF>>],
        evaluations: &[EF],
        combination_randomness: &[EF],
    ) {
        assert_eq!(combination_randomness.len(), points.len());
        assert_eq!(evaluations.len(), points.len());

        compute_eval_eq_base_packed_batched::<PF<EF>, EF>(
            points,
            self.weights.as_extension_packed_mut().unwrap(),
            combination_randomness,
        );

        // Accumulate the weighted sum (cheap, done sequentially)
        self.sum += combination_randomness
            .iter()
            .zip(evaluations.iter())
            .map(|(&rand, &eval)| rand * eval)
            .sum::<EF>();
    }

    fn run_sumcheck_many_rounds(
        &mut self,
        prev_folding_scalar: Option<EF>,
        prover_state: &mut impl FSProver<EF>,
        n_rounds: usize,
        pow_bits: usize,
    ) -> MultilinearPoint<EF> {
        let (challenges, folds, new_sum) = sumcheck_prove_many_rounds(
            MleGroupRef::merge(&[&self.evals.by_ref(), &self.weights.by_ref()]),
            prev_folding_scalar,
            &ProductComputation {},
            &vec![],
            None,
            prover_state,
            self.sum,
            None,
            n_rounds,
            false,
            pow_bits,
        );

        self.sum = new_sum;
        [self.evals, self.weights] = folds.split().try_into().unwrap();

        challenges
    }

    #[instrument(skip_all)]
    pub(crate) fn run_initial_sumcheck_rounds(
        evals: &MleRef<'_, EF>,
        statement: &[SparseStatement<EF>],
        combination_randomness: EF,
        prover_state: &mut impl FSProver<EF>,
        folding_factor: usize,
        pow_bits: usize,
    ) -> (Self, MultilinearPoint<EF>) {
        assert_ne!(folding_factor, 0);

        // Lazy-once fused combine + round-0 (transcript bit-identical to the
        // legacy path below; see the module comment on `LazyCombineTerms`).
        if lazy_combine_enabled() && packing_log_width::<EF>() > 0 {
            let evals_packed = evals.pack();
            if let MleRef::BasePacked(ev) = evals_packed.by_ref() {
                let terms = info_span!("build_lazy_combine_terms")
                    .in_scope(|| build_lazy_combine_terms::<EF>(statement, combination_randomness));
                let (first_poly, weights_buf) = info_span!("combine_and_compute_first_round")
                    .in_scope(|| combine_and_compute_first_round(ev, &terms, terms.combined_sum));
                if std::env::var("WHIR_LAZY_SELFCHECK").is_ok_and(|v| v == "1") {
                    let (w_ref, sum_ref) = combine_statement::<EF>(statement, combination_randomness);
                    assert_eq!(terms.combined_sum, sum_ref, "selfcheck: combined_sum diverged");
                    let n_bad = (0..w_ref.len()).filter(|&j| weights_buf[j] != w_ref[j]).count();
                    assert_eq!(n_bad, 0, "selfcheck: {n_bad} weight mismatches of {}", w_ref.len());
                }
                prover_state.add_sumcheck_polynomial(&first_poly.coeffs, None);
                prover_state.pow_grinding(pow_bits);
                let r1: EF = prover_state.sample();
                let sum1 = first_poly.evaluate(r1);
                let weights = Mle::Owned(MleOwned::ExtensionPacked(weights_buf));
                let (challenges, new_sum, folded_evals, folded_weights) = run_product_sumcheck_from_round1(
                    &evals_packed.by_ref(),
                    &weights.by_ref(),
                    prover_state,
                    r1,
                    sum1,
                    folding_factor,
                    pow_bits,
                );
                let sumcheck = Self {
                    evals: folded_evals,
                    weights: folded_weights,
                    sum: new_sum,
                };
                return (sumcheck, challenges);
            }
        }

        let (weights, sum) = combine_statement::<EF>(statement, combination_randomness);

        let mut evals = evals.pack();
        let mut weights = Mle::Owned(MleOwned::ExtensionPacked(weights));
        let (challengess, new_sum, new_evals, new_weights) = run_product_sumcheck(
            &evals.by_ref(),
            &weights.by_ref(),
            prover_state,
            sum,
            folding_factor,
            pow_bits,
        );

        evals = new_evals.into();
        weights = new_weights.into();

        let sumcheck = Self {
            evals: evals.as_owned().unwrap(),
            weights: weights.as_owned().unwrap(),
            sum: new_sum,
        };

        (sumcheck, challengess)
    }
}

#[derive(Debug)]
pub(crate) struct RoundState<EF>
where
    EF: ExtensionField<PF<EF>>,
{
    domain_size: usize,
    next_domain_gen: PF<EF>,
    sumcheck_prover: SumcheckSingle<EF>,
    commitment_merkle_prover_data_b: Option<MerkleData<EF>>,
    merkle_prover_data: MerkleData<EF>,
    randomness_vec: Vec<EF>,
}

#[allow(clippy::mismatching_type_param_order)]
impl<EF> RoundState<EF>
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: TwoAdicField,
{
    pub(crate) fn initialize_first_round_state(
        prover: &WhirConfig<EF>,
        prover_state: &mut impl FSProver<EF>,
        mut statement: Vec<SparseStatement<EF>>,
        witness: Witness<EF>,
        polynomial: &MleRef<'_, EF>,
    ) -> ProofResult<Self> {
        let ood_statements = witness
            .ood_points
            .into_iter()
            .zip(witness.ood_answers)
            .map(|(point, evaluation)| {
                SparseStatement::dense(
                    MultilinearPoint::expand_from_univariate(point, prover.num_variables),
                    evaluation,
                )
            })
            .collect::<Vec<_>>();

        statement.splice(0..0, ood_statements);

        prover_state.duplex();
        let combination_randomness_gen: EF = prover_state.sample();

        let (sumcheck_prover, folding_randomness) = SumcheckSingle::run_initial_sumcheck_rounds(
            polynomial,
            &statement,
            combination_randomness_gen,
            prover_state,
            prover.folding_factor.at_round(0),
            prover.starting_folding_pow_bits,
        );

        Ok(Self {
            domain_size: prover.starting_domain_size(),
            next_domain_gen: PF::<EF>::two_adic_generator(
                log2_strict_usize(prover.starting_domain_size()) - prover.folding_factor.at_round(0),
            ),
            sumcheck_prover,
            merkle_prover_data: witness.prover_data,
            commitment_merkle_prover_data_b: None,
            randomness_vec: folding_randomness.0.clone(),
        })
    }

    fn folding_randomness(&self, folding_factor: usize) -> MultilinearPoint<EF> {
        MultilinearPoint(self.randomness_vec[self.randomness_vec.len() - folding_factor..].to_vec())
    }
}

#[instrument(skip_all, fields(num_constraints = statements.len(), n_vars = statements[0].total_num_variables))]
fn combine_statement<EF>(statements: &[SparseStatement<EF>], gamma: EF) -> (ArenaVec<EFPacking<EF>>, EF)
where
    EF: ExtensionField<PF<EF>>,
{
    let num_variables = statements[0].total_num_variables;
    assert!(statements.iter().all(|e| e.total_num_variables == num_variables));

    let out_len = 1 << (num_variables - packing_log_width::<EF>());

    let is_full = |s: &SparseStatement<EF>| {
        !s.is_next && s.values.len() == 1 && s.values[0].selector == 0 && s.inner_num_variables() == num_variables
    };

    let mut combined_weights: ArenaVec<EFPacking<EF>>;
    let mut combined_sum = EF::ZERO;
    let mut gamma_pow = EF::ONE;

    let start_idx = match statements {
        [a, b, ..] if is_full(a) && is_full(b) => {
            combined_weights = unsafe { ArenaVec::uninitialized(out_len) };
            let sa = gamma_pow;
            let sb = gamma_pow * gamma;
            combined_sum = a.values[0].value * sa + b.values[0].value * sb;
            gamma_pow = sb * gamma;
            compute_eval_eq_packed_dual::<EF>(&a.point.0, &b.point.0, &mut combined_weights, sa, sb);
            2
        }
        [a, ..] if is_full(a) => {
            combined_weights = unsafe { ArenaVec::uninitialized(out_len) };
            let sa = gamma_pow;
            combined_sum = a.values[0].value * sa;
            gamma_pow *= gamma;
            compute_eval_eq_packed::<EF, false>(&a.point.0, &mut combined_weights, sa);
            1
        }
        _ => {
            combined_weights = unsafe { ArenaVec::zeroed(out_len) };
            0
        }
    };

    for smt in &statements[start_idx..] {
        if !smt.is_next && (smt.values.len() == 1 || smt.inner_num_variables() < packing_log_width::<EF>()) {
            for evaluation in &smt.values {
                compute_sparse_eval_eq_packed::<EF>(evaluation.selector, &smt.point, &mut combined_weights, gamma_pow);
                combined_sum += evaluation.value * gamma_pow;
                gamma_pow *= gamma;
            }
        } else {
            let inner_poly: ArenaVec<EFPacking<EF>> = if smt.is_next {
                let next = matrix_next_mle_folded(&smt.point.0);
                pack_extension(&next)
            } else {
                eval_eq_packed(&smt.point)
            };
            let shift = smt.inner_num_variables() - packing_log_width::<EF>();
            let mut indexed_smt_values = smt.values.iter().enumerate().collect::<Vec<_>>();
            indexed_smt_values.sort_by_key(|(_, e)| e.selector);
            indexed_smt_values.dedup_by_key(|(_, e)| e.selector);
            assert_eq!(
                indexed_smt_values.len(),
                smt.values.len(),
                "Duplicate selectors in sparse statement"
            );
            let mut chunks_mut = split_at_mut_many(
                &mut combined_weights,
                &indexed_smt_values
                    .iter()
                    .map(|(_, e)| e.selector << shift)
                    .collect::<Vec<_>>(),
            );
            chunks_mut.remove(0);
            let mut next_gamma_powers = arena_vec![gamma_pow];
            for _ in 1..indexed_smt_values.len() {
                next_gamma_powers.push(*next_gamma_powers.last().unwrap() * gamma);
            }
            for (e, &scalar) in smt.values.iter().zip(&next_gamma_powers) {
                combined_sum += e.value * scalar;
            }
            let n = 1usize << shift;
            let mask = n - 1;
            let ptrs: ArenaVec<(parallel::SendPtr<EFPacking<EF>>, EF)> = chunks_mut
                .iter_mut()
                .zip(&indexed_smt_values)
                .map(|(out_buff, &(origin_index, _))| {
                    (
                        parallel::SendPtr(out_buff.as_mut_ptr()),
                        next_gamma_powers[origin_index],
                    )
                })
                .collect();
            let inner = inner_poly.as_slice();
            parallel::for_each_index(ptrs.len() << shift, |flat| {
                let (ptr, scalar) = &ptrs[flat >> shift];
                let i = flat & mask;
                unsafe { *ptr.add(i) += inner[i] * *scalar };
            });
            gamma_pow = *next_gamma_powers.last().unwrap() * gamma;
        }
    }
    (combined_weights, combined_sum)
}

// ---------------------------------------------------------------------------
// Lazy-once fused combine + round-0 for the WHIR initial sumcheck (pw13-mac h-wf).
//
// `combine_statement` materializes w = Σ_s γ^{k_s}·weight_s with one full-size
// eq-tensor pass plus read-modify-write scatters over every statement region,
// then round 0 re-reads the buffer. Here the weight value w[j] is instead
// evaluated in-register from small per-statement tables (prefix/suffix split
// for full statements, shared inner-eq tables for block statements), exactly
// once, inside the round-0 pass — which also stream-writes the materialized
// buffer for rounds 1+. The transcript is bit-identical: the gamma-power
// accounting replays `combine_statement` exactly, and every weight value is
// the same field element (exact-field reassociation only).
//
// Toggle: WHIR_LAZY_COMBINE=0 falls back to the legacy path (also used when
// packing width is 1 or the evals are not base-packed).
// ---------------------------------------------------------------------------

const LAZY_OVERLAY_SPAN_MAX: usize = 8; // packed words; small blocks are pre-expanded

struct LazyFullTerm<EF: ExtensionField<PF<EF>>> {
    left: ArenaVec<EF>,              // 2^A prefix table, statement scalar folded in
    right: ArenaVec<EFPacking<EF>>,  // 2^(n - A - w) packed suffix table
    rshift: usize,
    rmask: usize,
}

/// One (statement, value) pair: scalar·eq(point,·) (or next-mle) on the packed
/// range [start, start + 2^ishift). Aligned: start is a multiple of 2^ishift.
struct LazyBlock {
    start: usize,
    ishift: usize,
    inner_id: u32,
    scalar: usize, // index into `scalars`
}

pub(crate) struct LazyCombineTerms<EF: ExtensionField<PF<EF>>> {
    full: Vec<LazyFullTerm<EF>>,
    inners: Vec<ArenaVec<EFPacking<EF>>>,
    blocks: Vec<LazyBlock>,
    scalars: Vec<EF>,
    grid: Vec<Vec<u32>>, // packed-index >> grid_log -> covering block ids
    grid_log: usize,
    overlay: Vec<(usize, EFPacking<EF>)>, // sorted by packed index
    pub(crate) combined_sum: EF,
}

impl<EF: ExtensionField<PF<EF>>> LazyCombineTerms<EF> {
    #[inline(always)]
    fn value_at(&self, j: usize) -> EFPacking<EF> {
        let mut acc = EFPacking::<EF>::ZERO;
        for t in &self.full {
            acc += t.right[j & t.rmask] * t.left[j >> t.rshift];
        }
        if !self.grid.is_empty() {
            for &b in &self.grid[j >> self.grid_log] {
                let blk = &self.blocks[b as usize];
                // a block listed in this cell covers the whole cell
                acc += self.inners[blk.inner_id as usize][j - blk.start] * self.scalars[blk.scalar];
            }
        }
        acc
    }
}

fn lazy_combine_enabled() -> bool {
    std::env::var("WHIR_LAZY_COMBINE").map(|v| v != "0").unwrap_or(true)
}

/// Replays `combine_statement`'s exact gamma-power accounting into lazy term
/// tables. `combined_sum` is the identical field element.
pub(crate) fn build_lazy_combine_terms<EF>(statements: &[SparseStatement<EF>], gamma: EF) -> LazyCombineTerms<EF>
where
    EF: ExtensionField<PF<EF>>,
{
    let num_variables = statements[0].total_num_variables;
    assert!(statements.iter().all(|e| e.total_num_variables == num_variables));
    let w = packing_log_width::<EF>();

    let is_full = |s: &SparseStatement<EF>| {
        !s.is_next && s.values.len() == 1 && s.values[0].selector == 0 && s.inner_num_variables() == num_variables
    };

    let mut full = Vec::new();
    let mut inners: Vec<ArenaVec<EFPacking<EF>>> = Vec::new();
    let mut blocks: Vec<LazyBlock> = Vec::new();
    let mut scalars: Vec<EF> = Vec::new();
    let mut overlay_map: std::collections::BTreeMap<usize, EFPacking<EF>> = Default::default();
    let mut combined_sum = EF::ZERO;
    let mut gamma_pow = EF::ONE;

    let make_full = |point: &[EF], scalar: EF| {
        let a = num_variables / 2;
        let mut left: ArenaVec<EF> = eval_eq(&point[..a]);
        for v in left.iter_mut() {
            *v *= scalar;
        }
        let right: ArenaVec<EFPacking<EF>> = eval_eq_packed(&point[a..]);
        let rshift = num_variables - a - w;
        LazyFullTerm {
            left,
            right,
            rshift,
            rmask: (1usize << rshift) - 1,
        }
    };

    let start_idx = match statements {
        [a, b, ..] if is_full(a) && is_full(b) => {
            let sa = gamma_pow;
            let sb = gamma_pow * gamma;
            combined_sum = a.values[0].value * sa + b.values[0].value * sb;
            gamma_pow = sb * gamma;
            full.push(make_full(&a.point.0, sa));
            full.push(make_full(&b.point.0, sb));
            2
        }
        [a, ..] if is_full(a) => {
            let sa = gamma_pow;
            combined_sum = a.values[0].value * sa;
            gamma_pow *= gamma;
            full.push(make_full(&a.point.0, sa));
            1
        }
        _ => 0,
    };

    for smt in &statements[start_idx..] {
        if !smt.is_next && (smt.values.len() == 1 || smt.inner_num_variables() < w) {
            // combine_statement's sparse path: per-value gamma powers.
            let inner_vars = smt.inner_num_variables();
            let mut stmt_inner: Option<u32> = None;
            for ev in &smt.values {
                let scalar = gamma_pow;
                combined_sum += ev.value * scalar;
                gamma_pow *= gamma;
                if inner_vars < w {
                    // lane-level: contributes within a single packed word
                    let shift = w - inner_vars;
                    let word = ev.selector >> shift;
                    let mut unpacked = vec![EF::ZERO; 1usize << w];
                    compute_sparse_eval_eq::<EF>(ev.selector & ((1 << shift) - 1), &smt.point.0, &mut unpacked, scalar);
                    let delta: Vec<EFPacking<EF>> = pack_extension(&unpacked);
                    *overlay_map.entry(word).or_insert(EFPacking::<EF>::ZERO) += delta[0];
                } else {
                    let inner_id = *stmt_inner.get_or_insert_with(|| {
                        inners.push(eval_eq_packed(&smt.point));
                        (inners.len() - 1) as u32
                    });
                    let ishift = inner_vars - w;
                    scalars.push(scalar);
                    blocks.push(LazyBlock {
                        start: ev.selector << ishift,
                        ishift,
                        inner_id,
                        scalar: scalars.len() - 1,
                    });
                }
            }
        } else {
            // combine_statement's dense path: sorted-unique selectors,
            // per-ORIGINAL-order gamma powers.
            let mut sorted = smt.values.iter().map(|e| e.selector).collect::<Vec<_>>();
            sorted.sort_unstable();
            sorted.dedup();
            assert_eq!(sorted.len(), smt.values.len(), "Duplicate selectors in sparse statement");

            let inner: ArenaVec<EFPacking<EF>> = if smt.is_next {
                let next = matrix_next_mle_folded(&smt.point.0);
                pack_extension(&next)
            } else {
                eval_eq_packed(&smt.point)
            };
            inners.push(inner);
            let inner_id = (inners.len() - 1) as u32;
            let ishift = smt.inner_num_variables() - w;

            let mut p = gamma_pow;
            for ev in &smt.values {
                combined_sum += ev.value * p;
                scalars.push(p);
                blocks.push(LazyBlock {
                    start: ev.selector << ishift,
                    ishift,
                    inner_id,
                    scalar: scalars.len() - 1,
                });
                p *= gamma;
            }
            gamma_pow = p;
        }
    }

    // Small blocks become exact overlay words; the rest go on the grid.
    let mut grid_blocks: Vec<LazyBlock> = Vec::new();
    for blk in blocks {
        let span = 1usize << blk.ishift;
        if span <= LAZY_OVERLAY_SPAN_MAX {
            let inner = &inners[blk.inner_id as usize];
            let s = scalars[blk.scalar];
            for t in 0..span {
                *overlay_map.entry(blk.start + t).or_insert(EFPacking::<EF>::ZERO) += inner[t] * s;
            }
        } else {
            grid_blocks.push(blk);
        }
    }

    let (grid, grid_log) = if grid_blocks.is_empty() {
        (Vec::new(), 0)
    } else {
        let grid_log = grid_blocks.iter().map(|b| b.ishift).min().unwrap();
        let n_cells = 1usize << (num_variables - w - grid_log);
        let mut grid: Vec<Vec<u32>> = vec![Vec::new(); n_cells];
        for (id, blk) in grid_blocks.iter().enumerate() {
            let c0 = blk.start >> grid_log;
            let c1 = (blk.start + (1usize << blk.ishift)) >> grid_log;
            for cell in grid.iter_mut().take(c1).skip(c0) {
                cell.push(id as u32);
            }
        }
        (grid, grid_log)
    };

    LazyCombineTerms {
        full,
        inners,
        blocks: grid_blocks,
        scalars,
        grid,
        grid_log,
        overlay: overlay_map.into_iter().collect(),
        combined_sum,
    }
}

/// One parallel pass: evaluates every weight value exactly once, stream-writes
/// the materialized buffer for rounds 1+, and accumulates the round-0
/// quadratic coefficients ((c0, c2); c1 deduced from the claimed sum).
fn combine_and_compute_first_round<EF>(
    evals: &[PFPacking<EF>],
    terms: &LazyCombineTerms<EF>,
    sum: EF,
) -> (DensePolynomial<EF>, ArenaVec<EFPacking<EF>>)
where
    EF: ExtensionField<PF<EF>>,
    EFPacking<EF>: std::ops::Mul<PFPacking<EF>, Output = EFPacking<EF>>,
{
    let n = evals.len();
    let half = n / 2;
    let mut weights = unsafe { ArenaVec::<EFPacking<EF>>::uninitialized(n) };
    let wp = parallel::SendPtr(weights.as_mut_ptr());

    let (mut c0p, mut c2p) = parallel::map_reduce(
        half,
        || (EFPacking::<EF>::ZERO, EFPacking::<EF>::ZERO),
        |i| {
            let w0 = terms.value_at(i);
            let w1 = terms.value_at(half + i);
            unsafe {
                *wp.add(i) = w0;
                *wp.add(half + i) = w1;
            }
            let x0 = evals[i];
            let x1 = evals[half + i];
            (w0 * x0, (w1 - w0) * (x1 - x0))
        },
        |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
    );

    // Exact overlay application: patch the buffer and correct the accumulators.
    for &(idx, delta) in &terms.overlay {
        weights[idx] += delta;
        if idx < half {
            // d c0 = delta·e0 ; d c2 = -delta·(e1 - e0)
            c0p += delta * evals[idx];
            c2p += delta * (evals[idx] - evals[half + idx]);
        } else {
            // d c2 = delta·(e1 - e0)
            c2p += delta * (evals[idx] - evals[idx - half]);
        }
    }

    let c0 = EFPacking::<EF>::to_ext_iter([c0p]).sum::<EF>();
    let c2 = EFPacking::<EF>::to_ext_iter([c2p]).sum::<EF>();
    let c1 = sum - c0.double() - c2;
    (DensePolynomial::new(vec![c0, c1, c2]), weights)
}

// ---------------------------------------------------------------------------
// h-wf kill-ladder rung benches (pw13-mac iter-1, hypothesis "whir-lazy-fusion").
// Test-only; no production code change.
// T0a: lazy chunk-wise weight evaluation (never materializing the 1.34 GB
//      combined weight) vs the materialized combine_statement + round-0 +
//      round-1-fold baseline. Gates (plan_spec): lazy_r0/(combine+read) <= 1.3
//      PASS, 1.3-2.0 GRAY, > 2.0 KILL. Bit-identical round polys asserted.
// T0b: EFxEF vs basexEF packed product-sumcheck ratio -> pins MAX_SLICES for
//      the delayed-EF representation (BDT 2024/1046).
// ---------------------------------------------------------------------------
#[cfg(test)]
mod fusion_bench {
    use super::*;
    use crate::{SparseStatement, SparseValue};
    use field::{PackedFieldExtension, PackedValue, PrimeCharacteristicRing};
    use koala_bear::{KoalaBear, QuinticExtensionFieldKB};
    use rand::{RngExt, SeedableRng, rngs::StdRng};
    use std::hint::black_box;
    use std::time::Instant;
    use sumcheck::{compute_product_sumcheck_polynomial, fold_and_compute_product_sumcheck_polynomial};

    type F = KoalaBear;
    type EF = QuinticExtensionFieldKB;
    type FP = PFPacking<EF>;
    type EFP = EFPacking<EF>;

    fn w_log() -> usize {
        packing_log_width::<EF>()
    }

    #[inline(always)]
    fn unpack_sum(s: EFP) -> EF {
        <EFP as PackedFieldExtension<F, EF>>::to_ext_iter([s]).sum::<EF>()
    }

    fn decompose(e: EFP) -> Vec<EF> {
        <EFP as PackedFieldExtension<F, EF>>::to_ext_iter([e]).collect()
    }

    /// Full-eq term: scalar pre-multiplied into the prefix table.
    /// value(j) = right_packed[j & rmask] * left[j >> rshift]
    struct FullT {
        left: ArenaVec<EF>,       // 2^A entries, scaled
        right: ArenaVec<EFP>,     // 2^(n - A - w) packed entries
        rshift: usize,            // n - A - w
        rmask: usize,
    }

    /// Dense block term (eq or next inner poly replicated over consecutive
    /// selector blocks with per-block scalars).
    /// Covers packed range [start, start + n_blocks << ishift).
    struct DenseT {
        start: usize,             // packed units
        end: usize,
        ishift: usize,            // inner_vars - w
        imask: usize,
        inner: ArenaVec<EFP>,     // 2^ishift packed entries (unscaled)
        scalars: Vec<EF>,         // per block, gamma powers
    }

    struct LazyTerms {
        full: Vec<FullT>,
        dense: Vec<DenseT>,
    }

    impl LazyTerms {
        #[inline(always)]
        fn at(&self, j: usize) -> EFP {
            let mut acc = EFP::ZERO;
            for t in &self.full {
                acc += t.right[j & t.rmask] * t.left[j >> t.rshift];
            }
            for t in &self.dense {
                if j >= t.start && j < t.end {
                    let o = j - t.start;
                    acc += t.inner[o & t.imask] * t.scalars[o >> t.ishift];
                }
            }
            acc
        }
    }

    /// Statement set mirroring stacked_pcs_global_statements + 2 OOD at the
    /// 1550-sig shape (tiny lane-level statements omitted in both arms; their
    /// production cost is ~epsilon and T1's proof-equality test covers them).
    /// Layout (elements): memory+acc [0, 2^23); bytecode_acc [2^23, 2^23+2^20);
    /// exec 20 cols at sel 9 (inner 2^20); poseidon 110 cols at sel 116
    /// (inner 2^18); ext 29 cols at sel 1807 (inner 2^15).
    fn rnd_pt(rng: &mut StdRng, len: usize) -> MultilinearPoint<EF> {
        MultilinearPoint((0..len).map(|_| rng.random::<EF>()).collect::<Vec<EF>>())
    }

    fn rnd_vals(rng: &mut StdRng, first_sel: usize, n: usize) -> Vec<SparseValue<EF>> {
        (0..n).map(|c| SparseValue::new(first_sel + c, rng.random::<EF>())).collect()
    }

    fn build_statements(n_vars: usize, rng: &mut StdRng) -> Vec<SparseStatement<EF>> {
        let mut stmts: Vec<SparseStatement<EF>> = Vec::new();
        // 2 OOD full statements (dual fast path)
        for _ in 0..2 {
            let p = rnd_pt(rng, n_vars);
            stmts.push(SparseStatement::new(n_vars, p, rnd_vals(rng, 0, 1)));
        }
        // memory + memory_acc (selectors 0,1 at inner n-4)
        let p = rnd_pt(rng, n_vars - 4);
        stmts.push(SparseStatement::new(n_vars, p, rnd_vals(rng, 0, 2)));
        // bytecode_acc (single value, inner n-6, selector 8)
        let p = rnd_pt(rng, n_vars - 6);
        stmts.push(SparseStatement::new(n_vars, p, rnd_vals(rng, 8, 1)));
        // exec: 2 eq statements (20 cols, inner n-6, sel 9..29) + 1 next (3 shift cols)
        for _ in 0..2 {
            let p = rnd_pt(rng, n_vars - 6);
            stmts.push(SparseStatement::new(n_vars, p, rnd_vals(rng, 9, 20)));
        }
        {
            let p = rnd_pt(rng, n_vars - 6);
            let mut s = SparseStatement::new(n_vars, p, rnd_vals(rng, 9, 3));
            s.is_next = true;
            stmts.push(s);
        }
        // poseidon: 2 eq statements (110 cols, inner n-8, sel 116..226)
        for _ in 0..2 {
            let p = rnd_pt(rng, n_vars - 8);
            stmts.push(SparseStatement::new(n_vars, p, rnd_vals(rng, 116, 110)));
        }
        // extension: 2 eq statements (29 cols, inner n-11, sel 1807..1836)
        for _ in 0..2 {
            let p = rnd_pt(rng, n_vars - 11);
            stmts.push(SparseStatement::new(n_vars, p, rnd_vals(rng, 1807, 29)));
        }
        stmts
    }

    /// Replays combine_statement's exact gamma-power accounting into lazy terms.
    /// Returns (terms, combined_sum) — combined_sum must equal combine_statement's.
    fn build_lazy_terms(statements: &[SparseStatement<EF>], gamma: EF, n_vars: usize) -> (LazyTerms, EF) {
        let w = w_log();
        let is_full = |s: &SparseStatement<EF>| {
            !s.is_next && s.values.len() == 1 && s.values[0].selector == 0 && s.inner_num_variables() == n_vars
        };
        let mut full = Vec::new();
        let mut dense = Vec::new();
        let mut combined_sum = EF::ZERO;
        let mut gamma_pow = EF::ONE;

        let make_full = |point: &[EF], scalar: EF| {
            let a = n_vars / 2; // prefix length
            let mut left: ArenaVec<EF> = eval_eq(&point[..a]);
            for v in left.iter_mut() {
                *v *= scalar;
            }
            let right: ArenaVec<EFP> = eval_eq_packed(&point[a..]);
            FullT {
                left,
                right,
                rshift: n_vars - a - w,
                rmask: (1usize << (n_vars - a - w)) - 1,
            }
        };

        let start_idx = match statements {
            [a, b, ..] if is_full(a) && is_full(b) => {
                let sa = gamma_pow;
                let sb = gamma_pow * gamma;
                combined_sum = a.values[0].value * sa + b.values[0].value * sb;
                gamma_pow = sb * gamma;
                full.push(make_full(&a.point.0, sa));
                full.push(make_full(&b.point.0, sb));
                2
            }
            [a, ..] if is_full(a) => {
                let sa = gamma_pow;
                combined_sum = a.values[0].value * sa;
                gamma_pow *= gamma;
                full.push(make_full(&a.point.0, sa));
                1
            }
            _ => 0,
        };

        for smt in &statements[start_idx..] {
            assert!(
                smt.inner_num_variables() >= w,
                "bench statement set must not contain lane-level statements"
            );
            let inner: ArenaVec<EFP> = if smt.is_next {
                let next = matrix_next_mle_folded(&smt.point.0);
                pack_extension(&next)
            } else {
                eval_eq_packed(&smt.point)
            };
            let ishift = smt.inner_num_variables() - w;
            // consecutive selectors assumed (true for the bench set)
            let first_sel = smt.values[0].selector;
            let mut scalars = Vec::with_capacity(smt.values.len());
            let mut p = gamma_pow;
            for (k, e) in smt.values.iter().enumerate() {
                assert_eq!(e.selector, first_sel + k, "bench terms assume consecutive selectors");
                combined_sum += e.value * p;
                scalars.push(p);
                p *= gamma;
            }
            gamma_pow = p;
            dense.push(DenseT {
                start: first_sel << ishift,
                end: (first_sel + smt.values.len()) << ishift,
                ishift,
                imask: (1usize << ishift) - 1,
                inner,
                scalars,
            });
        }
        (LazyTerms { full, dense }, combined_sum)
    }

    /// Lazy round-0: same (c0,c2)+c1-from-sum skeleton as
    /// compute_product_sumcheck_polynomial, weights from `terms.at(j)`.
    fn lazy_round0(evals: &[FP], terms: &LazyTerms, sum: EF) -> DensePolynomial<EF> {
        let n = evals.len();
        let half = n / 2;
        let (c0p, c2p) = parallel::map_reduce(
            half,
            || (EFP::ZERO, EFP::ZERO),
            |i| {
                let y0 = terms.at(i);
                let y1 = terms.at(half + i);
                let x0 = evals[i];
                let x1 = evals[half + i];
                let constant = y0 * x0;
                let quadratic = (y1 - y0) * (x1 - x0);
                (constant, quadratic)
            },
            |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
        );
        let c0 = unpack_sum(c0p);
        let c2 = unpack_sum(c2p);
        let c1 = sum - c0.double() - c2;
        DensePolynomial::new(vec![c0, c1, c2])
    }

    /// Lazy round-1 fused fold: recompute weights, fold both polys with r1,
    /// materialize half-size folded arrays, emit round-1 coeffs — mirrors
    /// fold_and_compute_product_sumcheck_polynomial exactly.
    #[allow(clippy::type_complexity)]
    fn lazy_fold_round1(
        evals: &[FP],
        terms: &LazyTerms,
        r1: EF,
        sum: EF,
    ) -> (DensePolynomial<EF>, ArenaVec<EFP>, ArenaVec<EFP>) {
        let n = evals.len();
        let quarter = n / 4;
        let r1p = EFP::from(r1);
        let mut e_folded = unsafe { ArenaVec::<EFP>::uninitialized(n / 2) };
        let mut w_folded = unsafe { ArenaVec::<EFP>::uninitialized(n / 2) };
        let pe = parallel::SendPtr(e_folded.as_mut_ptr());
        let pw = parallel::SendPtr(w_folded.as_mut_ptr());
        let (c0p, c2p) = parallel::map_reduce(
            quarter,
            || (EFP::ZERO, EFP::ZERO),
            |i| {
                let x_0 = r1p * (evals[2 * quarter + i] - evals[i]) + evals[i];
                let x_1 = r1p * (evals[3 * quarter + i] - evals[quarter + i]) + evals[quarter + i];
                let w00 = terms.at(i);
                let w01 = terms.at(quarter + i);
                let w10 = terms.at(2 * quarter + i);
                let w11 = terms.at(3 * quarter + i);
                let y_0 = r1p * (w10 - w00) + w00;
                let y_1 = r1p * (w11 - w01) + w01;
                unsafe {
                    *pe.add(i) = x_0;
                    *pe.add(quarter + i) = x_1;
                    *pw.add(i) = y_0;
                    *pw.add(quarter + i) = y_1;
                }
                let constant = y_0 * x_0;
                let quadratic = (y_1 - y_0) * (x_1 - x_0);
                (constant, quadratic)
            },
            |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
        );
        let c0 = unpack_sum(c0p);
        let c2 = unpack_sum(c2p);
        let c1 = sum - c0.double() - c2;
        (DensePolynomial::new(vec![c0, c1, c2]), e_folded, w_folded)
    }

    fn cheap_base_fill(len: usize) -> ArenaVec<FP> {
        let mut v = unsafe { ArenaVec::<FP>::uninitialized(len) };
        let unpacked = FP::unpack_slice_mut(&mut v);
        parallel::par_chunks_mut(unpacked, 1 << 16, |chunk_idx, chunk| {
            let mut state = (chunk_idx as u64).wrapping_mul(0x9E3779B97F4A7C15) | 1;
            for slot in chunk {
                state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                *slot = F::from_u32((state >> 33) as u32 & 0x3FFFFFFF);
            }
        });
        v
    }

    fn median(mut xs: Vec<f64>) -> f64 {
        xs.sort_by(|a, b| a.partial_cmp(b).unwrap());
        xs[xs.len() / 2]
    }

    fn time_med<T>(reps: usize, mut f: impl FnMut() -> T) -> (f64, T) {
        let mut times = Vec::new();
        let mut out = None;
        for _ in 0..reps {
            let t = Instant::now();
            let r = f();
            times.push(t.elapsed().as_secs_f64());
            out = Some(r);
        }
        (median(times), out.unwrap())
    }

    #[test]
    #[ignore]
    fn t0a_lazy_vs_materialized() {
        let n_vars: usize = std::env::var("FUSION_BENCH_VARS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(26);
        let w = w_log();
        let mut rng = StdRng::seed_from_u64(42);
        let gamma: EF = rng.random();
        let stmts = build_statements(n_vars, &mut rng);
        println!("T0a: n_vars={n_vars}, packing_log_width={w}, {} statements", stmts.len());

        let evals = cheap_base_fill(1 << (n_vars - w));

        // --- materialized baseline ---
        let (t_combine, (weights, sum_m)) = time_med(3, || combine_statement::<EF>(&stmts, gamma));
        let (t_read, read_sink) = time_med(3, || {
            parallel::map_reduce(weights.len(), || EFP::ZERO, |i| weights[i], |a, b| a + b)
        });
        black_box(read_sink);
        let (t_r0, base_r0) = time_med(3, || {
            compute_product_sumcheck_polynomial(&evals, &weights, sum_m, decompose)
        });
        let r1: EF = rng.random();
        let sum_after_r0 = base_r0.evaluate(r1);
        let (t_r1, (base_r1, base_folded)) = time_med(3, || {
            fold_and_compute_product_sumcheck_polynomial(&evals, &weights, r1, sum_after_r0, decompose)
        });

        // --- lazy ---
        let (t_terms, (terms, sum_l)) = time_med(3, || build_lazy_terms(&stmts, gamma, n_vars));
        assert_eq!(sum_l, sum_m, "gamma-power accounting diverged");
        // spot-check weight values
        for _ in 0..4096 {
            let j = rng.random_range(0..weights.len());
            assert_eq!(terms.at(j), weights[j], "lazy weight mismatch at packed index {j}");
        }
        let (t_lazy_r0, lazy_r0_poly) = time_med(3, || lazy_round0(&evals, &terms, sum_l));
        assert_eq!(lazy_r0_poly.coeffs, base_r0.coeffs, "round-0 poly mismatch");
        let (t_lazy_r1, (lazy_r1_poly, lazy_e_folded, lazy_w_folded)) =
            time_med(3, || lazy_fold_round1(&evals, &terms, r1, sum_after_r0));
        assert_eq!(lazy_r1_poly.coeffs, base_r1.coeffs, "round-1 poly mismatch");
        // folded arrays equality (weights: lazy vs baseline fold output)
        let bw = &base_folded[1];
        let be = &base_folded[0];
        for _ in 0..4096 {
            let j = rng.random_range(0..lazy_w_folded.len());
            assert_eq!(lazy_w_folded[j], bw[j], "folded weight mismatch at {j}");
            assert_eq!(lazy_e_folded[j], be[j], "folded evals mismatch at {j}");
        }

        let base_total = t_combine + t_r0 + t_r1;
        let lazy_total = t_terms + t_lazy_r0 + t_lazy_r1;
        let ratio_spec = t_lazy_r0 / (t_combine + t_read);
        let ratio_e2e = lazy_total / base_total;
        println!("  baseline: combine {:.0}ms + read {:.0}ms + r0 {:.0}ms + r1fold {:.0}ms  (combine+r0+r1 = {:.0}ms)",
            t_combine * 1e3, t_read * 1e3, t_r0 * 1e3, t_r1 * 1e3, base_total * 1e3);
        println!("  lazy:     terms {:.0}ms + r0 {:.0}ms + r1fold {:.0}ms  (total {:.0}ms)",
            t_terms * 1e3, t_lazy_r0 * 1e3, t_lazy_r1 * 1e3, lazy_total * 1e3);
        let verdict = if ratio_spec <= 1.3 {
            "PASS"
        } else if ratio_spec <= 2.0 {
            "GRAY"
        } else {
            "KILL"
        };
        println!(
            "T0A: ratio_spec (lazy_r0 / (combine+read)) = {ratio_spec:.2} (gate: <=1.3 PASS / <=2.0 GRAY / >2.0 KILL) => {verdict}"
        );
        println!("T0A: ratio_e2e (lazy r0+r1+terms / combine+r0+r1) = {ratio_e2e:.2} (decision-relevant; <1.0 = net win)");
        assert!(ratio_spec <= 2.0, "T0a KILL: lazy round-0 {ratio_spec:.2}x the materialized combine+read");
    }

    #[test]
    #[ignore]
    fn t0b_ef_vs_base_ratio() {
        let mut rng = StdRng::seed_from_u64(7);
        let w = w_log();
        println!("T0b: packed EFxEF vs basexEF product-sumcheck cost");
        let mut last_ratio = 0.0;
        for log_n in [20usize, 22, 23] {
            let n = 1 << (log_n - w);
            let base = cheap_base_fill(n);
            let ext: ArenaVec<EFP> = {
                let vals: Vec<EF> = (0..(n << w)).map(|i| EF::from(F::from_u32((i as u32) | 1)) * EF::from_u32(7)).collect();
                pack_extension(&vals)
            };
            let wts: ArenaVec<EFP> = {
                let vals: Vec<EF> = (0..(n << w)).map(|_| rng.random::<EF>()).collect();
                pack_extension(&vals)
            };
            let sum: EF = rng.random();
            let (t_base, p1) = time_med(3, || {
                compute_product_sumcheck_polynomial(&base, &wts, sum, decompose)
            });
            let (t_ext, p2) = time_med(3, || {
                compute_product_sumcheck_polynomial(&ext, &wts, sum, decompose)
            });
            black_box((p1, p2));
            last_ratio = t_ext / t_base;
            println!("  2^{log_n}: basexEF {:.1}ms, EFxEF {:.1}ms, ratio {:.2}", t_base * 1e3, t_ext * 1e3, last_ratio);
        }
        let max_slices = if last_ratio >= 4.0 {
            4
        } else if last_ratio >= 2.0 {
            2
        } else {
            1
        };
        println!("T0B: EFxEF/basexEF = {last_ratio:.2} => MAX_SLICES = {max_slices} (delayed-EF profitable while n_slices < ratio)");
    }
}

#[cfg(test)]
mod lazy_combine_diag {
    use super::*;
    use crate::{SparseStatement, SparseValue};
    use field::{PackedValue, PrimeCharacteristicRing};
    use koala_bear::{KoalaBear, QuinticExtensionFieldKB};
    use rand::{RngExt, SeedableRng, rngs::StdRng};

    type F = KoalaBear;
    type EF = QuinticExtensionFieldKB;

    #[test]
    fn diag_lazy_vs_combine_failing_shape() {
        let num_variables = 20usize;
        let mut rng = StdRng::seed_from_u64(7);
        let polynomial = (0..1usize << num_variables).map(|_| rng.random::<F>()).collect::<Vec<F>>();

        let mut statement: Vec<SparseStatement<EF>> = Vec::new();
        // 2 fake OOD full statements at the front (mirrors initialize_first_round_state)
        for _ in 0..2 {
            let p = MultilinearPoint((0..num_variables).map(|_| rng.random::<EF>()).collect::<Vec<EF>>());
            statement.push(SparseStatement::new(num_variables, p, vec![SparseValue { selector: 0, value: rng.random::<EF>() }]));
        }
        for (selector_len, n_sels) in [(6usize, 5usize), (8, 9), (11, 3)] {
            let point = MultilinearPoint((0..num_variables - selector_len).map(|_| rng.random::<EF>()).collect::<Vec<EF>>());
            let first = rng.random_range(0..(1usize << selector_len) - n_sels);
            statement.push(SparseStatement::new(
                num_variables,
                point,
                (0..n_sels).map(|k| SparseValue { selector: first + k, value: rng.random::<EF>() }).collect(),
            ));
        }
        {
            let point = MultilinearPoint((0..num_variables - 5).map(|_| rng.random::<EF>()).collect::<Vec<EF>>());
            let sel = rng.random_range(0..32);
            statement.push(SparseStatement::new(num_variables, point, vec![SparseValue { selector: sel, value: rng.random::<EF>() }]));
        }
        for inner in [0usize, 1] {
            let point = MultilinearPoint((0..inner).map(|_| rng.random::<EF>()).collect::<Vec<EF>>());
            let sel = rng.random_range(0..(1usize << (num_variables - inner)));
            statement.push(SparseStatement::new(num_variables, point, vec![SparseValue { selector: sel, value: rng.random::<EF>() }]));
        }
        {
            let inner = 10usize;
            let point = MultilinearPoint((0..inner).map(|_| rng.random::<EF>()).collect::<Vec<EF>>());
            let mut s = SparseStatement::new(
                num_variables,
                point,
                (0..2usize).map(|k| SparseValue { selector: 3 + k, value: rng.random::<EF>() }).collect(),
            );
            s.is_next = true;
            statement.push(s);
        }

        let gamma: EF = rng.random();
        let (w_ref, sum_ref) = combine_statement::<EF>(&statement, gamma);
        let terms = build_lazy_combine_terms::<EF>(&statement, gamma);
        assert_eq!(terms.combined_sum, sum_ref, "combined_sum diverged");

        // elementwise weight check including overlay
        let half = w_ref.len() / 2;
        let evals: Vec<PFPacking<EF>> = {
            let mut v = vec![PFPacking::<EF>::ZERO; w_ref.len()];
            let unp = PFPacking::<EF>::unpack_slice_mut(&mut v);
            for (i, slot) in unp.iter_mut().enumerate() {
                *slot = F::from_u32((i as u32).wrapping_mul(2654435761) >> 3);
            }
            v
        };
        let (poly_lazy, w_lazy) = combine_and_compute_first_round::<EF>(&evals, &terms, sum_ref);
        let mut n_bad = 0usize;
        for j in 0..w_ref.len() {
            if w_lazy[j] != w_ref[j] {
                if n_bad < 10 {
                    println!("weight mismatch at packed {j} (half={half}, j>>13={})", j >> 13);
                }
                n_bad += 1;
            }
        }
        println!("total weight mismatches: {n_bad} / {}", w_ref.len());
        assert_eq!(n_bad, 0, "weights diverged");
        let poly_ref = sumcheck::compute_product_sumcheck_polynomial(&evals, &w_ref, sum_ref, |e| {
            <EFPacking<EF> as field::PackedFieldExtension<F, EF>>::to_ext_iter([e]).collect()
        });
        assert_eq!(poly_lazy.coeffs, poly_ref.coeffs, "round-0 poly diverged");
        println!("diag: all equal");
    }
}
