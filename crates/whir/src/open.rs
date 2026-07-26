// Credits: whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).

use ::utils::log2_strict_usize;
use fiat_shamir::{FSProver, MerklePath, ProofResult};
use field::PrimeCharacteristicRing;
use field::{Field, TwoAdicField};
use sumcheck::{
    ProductComputation, packing_unpack_sum, run_product_sumcheck_from_round1, run_product_sumcheck_from_round1_delayed,
    sumcheck_prove_many_rounds,
};
use tracing::{info_span, instrument};
use zk_alloc::ArenaVec;

use crate::{config::WhirConfig, *};

impl<EF> WhirConfig<EF>
where
    EF: KoalaBearExtension,
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

fn open_merkle_tree_at_challenges<EF: KoalaBearExtension>(
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
pub struct SumcheckSingle<EF: KoalaBearExtension> {
    /// Evaluations of the polynomial `p(X)`.
    pub(crate) evals: MleOwned<EF>,
    /// Evaluations of the equality polynomial used for enforcing constraints.
    pub(crate) weights: MleOwned<EF>,
    /// Accumulated sum incorporating equality constraints.
    pub(crate) sum: EF,
}

impl<EF: Field> SumcheckSingle<EF>
where
    EF: KoalaBearExtension,
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

        let evals = evals.pack();

        let MleRef::BasePacked(ev) = evals.by_ref() else {
            unreachable!("we always commit in the base field");
        };

        let terms = info_span!("build_lazy_combine_terms")
            .in_scope(|| build_lazy_combine_terms::<EF>(statement, combination_randomness));
        let (first_poly, weights_buf) =
            info_span!("combine_and_compute_first_round").in_scope(|| combine_and_compute_first_round(ev, &terms));
        prover_state.add_sumcheck_polynomial(&first_poly.coeffs, None);
        prover_state.pow_grinding(pow_bits);
        let r1: EF = prover_state.sample();
        let sum1 = first_poly.evaluate(r1);
        let (challenges, new_sum, folded_evals, folded_weights) = if folding_factor >= 4 {
            run_product_sumcheck_from_round1_delayed(ev, &weights_buf, prover_state, r1, sum1, folding_factor, pow_bits)
        } else {
            let weights = Mle::Owned(MleOwned::ExtensionPacked(weights_buf));
            run_product_sumcheck_from_round1(
                &evals.by_ref(),
                &weights.by_ref(),
                prover_state,
                r1,
                sum1,
                folding_factor,
                pow_bits,
            )
        };
        (
            Self {
                evals: folded_evals,
                weights: folded_weights,
                sum: new_sum,
            },
            challenges,
        )
    }
}

#[derive(Debug)]
pub(crate) struct RoundState<EF>
where
    EF: KoalaBearExtension,
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
    EF: KoalaBearExtension,
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

// Fused combine + round-0: evaluate each combined weight Σ_s γ^{k_s}·weight_s once, inside
// the round-0 pass, instead of materializing then.

const LAZY_OVERLAY_SPAN_MAX: usize = 8; // packed words; small blocks are pre-expanded

struct LazyFullTerm<EF: KoalaBearExtension> {
    left: ArenaVec<EF>,             // prefix eq-table, scalar folded in
    right: ArenaVec<EFPacking<EF>>, // packed suffix eq-table
    rshift: usize,                  // hi = j >> rshift, lo = j & ((1 << rshift) - 1)
}

/// scalar·eq(point,·) on the packed range [start, start + 2^ishift).
struct LazyBlock<EF: KoalaBearExtension> {
    start: usize,
    ishift: usize,
    inner_id: u32,
    scalar: EF,
}

pub(crate) struct LazyCombineTerms<EF: KoalaBearExtension> {
    full: Vec<LazyFullTerm<EF>>,
    inners: Vec<ArenaVec<EFPacking<EF>>>,
    grid_blocks: Vec<LazyBlock<EF>>,
    grid: Vec<Vec<u32>>, // packed-index >> grid_log -> covering block ids
    grid_log: usize,
    overlay: Vec<(usize, EFPacking<EF>)>, // sorted by packed index
    pub(crate) combined_sum: EF,
}

impl<EF: KoalaBearExtension> LazyCombineTerms<EF> {
    #[inline(always)]
    fn value_at(&self, j: usize) -> EFPacking<EF> {
        let mut acc = EFPacking::<EF>::ZERO;
        for t in &self.full {
            acc += t.right[j & ((1 << t.rshift) - 1)] * t.left[j >> t.rshift];
        }
        if !self.grid.is_empty() {
            for &b in &self.grid[j >> self.grid_log] {
                let blk = &self.grid_blocks[b as usize];
                // listed blocks cover the whole cell
                acc += self.inners[blk.inner_id as usize][j - blk.start] * blk.scalar;
            }
        }
        acc
    }
}

/// Builds the lazy term tables; `combined_sum` is the exact combined value.
pub(crate) fn build_lazy_combine_terms<EF>(statements: &[SparseStatement<EF>], gamma: EF) -> LazyCombineTerms<EF>
where
    EF: KoalaBearExtension,
{
    let num_variables = statements[0].total_num_variables;
    assert!(statements.iter().all(|e| e.total_num_variables == num_variables));
    let w = packing_log_width::<EF>();

    let is_full = |s: &SparseStatement<EF>| {
        !s.is_next && s.values.len() == 1 && s.values[0].selector == 0 && s.inner_num_variables() == num_variables
    };

    let mut full = Vec::new();
    let mut inners: Vec<ArenaVec<EFPacking<EF>>> = Vec::new();
    let mut blocks: Vec<LazyBlock<EF>> = Vec::new();
    let mut overlay_map: std::collections::BTreeMap<usize, EFPacking<EF>> = Default::default();
    let mut combined_sum = EF::ZERO;
    let mut gamma_pow = EF::ONE;

    let make_full = |point: &[EF], scalar: EF| {
        let a = num_variables / 2;
        let left: ArenaVec<EF> = eval_eq_scaled(&point[..a], scalar);
        let right: ArenaVec<EFPacking<EF>> = eval_eq_packed(&point[a..]);
        LazyFullTerm {
            left,
            right,
            rshift: num_variables - a - w,
        }
    };

    // Leading full statements (dense eq over all variables) use the sqrt-memory tensor split.
    let mut start_idx = 0;
    while start_idx < statements.len() && is_full(&statements[start_idx]) {
        let s = &statements[start_idx];
        combined_sum += s.values[0].value * gamma_pow;
        full.push(make_full(&s.point.0, gamma_pow));
        gamma_pow *= gamma;
        start_idx += 1;
    }

    // Remaining statements, in order; one gamma power per value either way.
    for smt in &statements[start_idx..] {
        let inner_vars = smt.inner_num_variables();
        if !smt.is_next && inner_vars < w {
            // Lane-level: each value lands within a single packed word, applied via the overlay.
            let shift = w - inner_vars;
            for ev in &smt.values {
                combined_sum += ev.value * gamma_pow;
                let mut unpacked = vec![EF::ZERO; 1usize << w];
                compute_sparse_eval_eq::<EF>(ev.selector & ((1 << shift) - 1), &smt.point.0, &mut unpacked, gamma_pow);
                let delta: Vec<EFPacking<EF>> = pack_extension(&unpacked);
                *overlay_map.entry(ev.selector >> shift).or_insert(EFPacking::<EF>::ZERO) += delta[0];
                gamma_pow *= gamma;
            }
        } else {
            // Block path: build the inner eq-table once, then one block per value.
            let mut sels = smt.values.iter().map(|e| e.selector).collect::<Vec<_>>();
            sels.sort_unstable();
            sels.dedup();
            assert_eq!(sels.len(), smt.values.len(), "Duplicate selectors in sparse statement");

            let inner: ArenaVec<EFPacking<EF>> = if smt.is_next {
                pack_extension(&matrix_next_mle_folded(&smt.point.0))
            } else {
                eval_eq_packed(&smt.point)
            };
            inners.push(inner);
            let inner_id = (inners.len() - 1) as u32;
            let ishift = inner_vars - w;
            for ev in &smt.values {
                combined_sum += ev.value * gamma_pow;
                blocks.push(LazyBlock {
                    start: ev.selector << ishift,
                    ishift,
                    inner_id,
                    scalar: gamma_pow,
                });
                gamma_pow *= gamma;
            }
        }
    }

    // small blocks → overlay, large → grid
    let mut grid_blocks: Vec<LazyBlock<EF>> = Vec::new();
    for blk in blocks {
        let span = 1usize << blk.ishift;
        if span <= LAZY_OVERLAY_SPAN_MAX {
            let inner = &inners[blk.inner_id as usize];
            let s = blk.scalar;
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
        grid_blocks,
        grid,
        grid_log,
        overlay: overlay_map.into_iter().collect(),
        combined_sum,
    }
}

// Active terms per side fit in a stack array; overflow drops to the `value_at` fallback
// (full terms — usually 1-2 — plus the grid blocks covering the cell).
const MAX_RUN_TERMS: usize = 12;

/// Gathers the terms active over a run starting at `base` (one fold side): each is a
/// (packed slice, scalar) contributing `slice[t] * scalar` to the weight at offset t.
/// Returns the term count, or None if more than `MAX_RUN_TERMS` cover the run.
#[inline]
fn gather_run_terms<'a, EF: KoalaBearExtension>(
    terms: &'a LazyCombineTerms<EF>,
    base: usize,
    run: usize,
    out: &mut [(&'a [EFPacking<EF>], EF); MAX_RUN_TERMS],
) -> Option<usize> {
    let mut n = 0;
    for t in &terms.full {
        if n == MAX_RUN_TERMS {
            return None;
        }
        let lo = base & ((1usize << t.rshift) - 1);
        out[n] = (&t.right[lo..lo + run], t.left[base >> t.rshift]);
        n += 1;
    }
    if !terms.grid.is_empty() {
        for &b in &terms.grid[base >> terms.grid_log] {
            if n == MAX_RUN_TERMS {
                return None;
            }
            let blk = &terms.grid_blocks[b as usize];
            let o = base - blk.start;
            out[n] = (&terms.inners[blk.inner_id as usize][o..o + run], blk.scalar);
            n += 1;
        }
    }
    Some(n)
}

/// One parallel pass: write the rounds-1+ weight buffer and accumulate the round-0 quadratic.
fn combine_and_compute_first_round<EF>(
    evals: &[PFPacking<EF>],
    terms: &LazyCombineTerms<EF>,
) -> (DensePolynomial<EF>, ArenaVec<EFPacking<EF>>)
where
    EF: KoalaBearExtension,
    EFPacking<EF>: std::ops::Mul<PFPacking<EF>, Output = EFPacking<EF>> + std::ops::Mul<EF, Output = EFPacking<EF>>,
{
    let n = evals.len();
    let half = n / 2;
    let mut weights = unsafe { ArenaVec::<EFPacking<EF>>::uninitialized(n) };
    let wp = parallel::SendPtr(weights.as_mut_ptr());

    // Run length keeps each term's context constant, so the inner loop can hoist it.
    let mut run_log = ::utils::log2_strict_usize(half.max(1));
    for t in &terms.full {
        run_log = run_log.min(t.rshift);
    }
    if !terms.grid.is_empty() {
        run_log = run_log.min(terms.grid_log);
    }
    let run = 1usize << run_log;
    let n_runs = half >> run_log;

    let (mut c0p, mut c2p) = parallel::map_reduce(
        n_runs,
        || (EFPacking::<EF>::ZERO, EFPacking::<EF>::ZERO),
        |run_idx| {
            let j0 = run_idx << run_log;
            let mut acc0 = EFPacking::<EF>::ZERO;
            let mut acc2 = EFPacking::<EF>::ZERO;

            let mut buf_lo: [(&[EFPacking<EF>], EF); MAX_RUN_TERMS] = [(&[], EF::ZERO); MAX_RUN_TERMS];
            let mut buf_hi: [(&[EFPacking<EF>], EF); MAX_RUN_TERMS] = [(&[], EF::ZERO); MAX_RUN_TERMS];
            let (Some(n_lo), Some(n_hi)) = (
                gather_run_terms(terms, j0, run, &mut buf_lo),
                gather_run_terms(terms, half + j0, run, &mut buf_hi),
            ) else {
                // rare fallback: evaluate each weight directly
                for t in 0..run {
                    let i = j0 + t;
                    let w0 = terms.value_at(i);
                    let w1 = terms.value_at(half + i);
                    unsafe {
                        *wp.add(i) = w0;
                        *wp.add(half + i) = w1;
                    }
                    acc0 += w0 * evals[i];
                    acc2 += (w1 - w0) * (evals[half + i] - evals[i]);
                }
                return (acc0, acc2);
            };
            let (terms_lo, terms_hi) = (&buf_lo[..n_lo], &buf_hi[..n_hi]);

            let e_lo = &evals[j0..j0 + run];
            let e_hi = &evals[half + j0..half + j0 + run];
            for t in 0..run {
                let mut w0 = EFPacking::<EF>::ZERO;
                for term in terms_lo {
                    w0 += term.0[t] * term.1;
                }
                let mut w1 = EFPacking::<EF>::ZERO;
                for term in terms_hi {
                    w1 += term.0[t] * term.1;
                }
                unsafe {
                    *wp.add(j0 + t) = w0;
                    *wp.add(half + j0 + t) = w1;
                }
                acc0 += w0 * e_lo[t];
                acc2 += (w1 - w0) * (e_hi[t] - e_lo[t]);
            }
            (acc0, acc2)
        },
        |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
    );

    // apply overlay: patch buffer, correct accumulators
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

    let c0 = packing_unpack_sum::<EF>(c0p);
    let c2 = packing_unpack_sum::<EF>(c2p);
    let c1 = terms.combined_sum - c0.double() - c2;
    (DensePolynomial::new(vec![c0, c1, c2]), weights)
}
