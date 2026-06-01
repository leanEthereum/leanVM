use backend::*;
use lean_prover::fiat_shamir_domain_sep;
use lean_vm::*;
use utils::get_poseidon16;

use crate::compilation::BYTECODE_CLAIM_OFFSET;
use crate::{InnerVerified, get_aggregation_bytecode};

pub(crate) struct ReducedBytecodeClaims {
    pub final_claim: Evaluation<EF>,
    pub sumcheck_transcript: Vec<F>,
}

impl ReducedBytecodeClaims {
    pub fn final_claim_flat(&self) -> Vec<F> {
        flatten_bytecode_claim(&self.final_claim)
    }
}

pub(crate) fn flatten_bytecode_claim(claim: &Evaluation<EF>) -> Vec<F> {
    let mut ef_claim: Vec<EF> = claim.point.0.clone();
    ef_claim.push(claim.value);
    flatten_scalars_to_base::<F, EF>(&ef_claim)
}

pub(crate) fn compute_bytecode_value_at(point: &MultilinearPoint<EF>) -> EF {
    let bytecode = get_aggregation_bytecode();
    if point.iter().all(|x| x.is_zero()) {
        // fast path for multi-signatures coming from 100% raw XMSS (no recursion):
        EF::from(bytecode.instructions_multilinear[0])
    } else {
        bytecode.instructions_multilinear.evaluate(point)
    }
}

pub(crate) fn reduce_bytecode_claims(verified: &[InnerVerified]) -> ReducedBytecodeClaims {
    let bytecode = get_aggregation_bytecode();

    if verified.is_empty() {
        let zero_point = MultilinearPoint(vec![EF::ZERO; bytecode.cumulated_n_vars()]);
        let zero_value = compute_bytecode_value_at(&zero_point);
        return ReducedBytecodeClaims {
            final_claim: Evaluation::new(zero_point, zero_value),
            sumcheck_transcript: vec![],
        };
    }

    let mut claims = Vec::with_capacity(2 * verified.len());
    for v in verified {
        claims.push(extract_bytecode_claim_from_input_data(
            &v.input_data[BYTECODE_CLAIM_OFFSET..],
            bytecode.cumulated_n_vars(),
        ));
        claims.push(v.bytecode_evaluation.clone());
    }
    let n_claims = claims.len();
    let claim_size_padded = bytecode.bytecode_claim_size().next_multiple_of(DIGEST_LEN);
    let bytecode_claims_fs_input = build_bytecode_claims_ingested_by_fiatshamir(&claims, claim_size_padded);

    let mut reduction_capacity = fiat_shamir_domain_sep(bytecode);
    reduction_capacity[0] += F::ONE; // Domain-separate this sub-protocol's Fiat-Shamir from the main snark
    let mut reduction_prover = ProverState::new(get_poseidon16().clone(), reduction_capacity);
    reduction_prover.observe_scalars(&bytecode_claims_fs_input);
    let alpha: EF = reduction_prover.sample();
    let alpha_powers: Vec<EF> = alpha.powers().take(n_claims).collect();

    let weights_packed = claims
        .par_iter()
        .zip(&alpha_powers)
        .map(|(eval, &alpha_i)| eval_eq_packed_scaled(&eval.point.0, alpha_i))
        .reduce_with(|mut acc, eq_i| {
            acc.par_iter_mut().zip(&eq_i).for_each(|(w, e)| *w += *e);
            acc
        })
        .unwrap();

    let claimed_sum: EF = dot_product(claims.iter().map(|c| c.value), alpha_powers.iter().copied());

    let (reduced_point, _, bytecode_folded, _) = run_product_sumcheck(
        &MleRef::BasePacked(FPacking::<F>::pack_slice(&bytecode.instructions_multilinear)),
        &MleRef::ExtensionPacked(&weights_packed),
        &mut reduction_prover,
        claimed_sum,
        bytecode.cumulated_n_vars(),
        0,
    );

    let reduced_value = bytecode_folded.as_constant();
    let bytecode_claim_output = flatten_bytecode_claim(&Evaluation::new(reduced_point.clone(), reduced_value));
    assert_eq!(bytecode_claim_output.len(), bytecode.bytecode_claim_size());

    let sumcheck_transcript = {
        let mut vs = VerifierState::<EF, _>::new(
            reduction_prover.into_proof(),
            get_poseidon16().clone(),
            reduction_capacity,
        )
        .unwrap();
        vs.observe_scalars(&bytecode_claims_fs_input);
        let _: EF = vs.sample();
        sumcheck_verify(&mut vs, bytecode.cumulated_n_vars(), 2, claimed_sum, None).unwrap();
        vs.into_raw_proof().transcript
    };
    assert_eq!(
        sumcheck_transcript.len(),
        bytecode_reduction_sumcheck_proof_size(bytecode.cumulated_n_vars()),
        "bytecode claim-reduction sumcheck transcript length disagrees with the formula",
    );

    ReducedBytecodeClaims {
        final_claim: Evaluation::new(reduced_point, reduced_value),
        sumcheck_transcript,
    }
}

pub(crate) fn extract_bytecode_claim_from_input_data(
    public_input: &[F],
    bytecode_point_n_vars: usize,
) -> Evaluation<EF> {
    let claim_size = (bytecode_point_n_vars + 1) * DIMENSION;
    let packed = pack_scalars_to_extension(&public_input[..claim_size]);
    let point = MultilinearPoint(packed[..bytecode_point_n_vars].to_vec());
    let value = packed[bytecode_point_n_vars];
    Evaluation::new(point, value)
}

fn build_bytecode_claims_ingested_by_fiatshamir(claims: &[Evaluation<EF>], claim_size_padded: usize) -> Vec<F> {
    let mut buf = Vec::with_capacity(DIGEST_LEN + claims.len() * claim_size_padded);
    buf.push(F::from_usize(claims.len()));
    buf.resize(DIGEST_LEN, F::ZERO);
    for eval in claims {
        let start = buf.len();
        buf.extend(flatten_bytecode_claim(eval));
        buf.resize(start + claim_size_padded, F::ZERO);
    }
    buf
}

pub(crate) fn bytecode_reduction_sumcheck_proof_size(bytecode_point_n_vars: usize) -> usize {
    let per_round = (3 * DIMENSION).next_multiple_of(DIGEST_LEN);
    bytecode_point_n_vars * per_round
}
