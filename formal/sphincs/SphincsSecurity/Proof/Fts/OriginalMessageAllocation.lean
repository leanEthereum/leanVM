import SphincsSecurity.Proof.Fts.OriginalCertificateBound
import SphincsSecurity.Proof.Reference.ReferenceQueryAllocation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (retainedGameRestComputation)
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] scheme treeRoot gameAfterSecrets expectedBoundaryMessageCalls
  canonicalGraphGameInputs canonicalEncodingInputs canonicalGraphInputs retainedGameRestComputation

private theorem romRun_sampling_bind {Source Result : Type} (source : ProbComp Source)
    (next : Source → OracleComp OracleWorld Result) (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((liftM source : OracleComp OracleWorld Source) >>= next)).run cache =
      source >>= fun value => (simulateQ romImpl (next value)).run cache := by
  rw [simulateQ_bind, StateT.run_bind,
    show simulateQ romImpl (liftM source : OracleComp OracleWorld Source) =
      simulateQ (unifFwdImpl HashSpec) source from QueryImpl.simulateQ_add_liftM_left _ _ source,
    unifFwdImpl.simulateQ_run, bind_map_left]

theorem expected_boundaryComputation_messageCalls {Result : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld Result) (cache : QueryCache HashSpec) :
    (∑' result, Pr[= result | (simulateQ romImpl (boundaryComputation parameter computation)).run' cache] *
      (result.2.messageCalls.length : ENNReal)) = expectedBoundaryMessageCalls parameter computation cache := by
  have h := congrArg (fun law : ProbComp (Result × SigningBoundaryTrace) =>
    ∑' result, Pr[= result | law] * (result.2.messageCalls.length : ENNReal))
    (boundaryRun_fst_eq_boundaryComputation parameter computation cache)
  rw [tsum_probOutput_map_mul] at h
  rw [expectedBoundaryMessageCalls]
  exact h.symm

theorem expectedBoundaryMessageCalls_retained_eq_gameRest (adversary : Adversary) (key : SecretKey)
    (publicKey : PublicKey) (cache : QueryCache HashSpec) :
    expectedBoundaryMessageCalls key.parameter
      (simulateQ (expandedAdversaryImpl key) (retainedGameRestComputation adversary publicKey)) cache =
      expectedBoundaryMessageCalls key.parameter (gameRest scheme adversary publicKey key) cache := by
  rw [expectedBoundaryMessageCalls_eq_queryCharge, expectedBoundaryMessageCalls_eq_queryCharge]
  have hretained : retainedGameRestComputation adversary publicKey =
      OtsProbeSimulation.retainedGameRestComputation adversary publicKey := by
    unfold OtsProbeSimulation.retainedGameRestComputation retainedGameRestComputation
    rfl
  rw [hretained, OtsProbeSimulation.expectedQueryCharge_retained_eq_gameRest]

theorem originalCertificateMessageCost_le_boundaryGameCore (adversary : Adversary) :
    originalCertificateMessageCost adversary ≤
      ∑' result, Pr[= result | (simulateQ romImpl (boundaryGameCore adversary)).run' ∅] *
        (result.2.messageCalls.length : ENNReal) := by
  rw [originalCertificateMessageCost, show scheme.keygen = keygen by rw [scheme]]
  conv_lhs => rw [keygen, romRun_sampling_bind, tsum_probOutput_bind_mul]
  conv_rhs => rw [boundaryGameCore, simulateQ_romImpl_liftM_bind_run', tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  conv_lhs => rw [romRun_sampling_bind, tsum_probOutput_bind_mul]
  conv_rhs => rw [simulateQ_romImpl_liftM_bind_run', tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro otsSecret
  apply mul_le_mul' le_rfl
  conv_lhs => rw [romRun_sampling_bind, tsum_probOutput_bind_mul]
  conv_rhs => rw [simulateQ_romImpl_liftM_bind_run', tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  apply mul_le_mul' le_rfl
  conv_lhs => rw [simulateQ_bind, StateT.run_bind, tsum_probOutput_bind_mul]
  simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul,
    expectedBoundaryMessageCalls_retained_eq_gameRest]
  rw [expected_boundaryComputation_messageCalls, gameAfterSecrets, expectedBoundaryMessageCalls_bind]
  exact le_add_self

theorem boundaryGameCore_messageCalls_eq_referenceRecorded (dummy : OtsReferenceWords) (adversary : Adversary) :
    (∑' result, Pr[= result | (simulateQ romImpl (boundaryGameCore adversary)).run' ∅] *
      (result.2.messageCalls.length : ENNReal)) =
      ∑' result, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.messageCalls : ENNReal) := by
  have h := evalDist_boundaryGameCore_referenceFamily (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary)
    dummy adversary (hashInputs_subset_canonicalGraphGameInputs adversary)
  have hp := (evalDist_ext_iff
    (mx := (simulateQ romImpl (boundaryGameCore adversary)).run' ∅)
    (mx' := Prod.snd <$> referenceFamilyGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)).mp h
  calc
    _ = ∑' result, Pr[= result | Prod.snd <$> referenceFamilyGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
          (result.2.messageCalls.length : ENNReal) := tsum_congr fun result => congrArg (· * _) (hp result)
    _ = _ := by
      rw [tsum_probOutput_map_mul,
        ← referenceRecordedGame_erased (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary, tsum_probOutput_map_mul]
      rfl

theorem originalCertificateMessageCost_le_referenceRecorded (dummy : OtsReferenceWords) (adversary : Adversary) :
    originalCertificateMessageCost adversary ≤
      ∑' result, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.messageCalls : ENNReal) :=
  (originalCertificateMessageCost_le_boundaryGameCore adversary).trans_eq
    (boundaryGameCore_messageCalls_eq_referenceRecorded dummy adversary)

end SphincsSecurity.Concrete
