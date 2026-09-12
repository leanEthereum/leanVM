import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Reference.BoundaryMessageCost
import SphincsSecurity.Proof.Fts.OriginalProposalExecution
import SphincsSecurity.Proof.Base.RomQueryChargeBind
import SphincsSecurity.Proof.Fts.UpperDigestSelection

/-! ## RomQueryChargeComparison -/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem expectedQueryCharge_lift_unif_eq_zero
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (computation : OracleComp unifSpec α) (cache : QueryCache HashSpec) :
    expectedQueryCharge charge (liftM computation : OracleComp OracleWorld α) cache = 0 := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind query next ih =>
      rw [liftM_bind]
      change expectedQueryCharge charge
        ((liftM (OracleWorld.query (.inl query)) : OracleComp OracleWorld _) >>= fun answer => liftM (next answer)) cache = 0
      rw [expectedQueryCharge_query_bind]
      simp only [hashQueryCharge, Sum.elim_inl, ih, mul_zero, tsum_zero, zero_add]

end SphincsSecurity

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageHashCharge)
attribute [local instance] Classical.propDecidable
noncomputable local instance instSampleableTypeRandomness_7 : SampleableType Randomness := SampleableType.ofFintype Randomness

attribute [local irreducible] signDigestLoop signAttempt signWithView signAfterDigest
set_option backward.isDefEq.respectTransparency false

theorem expectedQueryCharge_messageDigest_message (key : SecretKey) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec) :
    expectedQueryCharge (messageHashCharge key.parameter)
      (liftM (messageDigest key.parameter key.root message randomness : OracleComp HashSpec MessageDigest)) cache = 1 := by
  change expectedQueryCharge (messageHashCharge key.parameter)
    ((liftM (OracleWorld.query (.inr (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root message randomness)))) : OracleComp OracleWorld HashOutput) >>=
      fun answer => pure (truncateMessageDigest answer)) cache = 1
  rw [expectedQueryCharge_query_bind]
  simp only [expectedQueryCharge_pure, mul_zero, tsum_zero, add_zero, hashQueryCharge, Sum.elim_inr,
    messageHashCharge, if_pos (show FtsProbeSimulation.MessageHashInput key.parameter
      (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) from ⟨_, rfl⟩)]

theorem expectedQueryCharge_signAttempt_message (key : SecretKey) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec) :
    expectedQueryCharge (messageHashCharge key.parameter)
      (liftM (signAttempt key message randomness : OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))) cache = 1 := by
  rw [signAttempt, liftM_bind, expectedQueryCharge_bind, expectedQueryCharge_messageDigest_message]
  conv_lhs =>
    arg 2
    tactic =>
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      split_ifs <;> simp
  exact add_zero 1

theorem expectedQueryCharge_signDigestLoop_message (attempts : Nat) (key : SecretKey)
    (message : Message) (cache : QueryCache HashSpec) :
    expectedQueryCharge (messageHashCharge key.parameter) (signDigestLoop attempts key message) cache =
      digestAttemptExpectation attempts key message cache := by
  induction attempts generalizing cache with
  | zero => simp only [signDigestLoop, expectedQueryCharge_pure, digestAttemptExpectation]
  | succ attempts ih =>
      have hsample : (simulateQ romImpl (liftM sampleRandomness)).run cache =
          (fun randomness => (randomness, cache)) <$> sampleRandomness :=
        roSim.run_liftM (hashSpec := HashSpec)
          (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) sampleRandomness cache
      rw [signDigestLoop, expectedQueryCharge_bind, expectedQueryCharge_lift_unif_eq_zero, zero_add,
        hsample, sampleRandomness_eq, tsum_probOutput_map_mul, digestAttemptExpectation,
        signDigestAttemptPrefix, tsum_probOutput_bind_mul]
      simp_rw [expectedQueryCharge_bind, expectedQueryCharge_signAttempt_message,
        mul_add, ENNReal.tsum_add, mul_one, tsum_probOutput_of_liftM_PMF]
      congr 1
      apply tsum_congr
      intro randomness
      rw [simulateQ_romImpl_liftM]
      congr 1
      rw [tsum_probOutput_bind_mul]
      apply tsum_congr
      intro result
      simp only [tsum_probOutput_pure_mul]
      cases result.1 <;> simp [ih]

theorem freshDigestSelection_mass_le_messageCharge (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) :
    (Fintype.card FtsLeaf : ENNReal) * freshDigestSelectionProbability key message cache ≤
      expectedQueryCharge (messageHashCharge key.parameter) (signWithView key message) cache := by
  have h := probEvent_signDigestLoop_fresh_le_attempts_mul_admissibility digestAttemptLimit key message cache cache
    (onlyRejectedNewMessageEntries_self cache key message)
  have hscaled := mul_le_mul' (le_refl (Fintype.card FtsLeaf : ENNReal)) h
  have hscalar : (Fintype.card FtsLeaf : ENNReal) *
      (digestAttemptExpectation digestAttemptLimit key message cache * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹) =
      digestAttemptExpectation digestAttemptLimit key message cache := by
    have hcard : (Fintype.card FtsLeaf : ENNReal) = ((2 ^ ftsTreeHeight : Nat) : ENNReal) := by
      simp [FtsLeaf]
    rw [mul_left_comm, hcard,
      ENNReal.mul_inv_cancel (by norm_num [ftsTreeHeight]) (by finiteness), mul_one]
  rw [hscalar] at hscaled
  apply hscaled.trans
  rw [signWithView, expectedQueryCharge_bind, expectedQueryCharge_signDigestLoop_message]
  exact le_self_add

private theorem expected_pmfLift {α : Type} (computation : ProbComp α) (weight : α → ENNReal) :
    (∑' result, Pr[= result | (liftM computation : PMF α)] * weight result) =
      ∑' result, Pr[= result | computation] * weight result := rfl

theorem expected_originalProposalRecord_sign_messageCalls (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) :
    (∑' record, Pr[= record | originalProposalRecord key (.inr message) cache] *
      record.trace.messageCalls.length) =
      expectedQueryCharge (messageHashCharge key.parameter) (signWithView key message) cache := by
  rw [originalProposalRecord, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
  have h := congrArg (fun law : PMF (TracedSigningRecord SigningBoundaryTrace) =>
    ∑' result, Pr[= result | law] * (result.1.2.messageCalls.length : ENNReal))
    (completedSigningRecord_forget (signingBoundaryTrace key.parameter) key message cache)
  rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul, expected_pmfLift] at h
  change _ = expectedBoundaryMessageCalls key.parameter (signWithView key message) cache at h
  exact h.trans (expectedBoundaryMessageCalls_eq_queryCharge key.parameter (signWithView key message) cache)

end SphincsSecurity.Concrete
